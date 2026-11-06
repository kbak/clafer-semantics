module

public import Clafer.Behavioral.PartialCompatibility
public import Clafer.Behavioral.Modifiers

/-! # Models, assertions and scenarios

Behavioral paper §§4.5/6.1, corrected by T5–T6 and T9.
Assertions quantify over all model traces. Scenarios ask for one trace satisfying
additional constraints. Assertion failure is classical negation of the entire
interpreted property, including its strict definedness, never source `!`.
-/

@[expose] public section
namespace Clafer.Behavioral.Properties
universe u
variable {A D : Nat → Type} {C : Type} {U : Type u}

-- [impl->req~behavioral-properties~1]
/-- Resolved attachment selectors include top-level root and nested declaration
views. Applying a selector never changes the retained instance during evaluation. -/
structure Constraint (C : Type) (A D : Nat → Type) (U : Type u) where
  contexts : Trace C U → Nat → Set U
  body : Formula A D 0

def Constraint.Holds (c : Constraint C A D U) (τ : Trace C U)
    (O : PartialObservation A D U) : Prop := c.body.PartialAttached τ O (c.contexts τ)

def Constraint.root (body : Formula A D 0) : Constraint C A D U :=
  ⟨fun τ _ => {τ.identities.root}, body⟩

def Constraint.nested {k : Nat} (m : Structural.Core k) (d : Fin k)
    (body : Formula A D 0) : Constraint (Fin k) A D U :=
  ⟨fun τ t => (τ.raw m.toEffectiveCore t).head d, body⟩

/-- `admissible` supplies independently established structural/modifier meaning.
It is not a preservation assumption or a finite enumeration of candidate traces. -/
structure Model (C : Type) (A D : Nat → Type) (U : Type u) where
  admissible : Set (Trace C U)
  observations : Trace C U → PartialObservation A D U
  constraints : Set (Constraint C A D U)

def Model.structural {k : Nat} (m : Structural.Core k)
    (O : Trace (Fin k) U → PartialObservation A D U)
    (constraints : Set (Constraint (Fin k) A D U)) : Model (Fin k) A D U :=
  ⟨fun τ => m.WellFormed ∧ Structural.Valid m τ, O, constraints⟩

/-- Full source admission adds the independently defined effective modifiers;
surface transitions/patterns enter through their proved constraint expansions. -/
def Model.behavioral {k : Nat} (m : Structural.Core k)
    (modifiers : Fin k → Set Modifiers.Modifier)
    (O : Trace (Fin k) U → PartialObservation A D U)
    (constraints : Set (Constraint (Fin k) A D U)) : Model (Fin k) A D U :=
  ⟨fun τ => m.WellFormed ∧ Structural.Valid m τ ∧ Modifiers.Holds m τ modifiers, O, constraints⟩

def Model.Satisfies (m : Model C A D U) (τ : Trace C U) : Prop :=
  τ ∈ m.admissible ∧ ∀ c ∈ m.constraints, c.Holds τ (m.observations τ)

def Model.Asserts (m : Model C A D U) (a : Constraint C A D U) : Prop :=
  ∀ τ, m.Satisfies τ → a.Holds τ (m.observations τ)

def Model.Counterexample (m : Model C A D U) (a : Constraint C A D U) (τ : Trace C U) : Prop :=
  m.Satisfies τ ∧ ¬ a.Holds τ (m.observations τ)

def Model.Possible (m : Model C A D U) (scenario : Set (Constraint C A D U)) : Prop :=
  ∃ τ, m.Satisfies τ ∧ ∀ c ∈ scenario, c.Holds τ (m.observations τ)

/-- Scenario extension enforces the original model as well as every scenario
constraint. It does not promote existential feasibility to an assertion. -/
def Model.withScenario (m : Model C A D U) (scenario : Set (Constraint C A D U)) : Model C A D U :=
  { m with constraints := m.constraints ∪ scenario }

-- [proof->req~behavioral-properties~1]
theorem Model.counterexample_iff (m : Model C A D U) (a : Constraint C A D U) :
    (∃ τ, m.Counterexample a τ) ↔ ¬ m.Asserts a := by
  classical
  simp [Model.Counterexample, Model.Asserts, not_forall, not_imp]

theorem Model.possible_iff (m : Model C A D U) (scenario : Set (Constraint C A D U)) :
    m.Possible scenario ↔ ∃ τ, (m.withScenario scenario).Satisfies τ := by
  simp only [Model.Possible, Model.Satisfies, Model.withScenario, Set.mem_union]
  constructor
  · rintro ⟨τ, ⟨ha, hm⟩, hs⟩
    exact ⟨τ, ha, fun c hc => hc.elim (hm c) (hs c)⟩
  · rintro ⟨τ, ha, h⟩
    exact ⟨τ, ⟨ha, fun c hc => h c (Or.inl hc)⟩, fun c hc => h c (Or.inr hc)⟩

theorem Constraint.root_holds (a : Formula A D 0) (τ : Trace C U)
    (O : PartialObservation A D U) (live : ∀ t, τ.identities.root ∈ τ.live t) :
    (Constraint.root a).Holds τ O ↔
      ∀ t, a.Satisfies τ O true (.closed τ.identities.root) t := by
  simp only [Constraint.Holds, Constraint.root, Formula.PartialAttached, Set.mem_singleton_iff]
  exact ⟨fun h t => h t _ rfl (live t), fun h t c hc _ => hc ▸ h t⟩

/-- A nested assertion covers every applicable instance, not one chosen witness. -/
theorem Constraint.nested_holds {k : Nat} (m : Structural.Core k) (d : Fin k)
    (a : Formula A D 0) (τ : Trace (Fin k) U) (O : PartialObservation A D U) :
    (Constraint.nested m d a).Holds τ O ↔
      ∀ t c, c ∈ (τ.raw m.toEffectiveCore t).head d → a.Satisfies τ O true (.closed c) t := by
  constructor
  · intro h t c hc; exact h t c hc hc.1
  · intro h t c hc _; exact h t c hc

/-- Downstream lowering keeps the source domain and lowers positive source truth;
counterexample search negates this whole judgment at the meta level. -/
theorem Constraint.lowered (c : Constraint C A D U) (τ : Trace C U)
    (O : PartialObservation A D U) :
    c.Holds τ O ↔ ∀ t x, x ∈ c.contexts τ t → x ∈ τ.live t →
      c.body.Defined τ O (.closed x) t ∧
      (c.body.normalize true).lower.eval τ O.canonical (.closed x) t := by
  simp only [Constraint.Holds, Formula.PartialAttached, Formula.satisfies_iff_lowered]

end Clafer.Behavioral.Properties
