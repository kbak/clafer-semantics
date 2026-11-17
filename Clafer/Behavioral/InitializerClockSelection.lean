module

public import Clafer.Behavioral.AbstractMultiplicity
public import Clafer.Behavioral.InitializerCompatibility
public import Clafer.Behavioral.InitializerLowering

/-! # Explicit initializer clocks over aggregate abstract multiplicity

Behavioral §5 Definitions 3–5 / §6.1 supply the lifecycle setting. Independent
clock selection is the #194 language extension, composed with #193's aggregate
profile. It does not change the historical shorthand or static importer.
-/

@[expose] public section
namespace Clafer.Behavioral.Initializers.ClockSelection
universe u
open Classification

-- [impl->req~initializer-clock-selection~1]
/-- Both authored clock and authored bounds come from resolved source input.
The original declaration supplies abstractness, group and parent context;
optimizer bounds and actual realization parents do not classify its clock. -/
def elaborate {k : Nat} {V : Type} (m : AbstractMultiplicity.Core k) (d : Fin k)
    (form : Form) (scalar : Bool) (rhs : V) (choice : Option Selection := none) :
    Except Diagnostic (Obligation (Fin k) V) :=
  Structure.elaborate m.source d form (m.authoredMultiplicity d) scalar rhs choice

-- [proof->req~initializer-clock-selection~1]
theorem instance_elaboration {C V : Type} (d : C) (metadata : Classification.Declaration)
    (scalar : Bool) (rhs : V)
    (ranges : ∀ r, metadata.authored = some r → ValidRange r)
    (admission : metadata.abstract = true → scalar = true) :
    Initializers.elaborate d .initial metadata scalar rhs (some .instance) =
      .ok ⟨d, if metadata.parented then .parent else .root, .instanceBirth, rhs⟩ := by
  have admissible : (metadata.abstract && !scalar) = false := by
    cases h : metadata.abstract
    · simp
    · simp [admission h]
  simp only [Initializers.elaborate, explicit_classification _ _ _ ranges,
    Selection.resolve, decide_true, Bool.and_true, admissible, Bool.false_eq_true,
    ↓reduceIte, Except.map]

theorem collection_elaboration {C V : Type} (d : C) (metadata : Classification.Declaration)
    (scalar : Bool) (rhs : V)
    (ranges : ∀ r, metadata.authored = some r → ValidRange r) :
    Initializers.elaborate d .initial metadata scalar rhs (some .collection) =
      .ok ⟨d, if metadata.parented then .parent else .root,
        if metadata.parented then .parentBirth else .globalZero, rhs⟩ := by
  simp only [Initializers.elaborate, explicit_collection _ _ ranges]
  cases metadata.parented <;> simp [Except.map]

/-- The `=` API ignores the clock selection: explicit clocks belong to `:=`.
A frontend may reject an inapplicable keyword; it must not change equality. -/
theorem constant_unchanged {C V : Type} (d : C) (metadata : Classification.Declaration)
    (scalar : Bool) (rhs : V) (choice : Option Selection) :
    Initializers.elaborate d .constant metadata scalar rhs choice =
      Initializers.elaborate d .constant metadata scalar rhs := rfl

-- [impl->req~initializer-clock-selection~1]
-- [impl->req~behavioral-structural-compatibility~1]
/-- Initializer satisfaction in the selected aggregate profile. Every obligation
uses its complete original declaration view and coherent inherited reference.
Own and inherited entries are conjoined; aggregate counts remain independent.
Modifiers and other constraints can be conjoined separately. -/
def Satisfies {k : Nat} {V : Type} {U : Type u} (m : AbstractMultiplicity.Core k)
    (τ : Trace (Fin k) U) (source : V → Transport.Value U (Set U) 0)
    (obligations : List (Obligation (Fin k) V)) : Prop :=
  ∃ valid : AbstractMultiplicity.Admissible m τ, ∀ o ∈ obligations,
    ∃ r, ∃ owner : InheritedReference.Owner m.source.family o.declaration r,
      Meaning τ (Structure.view m.source τ valid.2.1 owner) source o

def CoreSatisfies {k : Nat} {V : Type} {U : Type u} (m : AbstractMultiplicity.Core k)
    (τ : Trace (Fin k) U) (source : V → Transport.Value U (Set U) 0)
    (obligations : List (Obligation (Fin k) V)) : Prop :=
  ∃ valid : AbstractMultiplicity.Admissible m τ, ∀ o ∈ obligations,
    ∃ r, ∃ owner : InheritedReference.Owner m.source.family o.declaration r,
      let v := Structure.view m.source τ valid.2.1 owner
      ∀ t x, x ∈ attachments τ v o t → x ∈ τ.live t →
        (lowerCore o).eval τ (observation τ v source).checked (.closed x) t

-- [proof->req~initializer-clock-selection~1]
-- [proof->req~behavioral-past-formulas~1]
-- [proof->req~behavioral-environments~1]
/-- Production lowering preserves all chosen/inherited clocks, original RHS
frames, independent counts and the inactive guard, with no RHS totality premise. -/
theorem core_agrees {k : Nat} {V : Type} {U : Type u} (m : AbstractMultiplicity.Core k)
    (τ : Trace (Fin k) U) (source : V → Transport.Value U (Set U) 0)
    (obligations : List (Obligation (Fin k) V)) :
    CoreSatisfies m τ source obligations ↔ Satisfies m τ source obligations := by
  unfold CoreSatisfies Satisfies
  apply exists_congr
  intro valid
  apply forall_congr'
  intro o
  apply imp_congr_right
  intro _
  apply exists_congr
  intro r
  apply exists_congr
  intro owner
  exact lowerCore_agrees τ (Structure.view m.source τ valid.2.1 owner) source o
    valid.2.1.root_live

-- [proof->req~initializer-clock-selection~1]
theorem counts_required {k : Nat} {V : Type} {U : Type u} (m : AbstractMultiplicity.Core k)
    (τ : Trace (Fin k) U) (source : V → Transport.Value U (Set U) 0)
    (obligations : List (Obligation (Fin k) V))
    (h : Satisfies m τ source obligations) : AbstractMultiplicity.Always m τ := by
  obtain ⟨valid, _⟩ := h
  exact valid.2.2

end Clafer.Behavioral.Initializers.ClockSelection
