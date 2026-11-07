module

public import Clafer.Behavioral.Composition
public import Clafer.Behavioral.FinitePartial
public import Clafer.Behavioral.Transitions
public import Clafer.Behavioral.Patterns

/-! # Surface constraints and full finite model composition

Finite inventories must enumerate the exact source constraints and effective
modifier expansions. Agreement covers contexts as well as observations. The
full-model theorem applies to any independently admitted richer structural trace;
the common-fragment corollary checks structural admission with the existing S6
checker. Neither result establishes completeness over traces not supplied.
-/

@[expose] public section
namespace Clafer.Behavioral
namespace Properties
variable {A D : Nat → Type} {C : Type} {size last count : Nat}

-- [impl->req~behavioral-qualification~1]
def finitePlacement {k : Nat} (m : Structural.Core k) (L : Lasso (Fin k) size last)
    (placement : Modifiers.Placement (Fin k)) (s : Lasso.Clock last) : Finset (Fin size) :=
  Finset.univ.filter (fun x => (match placement with
    | .all => true
    | .heads d => (L.candidate m.toEffectiveCore s.1).head d x
    | .parents d => decide (∃ c, m.family.parent d = some c ∧
        (L.candidate m.toEffectiveCore s.1).head c x = true) : Bool) = true)

theorem finitePlacement_agrees {k : Nat} (m : Structural.Core k) (L : Lasso (Fin k) size last)
    (placement : Modifiers.Placement (Fin k)) (t : Nat) :
    (↑(finitePlacement m L placement (L.clock t)) : Set (Fin size)) =
      placement.contexts m L.unfold t := by
  ext x
  cases placement <;> simp [finitePlacement, Modifiers.Placement.contexts, Modifiers.parents,
    Lasso.candidate, Trace.raw, Lasso.unfold]

-- [impl->req~behavioral-qualification~1]
structure Constraint.Finite (c : Constraint C A D (Fin size)) (L : Lasso C size last) where
  program : c.body.Program true
  contexts : Lasso.Clock last → Finset (Fin size)
  contexts_agree : ∀ t, (↑(contexts (L.clock t)) : Set (Fin size)) = c.contexts L.unfold t

def Constraint.finiteRoot (L : Lasso C size last) (a : Formula A D 0) (p : a.Program true) :
    (Constraint.root a).Finite L :=
  ⟨p, fun _ => {L.identities.root}, fun _ => Finset.coe_singleton _⟩

def Constraint.finiteNested {k : Nat} (m : Structural.Core k) (L : Lasso (Fin k) size last)
    (d : Fin k) (a : Formula A D 0) (p : a.Program true) :
    (Constraint.nested m d a).Finite L :=
  ⟨p, finitePlacement m L (.heads d), finitePlacement_agrees m L (.heads d)⟩

def finiteModifier {k : Nat} (m : Structural.Core k) (L : Lasso (Fin k) size last)
    (item : Modifiers.Placement (Fin k) × Formula (SetAtom (Fin k)) (SetExpr (Fin k)) 0)
    (p : item.2.Program true) : (modifierConstraint m item).Finite L :=
  ⟨p, finitePlacement m L item.1, finitePlacement_agrees m L item.1⟩

namespace Constraint.Finite
variable {c : Constraint C A D (Fin size)} {L : Lasso C size last}

def domain (p : c.Finite L) (F : FinitePartialObservation A D size last) : Bool :=
  p.program.domain.attachedFinite L F.checked p.contexts

def value (p : c.Finite L) (F : FinitePartialObservation A D size last) : Bool :=
  p.program.value.attachedFinite L F.checked p.contexts

-- [proof->req~behavioral-qualification~1]
theorem domain_agrees (p : c.Finite L) {O : PartialObservation A D (Fin size)}
    (F : FinitePartialAdapter L O) : p.domain F.observations = true ↔
      ∀ t x, x ∈ c.contexts L.unfold t → x ∈ L.unfold.live t →
        c.body.Defined L.unfold O (.closed x) t := by
  rw [domain, Core.attachedFinite_agrees L _ _ (F.observations.checked_agrees L O F.agrees)]
  simp only [p.program.domain_eq, Formula.lower_agrees, Formula.domainFormula_agrees,
    ← p.contexts_agree, Finset.mem_coe]

theorem value_agrees (p : c.Finite L) {O : PartialObservation A D (Fin size)}
    (F : FinitePartialAdapter L O) : p.value F.observations = true ↔
      ∀ t x, x ∈ c.contexts L.unfold t → x ∈ L.unfold.live t →
        c.body.denote L.unfold O.canonical true (.closed x) t := by
  rw [value, Core.attachedFinite_agrees L _ _ (F.observations.checked_agrees L O F.agrees)]
  simp only [p.program.value_eq, Core.mapAtoms_agrees L.unfold O.canonical O.checked CheckedAtom.value
    (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => rfl), Formula.normalize_lower_agrees,
    ← p.contexts_agree, Finset.mem_coe]

theorem holds_iff (p : c.Finite L) {O : PartialObservation A D (Fin size)}
    (F : FinitePartialAdapter L O) :
    (p.domain F.observations = true ∧ p.value F.observations = true) ↔ c.Holds L.unfold O := by
  rw [p.domain_agrees F, p.value_agrees F]
  simp only [Constraint.Holds, Formula.PartialAttached, Formula.Satisfies]
  exact ⟨fun ⟨hd, hv⟩ t x hc hl => ⟨hd t x hc hl, hv t x hc hl⟩,
    fun h => ⟨fun t x hc hl => (h t x hc hl).1, fun t x hc hl => (h t x hc hl).2⟩⟩

end Constraint.Finite

-- [impl->req~behavioral-qualification~1]
structure FiniteBundle (L : Lasso C size last) (constraints : Fin count → Constraint C A D (Fin size)) where
  programs : ∀ i, (constraints i).Finite L

namespace FiniteBundle
variable {L : Lasso C size last} {constraints : Fin count → Constraint C A D (Fin size)}

def domain (p : FiniteBundle L constraints) (F : FinitePartialObservation A D size last) : Bool :=
  decide (∀ i, (p.programs i).domain F = true)

def value (p : FiniteBundle L constraints) (F : FinitePartialObservation A D size last) : Bool :=
  decide (∀ i, (p.programs i).value F = true)

-- [proof->req~behavioral-qualification~1]
theorem holds_iff (p : FiniteBundle L constraints) {O : PartialObservation A D (Fin size)}
    (F : FinitePartialAdapter L O) :
    (p.domain F.observations = true ∧ p.value F.observations = true) ↔
      ∀ c ∈ Set.range constraints, c.Holds L.unfold O := by
  simp only [domain, value, decide_eq_true_eq, Set.forall_mem_range]
  constructor
  · intro h i; exact ((p.programs i).holds_iff F).mp ⟨h.1 i, h.2 i⟩
  · intro h
    exact ⟨fun i => (((p.programs i).holds_iff F).mpr (h i)).1,
      fun i => (((p.programs i).holds_iff F).mpr (h i)).2⟩

end FiniteBundle

section Model
variable {k modifiersCount : Nat} (m : Structural.Core k) (declared : Fin k → Set Modifiers.Modifier)
  (O : Trace (Fin k) (Fin size) → PartialObservation A D (Fin size))
  {constraints : Fin count → Constraint (Fin k) A D (Fin size)}
  {modifiers : Fin modifiersCount → Constraint (Fin k) (SetAtom (Fin k)) (SetExpr (Fin k)) (Fin size)}
  {L : Lasso (Fin k) size last}
  (p : FiniteBundle L constraints) (q : FiniteBundle L modifiers)

-- [impl->req~behavioral-qualification~1]
def bodyCheck (F : FinitePartialObservation A D size last)
    (G : FinitePartialObservation (SetAtom (Fin k)) (SetExpr (Fin k)) size last) : Formula.Program.Result :=
  if p.domain F && q.domain G then
    if p.value F && q.value G then .satisfied else .violated
  else .undefined

-- [proof->req~behavioral-qualification~1]
/-- Complete source-model checking after independently established structural
admission. Constraint and modifier inventories must be exact, not samples. -/
theorem bodyCheck_correct
    (wf : m.WellFormed) (valid : Structural.Valid m L.unfold)
    (complete : Set.range modifiers = modifierConstraints m declared)
    (F : FinitePartialAdapter L (O L.unfold))
    (G : FinitePartialAdapter L (.ofTotal (.sets m.toEffectiveCore (Structural.observed m L.unfold)))) :
    bodyCheck p q F.observations G.observations = .satisfied ↔
      (Model.behavioral m declared O (Set.range constraints)).Satisfies L.unfold := by
  have hp := p.holds_iff F
  have hq : (q.domain G.observations = true ∧ q.value G.observations = true) ↔
      Modifiers.Holds m L.unfold declared := by
    rw [q.holds_iff G, complete, modifierConstraints_iff m declared _ valid]
  change _ ↔ (m.WellFormed ∧ Structural.Valid m L.unfold ∧ Modifiers.Holds m L.unfold declared) ∧
    ∀ c ∈ Set.range constraints, c.Holds L.unfold (O L.unfold)
  simp only [wf, valid, true_and, ← hq, ← hp]
  unfold bodyCheck
  cases p.domain F.observations <;> cases q.domain G.observations <;>
    cases p.value F.observations <;> cases q.value G.observations <;> simp

end Model

-- [impl->req~behavioral-qualification~1]
def commonCheck {k modifiersCount : Nat} (m : Semantics.EffectiveCore k)
    {L : Lasso (Fin k) size last}
    {constraints : Fin count → Constraint (Fin k) A D (Fin size)}
    {modifiers : Fin modifiersCount → Constraint (Fin k) (SetAtom (Fin k)) (SetExpr (Fin k)) (Fin size)}
    (p : FiniteBundle L constraints) (q : FiniteBundle L modifiers)
    (F : FinitePartialObservation A D size last)
    (G : FinitePartialObservation (SetAtom (Fin k)) (SetExpr (Fin k)) size last) : Bool :=
  decide (L.checks m) && decide (bodyCheck p q F G = .satisfied)

-- [proof->req~behavioral-qualification~1]
theorem commonCheck_correct {k modifiersCount : Nat} (m : Semantics.EffectiveCore k)
    (wf : m.WellFormed) (support : m.Supported)
    (groups : ∀ d, m.group d = (m.family.group d).effective.range)
    (declared : Fin k → Set Modifiers.Modifier)
    (O : Trace (Fin k) (Fin size) → PartialObservation A D (Fin size))
    {L : Lasso (Fin k) size last}
    {constraints : Fin count → Constraint (Fin k) A D (Fin size)}
    {modifiers : Fin modifiersCount → Constraint (Fin k) (SetAtom (Fin k)) (SetExpr (Fin k)) (Fin size)}
    (p : FiniteBundle L constraints) (q : FiniteBundle L modifiers)
    (complete : Set.range modifiers = modifierConstraints (Structural.Core.ofEffective m) declared)
    (F : FinitePartialAdapter L (O L.unfold))
    (G : FinitePartialAdapter L (.ofTotal (.sets m (Structural.observed (Structural.Core.ofEffective m) L.unfold)))) :
    commonCheck m p q F.observations G.observations = true ↔
      (Model.behavioral (Structural.Core.ofEffective m) declared O (Set.range constraints)).Satisfies L.unfold := by
  simp only [commonCheck, Bool.and_eq_true, decide_eq_true_eq, Lasso.checks_iff, Lasso.valid_iff_unfold]
  constructor
  · rintro ⟨hv, hb⟩
    exact (bodyCheck_correct _ declared O p q (Structural.Core.ofEffective_wellFormed wf support groups)
      ((Structural.valid_iff_common wf support groups _).mpr hv) complete F G).mp hb
  · intro h
    have hv := h.1.2.1
    exact ⟨(Structural.valid_iff_common wf support groups _).mp hv,
      (bodyCheck_correct _ declared O p q (Structural.Core.ofEffective_wellFormed wf support groups)
        hv complete F G).mpr h⟩

end Properties

-- [proof->req~behavioral-qualification~1]
theorem Transitions.Chain.finite_agrees {A D : Nat → Type} {C : Type} {size last n : Nat}
    (L : Lasso C size last) {O : PartialObservation A D (Fin size)} (F : FinitePartialAdapter L O)
    (context : Formula A D n) (chain : Transitions.Chain A D n) (sign : Bool)
    (p : (chain.expand context).Program sign) (ρ : FiniteEnvironment size n) (t : Nat) :
    p.check L F.observations ρ t = .satisfied ↔
      (chain.expand context).Defined L.unfold O ρ.realize t ∧
      chain.meaning L.unfold O.canonical context ρ.realize sign t :=
  (p.check_satisfied L F ρ t).trans (chain.partial_agrees _ _ _ _ _ _)

-- [proof->req~behavioral-qualification~1]
theorem Patterns.finite_agrees {A D : Nat → Type} {C : Type} {size last n : Nat}
    (L : Lasso C size last) {O : PartialObservation A D (Fin size)} (F : FinitePartialAdapter L O)
    (pattern : Patterns.Pattern (Formula A D n)) (scope : Patterns.Scope (Formula A D n))
    (sign : Bool) (p : (Patterns.expand pattern scope).Program sign)
    (ρ : FiniteEnvironment size n) (t : Nat) :
    p.check L F.observations ρ t = .satisfied ↔
      (Patterns.expand pattern scope).Defined L.unfold O ρ.realize t ∧
      Patterns.meaning (L.unfold.ParentPresent ρ.this)
        (pattern.map (fun a s => a.denote L.unfold O.canonical s ρ.realize))
        (scope.map (fun a s => a.denote L.unfold O.canonical s ρ.realize)) sign t :=
  (p.check_satisfied L F ρ t).trans (Patterns.partial_agrees _ _ _ _ _ _ _)

end Clafer.Behavioral
