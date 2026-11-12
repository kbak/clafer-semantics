module

public import Clafer.Behavioral.Properties
public import Clafer.Behavioral.Transitions

/-!
# Absent references and pending value obligations

Behavioral paper §5 Definitions 2–5 and §6.1, with T2/T7/T11 and the accepted
reading in issue #168. These are consequences of existing validity, current
navigation and parent-bounded meaning; no reference or temporal definition changes.
Relational singleton equality is separate from arithmetic empty-to-zero coercion.
-/

@[expose] public section
namespace Clafer.Behavioral.AbsentReference
open Semantics Constraints
universe u
variable {k n : Nat} {U : Type u}

-- [impl->req~behavioral-reference-atoms~1]
-- [proof->req~behavioral-reference-atoms~1]
/-- Typedness rejects hidden raw tuples. This applies both to guarded and richer
state validity, whose `typed` fields have exactly this type. -/
theorem raw_empty (m : EffectiveCore k) (τ : Trace (Fin k) U) {t : Nat}
    (typed : (τ.raw m t).Typed m) {x : U} (absent : x ∉ τ.live t) (d : Fin k) :
    {y | τ.deref t d x y} = ∅ := by
  ext y
  exact iff_false_intro (fun h => absent (typed.2 d x y h).1.1)

-- [proof->req~behavioral-inherited-reference-observation~1]
theorem inherited_empty (m : EffectiveCore k) (τ : Trace (Fin k) U) {t : Nat}
    {x : U} (absent : x ∉ τ.live t) (d : Fin k) :
    {y | InheritedReference.deref m.family (τ.raw m t) d x y} = ∅ := by
  ext y
  exact iff_false_intro (InheritedReference.absent_head τ absent)

-- [proof->req~behavioral-environments~1]
/-- Capture is retained even when its current dereference image is empty.
Observation filtering alone does not establish raw trace validity. -/
theorem captured_empty (m : EffectiveCore k) (τ : Trace (Fin k) U)
    (ρ : Environment U n) {t : Nat} {x : U} (absent : x ∉ τ.live t) (d : Fin k) :
    (SetExpr.var 0).eval m τ (ρ.push {x}) t = {x} ∧
    (SetExpr.step (.deref d) (.var 0)).eval m τ (ρ.push {x}) t = ∅ := by
  refine ⟨rfl, ?_⟩
  ext y
  rw [SetExpr.captured_deref]
  exact iff_false_intro (fun h => absent h.1)

theorem direct_empty (m : EffectiveCore k) (τ : Trace (Fin k) U)
    (ρ : Environment U n) {t : Nat} (absent : ρ.this ∉ τ.live t) (d : Fin k) :
    (SetExpr.thisStep (.deref d)).eval m τ ρ t = ∅ := by
  ext y
  simp [SetExpr.eval, Step.image, Step.relation, absent]

theorem direct_nonempty_live (m : EffectiveCore k) (τ : Trace (Fin k) U)
    (ρ : Environment U n) {t : Nat} (d : Fin k)
    (h : ((SetExpr.thisStep (.deref d)).eval m τ ρ t).Nonempty) :
    ρ.this ∈ τ.live t := by
  obtain ⟨y, x, hx, h⟩ := h
  exact (Set.mem_singleton_iff.mp hx) ▸ h.1

-- [proof->req~behavioral-reference-atoms~1]
/-- Never-live identities cannot introduce an unobserved raw reference choice. -/
theorem never_live (m : EffectiveCore k) (τ : Trace (Fin k) U)
    (typed : ∀ t, (τ.raw m t).Typed m) {x : U} (absent : ∀ t, x ∉ τ.live t) :
    ∀ t d, {y | τ.deref t d x y} = ∅ :=
  fun t d => raw_empty m τ (typed t) (absent t) d

section Primitive
variable (m : Structural.Core k) (τ : Trace (Fin k) U) (R : IntegerRealization U)
    (ρ : Environment U n) (t : Nat) (d : Fin k)

-- [impl->req~behavioral-formula-denotation~1]
/-- Resolved relational value equality, not equality after integer coercion. -/
def equalValue (d : Fin k) (v : Int) :
    Formula (PrimitiveExpression.Atom (Fin k)) (CollectionExpr (Fin k)) n :=
  .atom (.equal (.set (.thisStep (.deref d))) (.literal v))

-- [proof->req~behavioral-formula-denotation~1]
theorem equalValue_iff (v : Int) :
    (equalValue d v).Satisfies τ (.primitives m τ R) true ρ t ↔
      Structural.eval m τ (.thisStep (.deref d)) ρ t = {R.encode v} := by
  simp [equalValue, Formula.Satisfies, Formula.Defined, Formula.denote, polarity,
    PartialObservation.primitives, PartialObservation.canonical, PartialObservation.complete,
    PrimitiveExpression.Atom.eval, PrimitiveExpression.collection, Structural.eval]
  intro _
  exact ⟨_, Iff.rfl⟩

theorem next_equalValue_iff (v : Int) :
    (equalValue d v).next.Satisfies τ (.primitives m τ R) true ρ t ↔
      (τ.ParentPresent ρ.this (t + 1) →
        Structural.eval m τ (.thisStep (.deref d)) ρ (t + 1) = {R.encode v}) := by
  simp [equalValue, Formula.Satisfies, Formula.Defined, Formula.denote, polarity,
    Lifetime.next, PartialObservation.primitives, PartialObservation.canonical,
    PartialObservation.complete, PrimitiveExpression.Atom.eval,
    PrimitiveExpression.collection, Structural.eval]
  intro _ _
  exact ⟨_, Iff.rfl⟩

-- [proof->req~behavioral-reference-atoms~1]
theorem next_equalValue_live (v : Int) (parent : τ.ParentPresent ρ.this (t + 1))
    (obligation : (equalValue d v).next.Satisfies τ (.primitives m τ R) true ρ t) :
    ρ.this ∈ τ.live (t + 1) := by
  have he := (next_equalValue_iff m τ R ρ t d v).mp obligation parent
  apply direct_nonempty_live m.toEffectiveCore (Structural.observed m τ) ρ d
  rw [show (SetExpr.thisStep (.deref d)).eval m.toEffectiveCore
    (Structural.observed m τ) ρ (t + 1) = {R.encode v} from he]
  exact Set.singleton_nonempty _

/-- B/C and later same-identity rebirth: nothing at a later time or another
identity can repair failure at exactly `t + 1`. -/
theorem next_equalValue_absent (v : Int) (parent : τ.ParentPresent ρ.this (t + 1))
    (absent : ρ.this ∉ τ.live (t + 1)) :
    ¬ (equalValue d v).next.Satisfies τ (.primitives m τ R) true ρ t :=
  fun h => absent (next_equalValue_live m τ R ρ t d v parent h)

theorem next_unequalValue_absent (v : Int) (absent : ρ.this ∉ τ.live (t + 1)) :
    (equalValue d v).not.next.Satisfies τ (.primitives m τ R) true ρ t := by
  have he := direct_empty m.toEffectiveCore (Structural.observed m τ) ρ absent d
  simp [equalValue, Formula.Satisfies, Formula.Defined, Formula.denote, polarity,
    Lifetime.next, PartialObservation.primitives, PartialObservation.canonical,
    PartialObservation.complete, PrimitiveExpression.Atom.eval,
    PrimitiveExpression.collection, he]
  intro _
  exact ⟨False, id⟩

theorem next_distinct_values (v w : Int) (distinct : v ≠ w)
    (parent : τ.ParentPresent ρ.this (t + 1)) :
    ¬ ((equalValue d v).next.Satisfies τ (.primitives m τ R) true ρ t ∧
       (equalValue d w).next.Satisfies τ (.primitives m τ R) true ρ t) := by
  rintro ⟨hv, hw⟩
  have he := ((next_equalValue_iff m τ R ρ t d v).mp hv parent).symm.trans
    ((next_equalValue_iff m τ R ρ t d w).mp hw parent)
  exact distinct (R.encode.injective (Set.singleton_injective he))

theorem next_no_this_iff :
    (Formula.next (.not (.atom (.inhabited (.set .this)))) :
      Formula (PrimitiveExpression.Atom (Fin k)) (CollectionExpr (Fin k)) n).Satisfies
      τ (.primitives m τ R) true ρ t ↔
        (τ.ParentPresent ρ.this (t + 1) → ρ.this ∉ τ.live (t + 1)) := by
  simp [Formula.Satisfies, Formula.Defined, Formula.denote, polarity,
    Lifetime.next, PartialObservation.primitives, PartialObservation.canonical,
    PartialObservation.complete, PrimitiveExpression.Atom.eval,
    PrimitiveExpression.collection, SetExpr.eval, Structural.observed, Set.Nonempty]
  intro _ _
  exact ⟨_, Iff.rfl⟩

/-- The explicit `X (no this)` / `X (this.dref = v)` contradiction, under a
surviving parent. This does not depend on what any later state contains. -/
theorem next_disappearance_contradiction (v : Int)
    (parent : τ.ParentPresent ρ.this (t + 1)) :
    ¬ ((Formula.next (.not (.atom (.inhabited (.set .this)))) :
        Formula (PrimitiveExpression.Atom (Fin k)) (CollectionExpr (Fin k)) n).Satisfies
          τ (.primitives m τ R) true ρ t ∧
       (equalValue d v).next.Satisfies τ (.primitives m τ R) true ρ t) := by
  rintro ⟨gone, value⟩
  exact ((next_no_this_iff m τ R ρ t).mp gone parent)
    (next_equalValue_live m τ R ρ t d v parent value)

-- [proof->req~behavioral-reference-atoms~1]
/-- Empty reference images are defined collections, with separate coercion and
strict-extraction outcomes. These laws do not assert a value forces presence. -/
theorem absent_arithmetic (absent : ρ.this ∉ τ.live t) :
    PrimitiveExpression.integer m.toEffectiveCore (Structural.observed m τ) R ρ t
      (.coerce (.set (.thisStep (.deref d)))) = some 0 ∧
    PrimitiveExpression.integer m.toEffectiveCore (Structural.observed m τ) R ρ t
      (.extract (.set (.thisStep (.deref d)))) = none := by
  have he := direct_empty m.toEffectiveCore (Structural.observed m τ) ρ absent d
  simp [PrimitiveExpression.integer, PrimitiveExpression.integerValue,
    PrimitiveExpression.collection, he]

theorem absent_zero_comparison (absent : ρ.this ∉ τ.live t) :
    (PrimitiveExpression.Atom.integerEqual (.coerce (.set (.thisStep (.deref d))))
      (.literal 0)).eval m.toEffectiveCore (Structural.observed m τ) R ρ t = some True := by
  rw [PrimitiveExpression.Atom.eval, (absent_arithmetic m τ R ρ t d absent).1]
  simp [PrimitiveExpression.integer, PrimitiveExpression.integerValue, lift₂]

theorem absent_divisor (absent : ρ.this ∉ τ.live t) (v : Int) :
    PrimitiveExpression.integer m.toEffectiveCore (Structural.observed m τ) R ρ t
      (.binary .divide (.literal v) (.coerce (.set (.thisStep (.deref d))))) = none := by
  have he := direct_empty m.toEffectiveCore (Structural.observed m τ) ρ absent d
  simp [PrimitiveExpression.integer, PrimitiveExpression.integerValue,
    PrimitiveExpression.collection, he, Arithmetic.Binary.eval, Arithmetic.Binary.apply]

-- [impl->req~behavioral-transition-sugar~1]
/-- One resolved counter step. The source and target are relational equalities;
`nextValue` may implement increment/reset without changing the identity. -/
def valueTransition (d : Fin k) (v w : Int) :
    Formula (PrimitiveExpression.Atom (Fin k)) (CollectionExpr (Fin k)) n :=
  (Transitions.Chain.link (equalValue d v) none .immediate
    (.stop (equalValue d w))).expand .truth

-- [proof->req~behavioral-transition-sugar~1]
theorem valueTransition_iff (v w : Int) :
    (valueTransition d v w).Satisfies τ (.primitives m τ R) true ρ t ↔
      (Structural.eval m τ (.thisStep (.deref d)) ρ t = {R.encode v} →
        τ.ParentPresent ρ.this (t + 1) →
        Structural.eval m τ (.thisStep (.deref d)) ρ (t + 1) = {R.encode w}) := by
  classical
  simp [valueTransition, Transitions.Chain.expand, Transitions.precondition,
    Transitions.step, equalValue, Formula.Satisfies, Formula.Defined,
    Formula.denote, polarity, Lifetime.next, PartialObservation.primitives,
    PartialObservation.canonical, PartialObservation.complete, PrimitiveExpression.Atom.eval,
    PrimitiveExpression.collection, Structural.eval, or_iff_not_imp_left]
  intro _
  exact ⟨⟨_, Iff.rfl⟩, fun _ => ⟨_, Iff.rfl⟩⟩

theorem valueTransition_live (v w : Int)
    (source : Structural.eval m τ (.thisStep (.deref d)) ρ t = {R.encode v})
    (parent : τ.ParentPresent ρ.this (t + 1))
    (transition : (valueTransition d v w).Satisfies τ (.primitives m τ R) true ρ t) :
    ρ.this ∈ τ.live (t + 1) := by
  apply next_equalValue_live m τ R ρ t d w parent
  exact (next_equalValue_iff m τ R ρ t d w).mpr
    ((valueTransition_iff m τ R ρ t d v w).mp transition source)

/-- Any total next-value function (including increment/reset) keeps this exact
identity alive while its parent persists, provided every live state supplies a
singleton integer observation and issues the corresponding transition. Neither
initializers nor an arithmetic comparison imply these premises automatically. -/
theorem counter_alive (nextValue : Int → Int)
    (initial : ρ.this ∈ τ.live t)
    (parent : ∀ j, t ≤ j → τ.ParentPresent ρ.this (j + 1))
    (value : ∀ j, t ≤ j → ρ.this ∈ τ.live j → ∃ v,
      Structural.eval m τ (.thisStep (.deref d)) ρ j = {R.encode v})
    (rule : ∀ j, t ≤ j → ρ.this ∈ τ.live j → ∀ v,
      (valueTransition d v (nextValue v)).Satisfies τ (.primitives m τ R) true ρ j) :
    ∀ j, t ≤ j → ρ.this ∈ τ.live j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact initial
  | succ j hj ih =>
    obtain ⟨v, hv⟩ := value j hj ih
    exact valueTransition_live m τ R ρ j d v (nextValue v) hv (parent j hj) (rule j hj ih v)

end Primitive

-- [proof->req~behavioral-formula-denotation~1]
/-- Cancellation also removes the strict operand domain, even for undefined
arithmetic. Reappearance after this next state is irrelevant. -/
theorem next_cancel {A D : Nat → Type} {C : Type} (τ : Trace C U)
    (O : PartialObservation A D U) (a : Formula A D n) (s : Bool)
    (ρ : Environment U n) (t : Nat) (gone : ¬ τ.ParentPresent ρ.this (t + 1)) :
    a.next.Satisfies τ O s ρ t := by
  cases s <;> exact ⟨fun h => (gone h).elim, fun h => (gone h).elim⟩

-- [proof->req~behavioral-formula-denotation~1]
/-- Whole-model UNSAT requires an issued obligation and forced disappearance
in every candidate. Merely rejecting one disappearing candidate is weaker. -/
theorem forced_disappearance_unsat (m : Structural.Core k) (R : IntegerRealization U)
    (M : Properties.Model (Fin k) (PrimitiveExpression.Atom (Fin k)) (CollectionExpr (Fin k)) U)
    (d : Fin k) (v : Int)
    (observations : ∀ τ, M.observations τ = .primitives m τ R)
    (constraint : Properties.Constraint.nested m d (equalValue d v).next ∈ M.constraints)
    (forced : ∀ τ, M.Satisfies τ → ∃ t x,
      x ∈ (τ.raw m.toEffectiveCore t).head d ∧
      τ.ParentPresent x (t + 1) ∧ x ∉ τ.live (t + 1)) :
    ¬ ∃ τ, M.Satisfies τ := by
  rintro ⟨τ, hτ⟩
  obtain ⟨t, x, hx, hp, absent⟩ := forced τ hτ
  have h := hτ.2 _ constraint t x hx hx.1
  rw [observations] at h
  exact next_equalValue_absent m τ R (.closed x) t d v hp absent h

end Clafer.Behavioral.AbsentReference
