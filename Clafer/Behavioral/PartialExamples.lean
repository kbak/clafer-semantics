module

public import Clafer.Behavioral.Initializers
public import Clafer.Behavioral.StaticObservation
public import Clafer.Behavioral.PrimitiveExpressionExamples
public import Clafer.Behavioral.Examples

/-! Strict-domain witnesses on admitted structural traces. These distinguish
undefined from false, truth from short-circuit definedness, and cancellation
from the attachment object's disappearance. -/

@[expose] public section
namespace Clafer.Behavioral.PartialExamples

abbrev A (_ : Nat) := Unit
abbrev D (_ : Nat) := Unit
abbrev F (n : Nat) := Formula A D n

def source : Environment (Fin 8) 0 := .closed 3
def missing : PartialObservation A D (Fin 8) where
  atom _ _ _ := none
  domain _ _ _ := some {5, 6}

def beforeGap : PartialObservation A D (Fin 8) where
  atom _ _ t := if t < 2 then some True else none
  domain _ _ _ := some ∅

private theorem parent_gone : ¬ Examples.cycling.ParentPresent 3 2 := by
  simp [Trace.ParentPresent, Examples.cycling, Examples.pool, Examples.phaseLive]

private theorem before_end {j : Nat}
    (through : Lifetime.Through (Examples.cycling.ParentPresent 3) 0 j) : j < 2 := by
  by_contra hn
  exact Lifetime.not_through_after_end (by decide : 0 ≤ 2) (Nat.le_of_not_gt hn) parent_gone through

-- [utest->req~behavioral-reference-atoms~1]
theorem strict_boolean :
    ¬ (Formula.or .truth (.atom ()) : F 0).Defined Examples.cycling missing source 0 ∧
    ¬ (Formula.ite .truth .truth (.atom ()) : F 0).Defined Examples.cycling missing source 0 := by
  simp [Formula.Defined, missing]

theorem cancellation_ends_definedness :
    (Formula.always (.atom ()) : F 0).Satisfies Examples.cycling beforeGap true source 0 := by
  constructor
  · intro j hj hp
    exact ⟨True, ite_eq_left (before_end hp)⟩
  · intro j hj hp
    change (if j < 2 then some True else none).getD False
    rw [ite_eq_left (before_end hp)]
    trivial

theorem reappearance_starts_new_domain :
    ¬ (Formula.always (.atom ()) : F 0).Defined Examples.cycling beforeGap source 3 := by
  intro h
  have hp : Lifetime.Through (Examples.cycling.ParentPresent 3) 3 3 := by
    intro k hk hk'
    have he : k = 3 := by omega
    subst k
    simp [Trace.ParentPresent, Examples.cycling, Examples.pool, Examples.phaseLive]
  obtain ⟨p, bad⟩ := h 3 (by decide) hp
  simp [beforeGap] at bad

theorem next_cancelled :
    (Formula.next (.atom ()) : F 0).Satisfies Examples.cycling missing true source 1 ∧
    (Formula.next (.atom ()) : F 0).Satisfies Examples.cycling missing false source 1 := by
  constructor <;> constructor <;> intro hp <;> exact (parent_gone hp).elim

theorem context_absence_does_not_cancel :
    ¬ (Formula.next (.atom ()) : F 0).Defined Examples.cycling missing source 0 := by
  intro h
  have hp : Examples.cycling.ParentPresent 3 1 := by
    simp [Trace.ParentPresent, Examples.cycling, Examples.pool, Examples.phaseLive]
  obtain ⟨p, bad⟩ := h hp
  cases bad

def onlyZero : PartialObservation A D (Fin 8) :=
  { beforeGap with atom := fun _ _ t => if t = 0 then some True else none }

theorem early_truth_does_not_hide_undefined :
    ¬ (Formula.eventually (.atom ()) : F 0).Defined Examples.cycling onlyZero source 0 := by
  intro h
  have hp : Lifetime.Through (Examples.cycling.ParentPresent 3) 0 1 := by
    intro k hk hk'
    have he : k = 0 ∨ k = 1 := by omega
    rcases he with rfl | rfl <;>
      simp [Trace.ParentPresent, Examples.cycling, Examples.pool, Examples.phaseLive]
  obtain ⟨p, bad⟩ := h 1 (by decide) hp
  simp [onlyZero] at bad

noncomputable def memberMissing : PartialObservation A D (Fin 8) where
  atom {n} _ ρ _ := by
    classical
    exact if ∃ i : Fin n, (6 : Fin 8) ∈ ρ.lookup i then none else some True
  domain _ _ _ := some {5, 6}

theorem every_quantified_member (q : Quantifier) :
    ¬ (Formula.quant q () (.atom ()) : F 0).Defined Examples.cycling memberMissing source 0 := by
  rintro ⟨S, hs, hbody⟩
  have he : S = {5, 6} := Option.some.inj hs.symm
  subst S
  obtain ⟨p, bad⟩ := hbody 6 (by simp)
  have hm : ∃ i : Fin 1, (6 : Fin 8) ∈ (source.push {6}).lookup i := ⟨0, rfl⟩
  simp [memberMissing, hm] at bad

theorem empty_domain_defined :
    (Formula.quant .all () (.atom ()) : F 0).Defined Examples.cycling
      { missing with domain := fun _ _ _ => some ∅ } source 0 :=
  ⟨∅, rfl, fun _ h => h.elim⟩

theorem inactive_anchor_defined :
    (Formula.initially (.atom ()) : F 0).Defined Examples.cycling missing source 1 := by
  intro h
  have hnot : ¬ Examples.cycling.Starts 1 3 := by
    simp [Trace.Starts, Examples.cycling, Examples.phaseLive]
  exact (hnot h).elim

open PrimitiveExpressionExamples in
theorem division_zero_neither :
    let O := PartialObservation.primitives model trace integers
    let a : Formula (PrimitiveExpression.Atom (Fin 3)) (CollectionExpr (Fin 3)) 0 :=
      .atom (.integerEqual (.binary .divide (.literal 5) (.literal 0)) (.literal 0))
    ¬ a.Satisfies trace O true (.closed (.inl 1)) 0 ∧
    ¬ a.Satisfies trace O false (.closed (.inl 1)) 0 := by
  dsimp only
  apply Formula.undefined_neither
  simp [Formula.Defined, PartialObservation.primitives, PrimitiveExpression.Atom.eval,
    PrimitiveExpression.division_zero, Constraints.lift₂]

open PrimitiveExpressionExamples in
theorem static_partial_extraction_neither :
    let e : Constraints.Expr support [] .boolean :=
      .equal (.integerOf (by decide) (.empty (.objects 2))) (.integer 0)
    let a : Formula (StaticObservation.Atom support) (StaticObservation.Domain support) 0 :=
      .atom (.ofExpr e)
    ¬ a.Satisfies trace (StaticObservation.observation trace.live binding) true (.closed (.inl 1)) 0 ∧
    ¬ a.Satisfies trace (StaticObservation.observation trace.live binding) false (.closed (.inl 1)) 0 := by
  dsimp only
  apply Formula.undefined_neither
  simp [Formula.Defined, StaticObservation.observation, StaticObservation.Atom.ofExpr,
    CapturedStatic.eval, Constraints.lift₂]

-- [utest->req~behavioral-structural-compatibility~1]
theorem initializer_default_refused :
    Initializers.Legacy.elaborate (C := Fin 3) (n := 0) .defaultValue
      (.set .this) (.set .this) (.literal 3) = none := rfl

open PrimitiveExpressionExamples in
theorem constant_is_not_birth_only :
    let a : Formula (PrimitiveExpression.Atom (Fin 3)) (CollectionExpr (Fin 3)) 0 :=
      Initializers.Legacy.constant (.set .this) (.set (.thisStep (.deref 1))) (.literal 3)
    a.Satisfies trace (.primitives model trace integers) true (.closed (.inl 1)) 0 ∧
    ¬ a.Satisfies trace (.primitives model trace integers) true (.closed (.inl 1)) 1 := by
  have head (t : Nat) : PrimitiveExpression.collection model.toEffectiveCore
      (Structural.observed model trace) integers (.closed (.inl 1)) t (.set .this) =
      some {Sum.inl 1} := by
    simp [PrimitiveExpression.collection, SetExpr.eval, Structural.observed, trace, Environment.closed]
  have value (t : Nat) : PrimitiveExpression.collection model.toEffectiveCore
      (Structural.observed model trace) integers (.closed (.inl 1)) t (.set (.thisStep (.deref 1))) =
      some {integers.encode (if t = 0 then 3 else 5)} := by
    change some (targetVariable.eval model.toEffectiveCore (Structural.observed model trace)
      ((Environment.closed (.inl 1)).push {.inl 1}) t) = _
    rw [current_target _ _ (Or.inl rfl)]
  dsimp only
  rw [Initializers.Legacy.constant_truth model trace integers (.closed (.inl 1)) 0 _ _ _ _ _ _
      (head 0) (value 0) rfl,
    Initializers.Legacy.constant_truth model trace integers (.closed (.inl 1)) 1 _ _ _ _ _ _
      (head 1) (value 1) rfl]
  simp [integers]

end Clafer.Behavioral.PartialExamples
