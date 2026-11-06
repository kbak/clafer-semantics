module

public import Clafer.Behavioral.IntegerObservation
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# Finite integer aggregates and extrema

Reviewed D3: explicit aggregates retain occurrence indices; extrema select
integer objects and preserve empty collections. See 0.5.7 static S8/S11 and
the source dispositions in docs/behavioral-structure.md. This interface does
not construct occurrence indices from unresolved frontend syntax.
-/

@[expose] public section
namespace Clafer.Behavioral.Aggregate
open Constraints
open scoped BigOperators

universe u v
variable {H : Type u} {U : Type v}

inductive Fold where
  | sum | product

-- [impl->req~behavioral-integer-aggregates~1]
/-- Distinct indices contribute separately even at equal values. A missing
value invalidates the whole fold; the internal default is unreachable on every
contributing index after the definedness guard. -/
noncomputable def Fold.eval (op : Fold) (S : Set H) (value : H → Option Int) : Option Int := by
  classical
  exact if h : S.Finite then
    if ∀ x ∈ S, (value x).isSome then
      some (match op with
        | .sum => ∑ x ∈ h.toFinset, (value x).getD 0
        | .product => ∏ x ∈ h.toFinset, (value x).getD 0)
    else none
  else none

-- [proof->req~behavioral-integer-aggregates~1]
theorem fold_defined_iff (op : Fold) (S : Set H) (value : H → Option Int) :
    (∃ n, op.eval S value = some n) ↔ S.Finite ∧ ∀ x ∈ S, (value x).isSome := by
  classical
  unfold Fold.eval
  split <;> simp_all

theorem fold_finite (op : Fold) {S : Set H} (h : S.Finite) (value : H → Option Int)
    (defined : ∀ x ∈ S, (value x).isSome) :
    op.eval S value = some (match op with
      | .sum => ∑ x ∈ h.toFinset, (value x).getD 0
      | .product => ∏ x ∈ h.toFinset, (value x).getD 0) := by
  classical
  simp only [Fold.eval, dite_eq_left h, ite_eq_left defined]

@[simp] theorem sum_empty (value : H → Option Int) : Fold.sum.eval ∅ value = some 0 := by
  classical
  simp [Fold.eval]

@[simp] theorem product_empty (value : H → Option Int) : Fold.product.eval ∅ value = some 1 := by
  classical
  simp [Fold.eval]

theorem fold_missing (op : Fold) {S : Set H} (value : H → Option Int)
    {x : H} (hx : x ∈ S) (missing : value x = none) : op.eval S value = none := by
  classical
  have bad : ¬ ∀ x ∈ S, (value x).isSome := by
    intro h
    simpa [missing] using h x hx
  simp [Fold.eval, bad]

theorem fold_infinite (op : Fold) {S : Set H} (h : S.Infinite)
    (value : H → Option Int) : op.eval S value = none := by
  classical
  simp [Fold.eval, h]

inductive Extreme where
  | minimum | maximum

def Extreme.before : Extreme → Int → Int → Prop
  | .minimum, x, y => x ≤ y
  | .maximum, x, y => y ≤ x

/-- A selector, not scalar extraction: the empty result is a defined empty set. -/
noncomputable def Extreme.select (op : Extreme) (R : IntegerRealization U)
    (S : Set U) : Option (Set U) := by
  classical
  exact if S.Finite ∧ S ⊆ R.domain then
    some {x | x ∈ S ∧ ∀ y ∈ S, op.before (R.decode x) (R.decode y)}
  else none

theorem select_defined_iff (op : Extreme) (R : IntegerRealization U) (S : Set U) :
    (∃ T, op.select R S = some T) ↔ S.Finite ∧ S ⊆ R.domain := by
  classical
  unfold Extreme.select
  split <;> simp_all

theorem select_finite (op : Extreme) (R : IntegerRealization U) {S : Set U}
    (h : S.Finite) (typed : S ⊆ R.domain) :
    op.select R S = some {x | x ∈ S ∧ ∀ y ∈ S, op.before (R.decode x) (R.decode y)} := by
  classical
  simp [Extreme.select, h, typed]

@[simp] theorem select_empty (op : Extreme) (R : IntegerRealization U) :
    op.select R ∅ = some ∅ := by
  classical
  simp [Extreme.select]

theorem select_subset (op : Extreme) (R : IntegerRealization U) {S T : Set U}
    (h : op.select R S = some T) : T ⊆ S := by
  classical
  unfold Extreme.select at h
  split at h
  · cases Option.some.inj h
    exact fun _ hx => hx.1
  · cases h

/-- A finite nonempty integer observation has exactly one selected object. -/
theorem select_singleton (op : Extreme) (R : IntegerRealization U) {S : Set U}
    (h : S.Finite) (typed : S ⊆ R.domain) (hne : S.Nonempty) :
    ∃ x ∈ S, op.select R S = some {x} := by
  classical
  have exists_best : ∃ x ∈ S, ∀ y ∈ S, op.before (R.decode x) (R.decode y) := by
    cases op with
    | minimum => exact Set.exists_min_image S R.decode h hne
    | maximum => exact Set.exists_max_image S R.decode h hne
  obtain ⟨x, hx, best⟩ := exists_best
  refine ⟨x, hx, ?_⟩
  rw [select_finite op R h typed]
  congr 1
  ext y
  constructor
  · rintro ⟨hy, hybest⟩
    have values : R.decode y = R.decode x := by
      cases op with
      | minimum => exact le_antisymm (hybest x hx) (best y hy)
      | maximum => exact le_antisymm (best y hy) (hybest x hx)
    exact (R.encode_decode (typed hy)).symm.trans
      ((congrArg R.encode values).trans (R.encode_decode (typed hx)))
  · rintro rfl
    exact ⟨hx, best⟩

/-- The reviewed empty-to-zero conversion applies after collection selection. -/
@[simp] theorem empty_extreme_operand (op : Extreme) (R : IntegerRealization U) :
    IntegerObservation.operand R (op.select R ∅) = some 0 := by
  rw [select_empty, IntegerObservation.operand_empty]

end Clafer.Behavioral.Aggregate
