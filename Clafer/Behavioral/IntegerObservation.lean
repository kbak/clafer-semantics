module

public import Clafer.Constraints.Integer
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Integer-set conversion for behavioral arithmetic

The reviewed D3 extension to the 0.5.7 profile uses finite integer-set sums
for arithmetic operands, as in the pinned Alloy and Choco generators.
The empty set contributes zero. Relational equality/presence and the historical
SoSyM D.3–D.4 exact-singleton extraction keep their independent meanings.
This module chooses no division, remainder, overflow or empty-extremum policy.
-/

@[expose] public section
namespace Clafer.Behavioral.IntegerObservation
open Constraints
open scoped BigOperators

universe u
variable {U : Type u} (R : IntegerRealization U)

-- [impl->req~behavioral-integer-coercion~1]
/-- Defined exactly for finite observations entirely in the integer domain.
Each distinct integer target contributes once; reference-head aggregation is
a different operation. Invalid or infinite observations have no numeric fallback. -/
noncomputable def coerce (S : Set U) : Option Int := by
  classical
  exact if h : S.Finite then
    if S ⊆ R.domain then some (∑ x ∈ h.toFinset, R.decode x) else none
  else none

/-- A missing expression result is different from a defined empty collection. -/
noncomputable def operand (S : Option (Set U)) : Option Int := S.bind (coerce R)

-- [proof->req~behavioral-integer-coercion~1]
theorem coerce_finite {S : Set U} (h : S.Finite) (typed : S ⊆ R.domain) :
    coerce R S = some (∑ x ∈ h.toFinset, R.decode x) := by
  classical
  simp [coerce, h, typed]

theorem coerce_defined_iff (S : Set U) :
    (∃ n, coerce R S = some n) ↔ S.Finite ∧ S ⊆ R.domain := by
  classical
  unfold coerce
  split <;> simp_all

theorem coerce_infinite {S : Set U} (h : S.Infinite) : coerce R S = none := by
  classical
  simp [coerce, h]

theorem coerce_wrong_domain {S : Set U} {x : U} (hx : x ∈ S)
    (bad : x ∉ R.domain) : coerce R S = none := by
  classical
  have h : ¬ S ⊆ R.domain := fun typed => bad (typed hx)
  simp [coerce, h]

@[simp] theorem coerce_empty : coerce R ∅ = some 0 := by
  classical
  simp [coerce]

@[simp] theorem coerce_singleton (n : Int) : coerce R {R.encode n} = some n := by
  classical
  rw [coerce_finite R (Set.finite_singleton _) (by
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact ⟨n, rfl⟩)]
  simp [R.decode_encode]

/-- Agreement with the historical extraction on its entire defined domain. -/
theorem agrees_with_extract {S : Set U} {n : Int} (h : R.extract S = some n) :
    coerce R S = some n := by
  have hs := (R.extract_eq_some_iff S n).mp h
  change S = {R.encode n} at hs
  rw [hs, coerce_singleton]

@[simp] theorem operand_missing : operand R none = none := rfl

@[simp] theorem operand_empty : operand R (some ∅) = some 0 := coerce_empty R

end Clafer.Behavioral.IntegerObservation
