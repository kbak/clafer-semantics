module

public import Clafer.Behavioral.ReferenceObservation
public import Clafer.Behavioral.Examples

/-! T8/T11 observation boundaries: changing assignments can preserve the target
set; repeated-target bag heads retain their separate occurrence counts. -/

@[expose] public section
namespace Clafer.Behavioral.ReferenceObservationExamples
open Semantics Constraints ReferenceObservation Examples

/-- Two heads, two live targets, and a parent. Swapping the assignments changes
neither the heads nor the target image. This is observation data, not a claim
that a final modifier holds. -/
def swapped (swap : Bool) : Configuration Unit (Fin 5) where
  root := 0
  head _ := Set.univ
  contains _ p x := p = 0 ∧ (x = 1 ∨ x = 2)
  deref _ x y := if swap then (x = 1 ∧ y = 4) ∨ (x = 2 ∧ y = 3)
    else (x = 1 ∧ y = 3) ∨ (x = 2 ∧ y = 4)

-- [utest->req~behavioral-snapshot-bridge~1]
theorem swapped_same_heads : heads (swapped false) () 0 = heads (swapped true) () 0 := rfl

theorem swapped_same_targets : targets (swapped false) () 0 = targets (swapped true) () 0 := by
  ext y
  simp only [targets, assignments, heads, swapped, Bool.false_eq_true, ↓reduceIte,
    Set.mem_ofPred_eq]
  decide +revert

theorem swapped_different_assignments :
    assignments (swapped false) () 0 ≠ assignments (swapped true) () 0 := by
  intro h
  have first : ((1, 3) : Fin 5 × Fin 5) ∈ assignments (swapped false) () 0 := by
    simp [assignments, heads, swapped]
  have bad := h ▸ first
  exact (by simp [assignments, heads, swapped] :
    ((1, 3) : Fin 5 × Fin 5) ∉ assignments (swapped true) () 0) bad

-- [utest->req~behavioral-snapshot-bridge~1]
-- [utest->req~behavioral-identities~1]
theorem bag_heads : heads (cycling.raw model 0) 2 1 = {3, 4} := by
  ext x
  change ((cycling.raw model 0).contains 2 1 x) ↔ x = 3 ∨ x = 4
  dsimp only [Trace.raw, Trace.ParentAt, cycling, phaseLive, pool]
  simp only [Set.mem_ofPred_eq]
  decide +revert

theorem bag_targets : targets (cycling.raw model 0) 2 1 = {5} := by
  ext y
  simp only [targets, assignments, bag_heads, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  change (∃ x, (x = 3 ∨ x = 4) ∧ cycling.deref 0 2 x y) ↔ y = 5
  dsimp only [cycling, phaseDeref]
  decide +revert

theorem bag_counts : finiteCard (heads (cycling.raw model 0) 2 1) = some ⟨2⟩ ∧
    finiteCard (targets (cycling.raw model 0) 2 1) = some ⟨1⟩ := by
  simp [bag_heads, bag_targets, finiteCard]

theorem absent_head : ¬ cycling.deref 1 2 3 5 :=
  absent_head_no_deref cycling cycling_valid (by simp [cycling, phaseLive])

/-- Finite observations do not require a finite integer carrier. -/
def integerRefs : Configuration Unit Int where
  root := 0
  head _ := Set.univ
  contains _ p x := p = 0 ∧ (x = 1 ∨ x = 2)
  deref _ x y := (x = 1 ∨ x = 2) ∧ y = -37

theorem integer_targets : targets integerRefs () 0 = {-37} := by
  ext y
  simp only [targets, assignments, heads, integerRefs, Set.mem_ofPred_eq,
    Set.mem_singleton_iff, true_and]
  constructor
  · rintro ⟨_, _, _, rfl⟩; rfl
  · rintro rfl; exact ⟨1, Or.inl rfl, Or.inl rfl, rfl⟩

-- [utest->req~behavioral-snapshot-bridge~1]
theorem finite_integer_observation : (targets integerRefs () 0).Finite := by
  apply finite_targets
  · exact ((Set.finite_singleton (2 : Int)).insert 1).subset (by intro x h; exact h.2)
  · intro x _ y z hy hz
    exact hy.2.trans hz.2.symm

end Clafer.Behavioral.ReferenceObservationExamples
