module

public import Clafer.Behavioral.Aggregate
public import Clafer.Behavioral.IntegerObservationExamples

/-! D3 collection/occurrence and empty-extrema boundary witnesses. -/

@[expose] public section
namespace Clafer.Behavioral.AggregateExamples
open Aggregate IntegerObservationExamples

-- [utest->req~behavioral-integer-aggregates~1]
theorem repeated_head_values :
    Fold.sum.eval (Set.univ : Set (Fin 2)) (fun _ => some 3) = some 6 ∧
    Fold.product.eval (Set.univ : Set (Fin 2)) (fun _ => some 3) = some 9 := by
  classical
  constructor <;> rw [fold_finite _ Set.finite_univ _ (by simp)] <;> simp

theorem distinct_target_conversion : IntegerObservation.coerce integers {3} = some 3 :=
  IntegerObservation.coerce_singleton integers 3

theorem empty_folds :
    Fold.sum.eval (∅ : Set Nat) (fun _ => none) = some 0 ∧
    Fold.product.eval (∅ : Set Nat) (fun _ => none) = some 1 := by simp

theorem missing_occurrence :
    Fold.sum.eval ({0, 1} : Set Nat) (fun x => if x = 0 then some 3 else none) = none := by
  apply fold_missing _ _ (x := 1) (by simp)
  simp

theorem infinite_observation :
    Fold.product.eval (Set.univ : Set Nat) (fun _ => some 1) = none :=
  fold_infinite _ Set.infinite_univ _

theorem empty_extrema (op : Extreme) :
    op.select integers ∅ = some ∅ ∧
    op.select integers ∅ ≠ some {0} ∧
    IntegerObservation.operand integers (op.select integers ∅) = some 0 := by simp

theorem finite_extrema :
    Extreme.minimum.select integers {-2, 5} = some {-2} ∧
    Extreme.maximum.select integers {-2, 5} = some {5} := by
  have typed : ({-2, 5} : Set Int) ⊆ integers.domain := fun x _ => ⟨x, rfl⟩
  have finite := (Set.finite_singleton (5 : Int)).insert (-2)
  constructor <;> rw [select_finite _ integers finite typed] <;>
    congr 1 <;> ext x <;> simp [Extreme.before, integers] <;> omega

theorem infinite_extrema (op : Extreme) : op.select integers Set.univ = none := by
  classical
  simp [Extreme.select, Set.infinite_univ]

theorem noninteger_extrema (op : Extreme) : op.select tagged {none} = none := by
  classical
  have bad : ¬ ({none} : Set (Option Int)) ⊆ tagged.domain := by
    intro h
    obtain ⟨n, hn⟩ := h (Set.mem_singleton _)
    cases hn
  simp [Extreme.select, bad]

end Clafer.Behavioral.AggregateExamples
