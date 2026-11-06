module

public import Clafer.Behavioral.IntegerObservation

/-! D3 boundary witnesses: absence, zero, finite sets, strict extraction and
unbounded integer values. No backend bit width is part of these equations. -/

@[expose] public section
namespace Clafer.Behavioral.IntegerObservationExamples
open Constraints IntegerObservation

def integers : IntegerRealization Int where
  encode := Function.Embedding.refl _
  decode := id
  decode_encode _ := rfl

private theorem integers_domain : integers.domain = Set.univ := by
  ext x
  exact ⟨fun _ => trivial, fun _ => ⟨x, rfl⟩⟩

-- [utest->req~behavioral-integer-coercion~1]
theorem absent_contributes_zero : coerce integers ∅ = some 0 := coerce_empty _

theorem absent_stays_distinct : (∅ : Set Int) ≠ {0} ∧
    coerce integers ∅ = coerce integers {0} := by
  constructor
  · simp
  · exact (coerce_empty _).trans (coerce_singleton integers 0).symm

theorem strict_extraction_unchanged : integers.extract ∅ = none ∧
    operand integers (some ∅) = some 0 ∧ operand integers none = none := by
  simp

theorem multiple_values_sum : coerce integers {2, 3} = some 5 := by
  classical
  rw [coerce_finite integers ((Set.finite_singleton (3 : Int)).insert 2)
    (by rw [integers_domain]; exact Set.subset_univ _)]
  simp [integers]

theorem equal_targets_once : coerce integers ({2} ∪ {2}) = some 2 := by
  rw [Set.union_self]
  exact coerce_singleton integers 2

theorem arbitrary_integer (n : Int) : coerce integers {n} = some n :=
  coerce_singleton integers n

theorem infinite_domain_rejected : coerce integers Set.univ = none :=
  coerce_infinite _ Set.infinite_univ

/-- The decoder's arbitrary off-domain zero must never be used. -/
def tagged : IntegerRealization (Option Int) where
  encode := ⟨some, Option.some_injective _⟩
  decode := fun x => x.getD 0
  decode_encode _ := rfl

theorem noninteger_rejected : coerce tagged {none} = none := by
  apply coerce_wrong_domain tagged (Set.mem_singleton _)
  rintro ⟨n, h⟩
  cases h

end Clafer.Behavioral.IntegerObservationExamples
