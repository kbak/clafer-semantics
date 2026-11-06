module

public import Clafer.Behavioral.Arithmetic
public import Clafer.Behavioral.IntegerObservationExamples

/-! D3 signed division, missing values and unbounded arithmetic witnesses. -/

@[expose] public section
namespace Clafer.Behavioral.ArithmeticExamples
open Arithmetic IntegerObservation IntegerObservationExamples

-- [utest->req~behavioral-integer-arithmetic~1]
theorem signed_division :
    Binary.divide.apply (-5) 2 = some (-2) ∧
    Binary.divide.apply 5 (-2) = some (-2) ∧
    Binary.divide.apply (-5) (-2) = some 2 := by decide

theorem signed_remainder :
    Binary.remainder.apply (-5) 2 = some (-1) ∧
    Binary.remainder.apply 5 (-2) = some 1 ∧
    Binary.remainder.apply (-5) (-2) = some (-1) := by decide

theorem all_zero_divisors_rejected :
    Binary.divide.apply 5 0 = none ∧ Binary.divide.apply 0 0 = none ∧
    Binary.remainder.apply 5 0 = none ∧ Binary.remainder.apply 0 0 = none := by decide

theorem absent_numerator : Binary.divide.eval (coerce integers ∅) (some 2) = some 0 := by
  rw [coerce_empty]
  rfl

theorem absent_denominator : Binary.divide.eval (some 5) (coerce integers ∅) = none := by
  rw [coerce_empty]
  rfl

theorem absent_addend : Binary.add.eval (coerce integers ∅) (some 1) = some 1 := by
  rw [coerce_empty]
  rfl

theorem undefined_propagates :
    Binary.multiply.eval (some 0) (Binary.divide.apply 5 0) = none := rfl

theorem no_machine_overflow :
    Binary.multiply.apply 100000 100000 = some 10000000000 ∧
    Binary.add.apply 2147483640 100 = some 2147483740 := by decide

theorem arbitrary_addition (a b : Int) : Binary.add.apply a b = some (a + b) := rfl

theorem arbitrary_multiplication (a b : Int) : Binary.multiply.apply a b = some (a * b) := rfl

end Clafer.Behavioral.ArithmeticExamples
