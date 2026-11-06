module

public import Clafer.Constraints.Denotation
public import Clafer.Behavioral.IntegerObservation

/-!
# Mathematical behavioral arithmetic

Reviewed D3 disposition for the 0.5.7 profile: unbounded Int, truncation toward
zero with matching remainder, and undefined division/remainder at zero.
The independent source rule deliberately differs from default Alloy's total
bitvector operations and Choco's zero-numerator/overflow optimizations.
-/

@[expose] public section
namespace Clafer.Behavioral.Arithmetic

inductive Binary where
  | add | subtract | multiply | divide | remainder

-- [impl->req~behavioral-integer-arithmetic~1]
def Binary.apply : Binary → Int → Int → Option Int
  | .add, a, b => some (a + b)
  | .subtract, a, b => some (a - b)
  | .multiply, a, b => some (a * b)
  | .divide, a, b => if b = 0 then none else some (a.tdiv b)
  | .remainder, a, b => if b = 0 then none else some (a.tmod b)

/-- Undefined operands propagate, including an undefined result of division. -/
def Binary.eval (op : Binary) (a b : Option Int) : Option Int :=
  a.bind fun x => b.bind fun y => op.apply x y

def negate (a : Option Int) : Option Int := a.map Int.neg

-- [proof->req~behavioral-integer-arithmetic~1]
theorem defined_iff (op : Binary) (a b : Int) :
    (∃ n, op.apply a b = some n) ↔
      (op = .divide ∨ op = .remainder → b ≠ 0) := by
  cases op <;> by_cases h : b = 0 <;> simp [Binary.apply, h]

@[simp] theorem divide_zero (a : Int) : Binary.divide.apply a 0 = none := by
  simp [Binary.apply]

@[simp] theorem remainder_zero (a : Int) : Binary.remainder.apply a 0 = none := by
  simp [Binary.apply]

theorem divide_nonzero (a b : Int) (h : b ≠ 0) :
    Binary.divide.apply a b = some (a.tdiv b) := by simp [Binary.apply, h]

theorem remainder_nonzero (a b : Int) (h : b ≠ 0) :
    Binary.remainder.apply a b = some (a.tmod b) := by simp [Binary.apply, h]

theorem division_remainder (a b q r : Int)
    (hq : Binary.divide.apply a b = some q)
    (hr : Binary.remainder.apply a b = some r) : b * q + r = a := by
  by_cases hz : b = 0
  · simp [hz] at hq
  · have eqQ := Option.some.inj ((divide_nonzero a b hz).symm.trans hq)
    have eqR := Option.some.inj ((remainder_nonzero a b hz).symm.trans hr)
    rw [← eqQ, ← eqR]
    exact Int.mul_tdiv_add_tmod a b

@[simp] theorem missing_left (op : Binary) (b : Option Int) : op.eval none b = none := rfl

@[simp] theorem missing_right (op : Binary) (a : Option Int) : op.eval a none = none := by
  cases a <;> rfl

/-- The historical scalar addition/subtraction core is unchanged, including
strict propagation of undefined operands. No collection conversion is assumed. -/
theorem static_arithmetic_agrees (op : Constraints.Arithmetic) (a b : Option Int) :
    ((match op with
      | .add => Binary.add
      | .subtract => Binary.subtract).eval a b).map (ULift.up : Int → ULift Int) =
    Constraints.lift₂ (fun (x y : ULift Int) => ULift.up (match op with
      | .add => x.down + y.down | .subtract => x.down - y.down))
      (a.map ULift.up) (b.map ULift.up) := by
  cases op <;> cases a <;> cases b <;> rfl

end Clafer.Behavioral.Arithmetic
