module

public import DPGraph.Predicates.Meaning
public import Mathlib.Data.Fintype.EquivFin

/-!
[impl->req~reusable-span-laws~1]
[proof->req~reusable-span-laws~1]
-/

/-! # Finite specialization of cardinal ranges

SoSyM Table 3/Appendix 1. Finiteness is local to the counted fiber;
this bridge does not restrict the generic span or model carriers.
-/

@[expose] public section
universe u
namespace DPGraph.Predicates

def CountInRange (r : Range) (k : Nat) : Prop :=
  r.lower ≤ k ∧ match r.upper with
    | .finite hi => k ≤ hi
    | .unbounded => True

instance (r : Range) (k : Nat) : Decidable (CountInRange r k) := by
  unfold CountInRange
  cases r.upper <;> infer_instance

/-- Exact finite specialization of the existing cardinal semantics, in both
directions, including empty fibers and an unbounded upper limit. -/
theorem inRange_card (r : Range) (A : Type u) [Fintype A] :
    InRange r A ↔ CountInRange r (Fintype.card A) := by
  unfold InRange CountInRange
  cases r.upper <;> simp [Function.Embedding.nonempty_iff_card_le]

end DPGraph.Predicates
