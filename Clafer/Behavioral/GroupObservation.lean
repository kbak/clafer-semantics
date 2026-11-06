module

public import Clafer.Behavioral.Snapshot
public import Clafer.Semantics.Groups

/-! T11/S3 effective groups: live projection preserves the complete inherited
child-head union. This transport does not assert that guarded state validity
enforces the richer inherited-group predicate. -/

@[expose] public section
namespace Clafer.Behavioral.GroupObservation
open Semantics DPGraph.Predicates

universe u
variable {n : Nat} {U : Type u} {m : EffectiveCore n} (τ : Trace (Fin n) U)

-- [impl->req~behavioral-snapshot-bridge~1]
/-- Each inherited child remains the same occurrence on the live carrier. -/
def childrenEquiv (h : τ.Valid m) (t : Nat) (d : Fin n) (p : τ.Live t) :
    {x // Groups.ChildObjects m.family (τ.snapshot h t) d p x} ≃
      {x // Groups.ChildObjects m.family (τ.raw m t) d p.val x} where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, by
    obtain ⟨a, _, c, _, hc⟩ := x.property
    exact hc.1.2.1⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- [proof->req~behavioral-snapshot-bridge~1]
-- [proof->req~clafer-compile-groups~1]
/-- Bounds transport without a finiteness assumption or target deduplication. -/
theorem bounds_iff (h : τ.Valid m) (t : Nat) (d : Fin n) (p : τ.Live t)
    (bounds : Range) :
    InRange bounds {x // Groups.ChildObjects m.family (τ.snapshot h t) d p x} ↔
      InRange bounds {x // Groups.ChildObjects m.family (τ.raw m t) d p.val x} :=
  inRange_iff bounds (childrenEquiv τ h t d p)

/-- Effective group satisfaction on a live snapshot is precisely the same
predicate on live context objects in the raw presentation. -/
theorem holds_iff (h : τ.Valid m) (t : Nat) (d : Fin n) :
    Groups.Holds m.family (τ.snapshot h t) d ↔
      ∀ p : U, p ∈ (τ.raw m t).head d →
        InRange (m.family.group d).effective.range
          {x // Groups.ChildObjects m.family (τ.raw m t) d p x} := by
  constructor
  · intro hs p hp
    exact (bounds_iff τ h t d ⟨p, hp.1⟩ _).mp (hs ⟨⟨p, hp.1⟩, hp⟩)
  · intro hs p
    exact (bounds_iff τ h t d p.val _).mpr (hs p.val.val p.property)

end Clafer.Behavioral.GroupObservation
