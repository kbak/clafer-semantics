module

public import Clafer.Behavioral.StructuralObservation

/-! # Richer live-carrier observations

Behavioral Definition 2 and T8/T11. Effective groups and inherited-reference
heads, assignments and targets transport to the same live identities. This
projection does not assert the historical guarded `StructuralSatisfies` outside
its domain, nor any final/finalref/finaltarget modifier semantics.
-/

@[expose] public section
namespace Clafer.Behavioral.Structural
open Semantics DPGraph.Predicates ReferenceObservation
universe u
variable {n : Nat} {U : Type u} (m : Core n) (τ : Trace (Fin n) U)

-- [impl->req~behavioral-reference-atoms~1]
def current (t : Nat) : Configuration (Fin n) U := (observed m τ).raw m.toEffectiveCore t

def snapshot (h : Valid m τ) (t : Nat) : Configuration (Fin n) (τ.Live t) where
  root := ⟨τ.identities.root, h.root_live t⟩
  head d := {x | x.val ∈ (current m τ t).head d}
  contains d p x := (current m τ t).contains d p.val x.val
  deref d x y := (current m τ t).deref d x.val y.val

def childrenEquiv (h : Valid m τ) (t : Nat) (d : Fin n) (p : τ.Live t) :
    {x // Semantics.Groups.ChildObjects m.family (snapshot m τ h t) d p x} ≃
      {x // Semantics.Groups.ChildObjects m.family (current m τ t) d p.val x} where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, by
    obtain ⟨a, _, c, _, hc⟩ := x.property
    exact hc.1.2.1⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- [proof->req~behavioral-structural-compatibility~1]
theorem snapshot_groups (h : Valid m τ) (t : Nat) (d : Fin n)
    (ordinary : m.authoredAbstract d = false) :
    Semantics.Groups.Holds m.family (snapshot m τ h t) d := by
  intro p
  exact (inRange_iff _ (childrenEquiv m τ h t d p.val)).mpr
    ((h.states t).groups d ordinary ⟨p.val.val, p.property⟩)

-- [proof->req~behavioral-reference-atoms~1]
theorem snapshot_heads (h : Valid m τ) (t : Nat) (d : Fin n) (p : τ.Live t) :
    τ.embedding t '' heads (snapshot m τ h t) d p = heads (current m τ t) d p.val := by
  ext x
  exact ⟨fun ⟨a, ha, he⟩ => he ▸ ha, fun hx => ⟨⟨x, hx.1.2.1⟩, hx, rfl⟩⟩

theorem snapshot_assignments (h : Valid m τ) (t : Nat) (d : Fin n) (p : τ.Live t) :
    (fun xy : τ.Live t × τ.Live t => (xy.1.val, xy.2.val)) ''
      assignments (snapshot m τ h t) d p = assignments (current m τ t) d p.val := by
  ext xy
  constructor
  · rintro ⟨⟨x, y⟩, hxy, rfl⟩; exact hxy
  · rintro ⟨hx, hd⟩
    exact ⟨(⟨xy.1, hx.1.2.1⟩, ⟨xy.2, h.target_live hd⟩), ⟨hx, hd⟩, rfl⟩

theorem snapshot_targets (h : Valid m τ) (t : Nat) (d : Fin n) (p : τ.Live t) :
    τ.embedding t '' targets (snapshot m τ h t) d p = targets (current m τ t) d p.val := by
  ext y
  constructor
  · rintro ⟨b, ⟨a, ha, hd⟩, rfl⟩; exact ⟨a.val, ha, hd⟩
  · rintro ⟨a, ha, hd⟩
    exact ⟨⟨y, h.target_live hd⟩, ⟨⟨a, ha.1.2.1⟩, ha, hd⟩, rfl⟩

theorem finite_current_targets (h : Valid m τ) (t : Nat) (d : Fin n) (p : U)
    (finite : (heads (current m τ t) d p).Finite) : (targets (current m τ t) d p).Finite :=
  ReferenceObservation.finite_targets _ _ _ finite
    (fun _ _ _ _ hy hz => h.refined_reference_agrees hy hz)

end Clafer.Behavioral.Structural
