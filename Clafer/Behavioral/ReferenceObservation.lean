module

public import Clafer.Behavioral.Snapshot
public import Clafer.Constraints.DenotationLaws
public import Clafer.Semantics.Groups
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Current reference observations

Juodisius et al., §5 Definitions 2–3, with pinned 0.5.7 T8/T11 and S4.
Heads, head-to-target assignments and target images are different observations.
These projections and finite-observation results reuse existing structural
meaning; they impose no final/finalref/finaltarget or new arithmetic policy.
-/

@[expose] public section
namespace Clafer.Behavioral.ReferenceObservation
open Semantics Constraints

universe u
variable {C : Type} {U : Type u}

-- [impl->req~behavioral-snapshot-bridge~1]
/-- The occurrences owned by one parent in a declaration view. -/
def heads (s : Configuration C U) (d : C) (p : U) : Set U :=
  {x | s.contains d p x}

/-- Retain the head coordinate even when different heads share a target. -/
def assignments (s : Configuration C U) (d : C) (p : U) : Set (U × U) :=
  {xy | xy.1 ∈ heads s d p ∧ s.deref d xy.1 xy.2}

/-- The target image is a set; it is not the occurrence inventory. -/
def targets (s : Configuration C U) (d : C) (p : U) : Set U :=
  {y | ∃ x, (x, y) ∈ assignments s d p}

-- [proof->req~behavioral-snapshot-bridge~1]
theorem targets_image (s : Configuration C U) (d : C) (p : U) :
    targets s d p = relationalImage (heads s d p) {xy | s.deref d xy.1 xy.2} := by
  ext y
  rfl

/-- Finitely many observed heads and functional references give finitely many
observed targets. No finite ambient carrier or primitive domain is assumed. -/
theorem finite_targets (s : Configuration C U) (d : C) (p : U)
    (finite : (heads s d p).Finite)
    (functional : ∀ x ∈ heads s d p, ∀ y z,
      s.deref d x y → s.deref d x z → y = z) : (targets s d p).Finite := by
  have hf : ∀ x ∈ heads s d p, Set.Finite {y | s.deref d x y} := by
    intro x hx
    exact (show Set.Subsingleton {y | s.deref d x y} from
      fun y hy z hz => functional x hx y z hy hz).finite
  have h := finite.biUnion hf
  apply h.subset
  rintro y ⟨x, hx, hy⟩
  exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, hy⟩⟩

variable {n : Nat} {m : EffectiveCore n} (τ : Trace (Fin n) U)

/-- Projection retains every head in the same parent fiber. -/
theorem snapshot_heads (h : τ.Valid m) (t : Nat) (d : Fin n) (p : τ.Live t) :
    τ.embedding t '' heads (τ.snapshot h t) d p = heads (τ.raw m t) d p.val := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hx
    exact ⟨⟨x, hx.1.2.1⟩, hx, rfl⟩

/-- Projection retains assignments with both coordinates, not only targets. -/
theorem snapshot_assignments (h : τ.Valid m) (t : Nat) (d : Fin n) (p : τ.Live t) :
    (fun xy : τ.Live t × τ.Live t => (xy.1.val, xy.2.val)) ''
      assignments (τ.snapshot h t) d p = assignments (τ.raw m t) d p.val := by
  ext xy
  constructor
  · rintro ⟨⟨x, y⟩, hxy, rfl⟩
    exact hxy
  · rintro ⟨hx, hd⟩
    obtain ⟨_, c, _, hy⟩ := (h.states t).typed.2 d xy.1 xy.2 hd
    exact ⟨(⟨xy.1, hx.1.2.1⟩, ⟨xy.2, hy.1⟩), ⟨hx, hd⟩, rfl⟩

theorem snapshot_targets (h : τ.Valid m) (t : Nat) (d : Fin n) (p : τ.Live t) :
    τ.embedding t '' targets (τ.snapshot h t) d p = targets (τ.raw m t) d p.val := by
  ext y
  constructor
  · rintro ⟨b, ⟨a, ha, hd⟩, rfl⟩
    exact ⟨a.val, ha, hd⟩
  · rintro ⟨a, ha, hd⟩
    obtain ⟨_, c, _, hy⟩ := (h.states t).typed.2 d a y hd
    exact ⟨⟨y, hy.1⟩, ⟨⟨a, ha.1.2.1⟩, ha, hd⟩, rfl⟩

theorem target_live (h : τ.Valid m) {t : Nat} {d : Fin n} {p y : U}
    (hy : y ∈ targets (τ.raw m t) d p) : y ∈ τ.live t := by
  obtain ⟨x, _, hd⟩ := hy
  obtain ⟨_, c, _, hc⟩ := (h.states t).typed.2 d x y hd
  exact hc.1

/-- A raw off-live dereference is rejected, rather than hidden by projection. -/
theorem absent_head_no_deref (h : τ.Valid m) {t : Nat} {d : Fin n} {x y : U}
    (hx : x ∉ τ.live t) : ¬ τ.deref t d x y := by
  intro hd
  exact hx ((h.states t).typed.2 d x y hd).1.1

theorem absent_parent_heads (t : Nat) (d : Fin n) (p : U) (hp : p ∉ τ.live t) :
    heads (τ.raw m t) d p = ∅ := by
  ext x
  simp only [heads, Trace.raw, Trace.ParentAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false]
  exact fun h => hp h.1.1

-- [proof->req~behavioral-snapshot-bridge~1]
/-- In particular, an observed finite set of integer reference heads has a
finite target image even though the complete integer realization is infinite. -/
theorem valid_finite_targets (h : τ.Valid m) (t : Nat) (d c : Fin n) (p : U)
    (ref : (m.family.reference d).target = some c)
    (finite : (heads (τ.raw m t) d p).Finite) :
    (targets (τ.raw m t) d p).Finite := by
  apply finite_targets _ _ _ finite
  intro x hx y z hy hz
  have head := ((h.states t).typed.1 d p x hx).1
  obtain ⟨a, _, unique⟩ := (h.states t).references d c ref x head
  exact (unique y hy).trans (unique z hz).symm

theorem valid_target_cardinality (h : τ.Valid m) (t : Nat) (d c : Fin n) (p : U)
    (ref : (m.family.reference d).target = some c)
    (finite : (heads (τ.raw m t) d p).Finite) :
    finiteCard (targets (τ.raw m t) d p) =
      some ⟨((targets (τ.raw m t) d p).ncard : Int)⟩ :=
  finiteCard_finite _ (valid_finite_targets τ h t d c p ref finite)

end Clafer.Behavioral.ReferenceObservation
