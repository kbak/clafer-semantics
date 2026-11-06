module

public import Clafer.Behavioral.Trace

/-!
# Live structural snapshots and constant embedding

Juodisius et al., §5 Definitions 2–3 and 5.1/5.3, with T1/T11.
The bridge reuses the guarded SoSyM structural meaning. Cardinalities are
transported by equivalences of head-object fibers, not target sets.
-/

@[expose] public section
namespace Clafer.Behavioral
open Semantics DPGraph.Predicates

universe u
namespace Trace
variable {n : Nat} {U : Type u} {m : EffectiveCore n} (τ : Trace (Fin n) U)

-- [impl->req~behavioral-snapshot-bridge~1]
def snapshot (h : τ.Valid m) (t : Nat) : Configuration (Fin n) (τ.Live t) where
  root := ⟨τ.identities.root, h.root_live t⟩
  head d := {x | x.val ∈ (τ.raw m t).head d}
  contains d p x := (τ.raw m t).contains d p.val x.val
  deref d x y := (τ.raw m t).deref d x.val y.val

/-- Restriction preserves each occurrence in a containment fiber. -/
def fiberEquiv (h : τ.Valid m) (t : Nat) (d : Fin n) (p : τ.Live t) :
    {x // (τ.snapshot h t).contains d p x} ≃
      {x // (τ.raw m t).contains d p.val x} where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1.2.1⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The group union is also a union of head objects on both carriers. -/
def childEquiv (h : τ.Valid m) (t : Nat) (d : Fin n) (p : τ.Live t) :
    {x // (τ.snapshot h t).Child m d p x} ≃
      {x // (τ.raw m t).Child m d p.val x} where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, by obtain ⟨c, _, hc⟩ := x.property; exact hc.1.2.1⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- [proof->req~behavioral-snapshot-bridge~1]
/-- The structural conclusion is derived on the live carrier. The stronger
admission guard is needed to select the common language domain, not this transport. -/
theorem snapshot_structural (h : τ.Valid m) (t : Nat) :
    StructuralSatisfies m (τ.snapshot h t) := by
  have hs := h.states t
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro d p x hx
      obtain ⟨hx', c, hc, hp⟩ := hs.typed.1 d p.val x.val hx
      exact ⟨hx', c, hc, hp⟩
    · intro d x y hy
      obtain ⟨hx, c, hc, ht⟩ := hs.typed.2 d x.val y.val hy
      exact ⟨hx, c, hc, ht⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x
      exact ⟨fun hx => Subtype.ext ((hs.root_head x.val).mp hx),
        fun hx => (hs.root_head x.val).mpr (congrArg Subtype.val hx)⟩
    · exact hs.root_separate
    · intro x
      by_cases hx : x.val = τ.identities.root
      · exact Or.inl (Subtype.ext hx)
      · exact Or.inr ⟨τ.identities.directType x.val,
          fun he => hx (h.identities.root_only x.val he), x.property, .refl⟩
  · intro d c hc x hx
    exact hs.inherits d c hc x.val hx
  · intro d hd
    constructor
    · intro x hx
      exact (hs.abstracts d hd).1 x.val hx
    · intro c e hc he hne x hx
      exact (hs.abstracts d hd).2 c e hc he hne x.val hx
  · intro d c hc x hx
    obtain ⟨p, hp, unique⟩ := hs.parents d c hc x.val hx
    refine ⟨⟨p, hp.1.1⟩, hp, ?_⟩
    intro q hq
    exact Subtype.ext (unique q.val hq)
  · intro d c hc x hx
    obtain ⟨y, hy, unique⟩ := hs.references d c hc x.val hx
    have hyLive : y ∈ τ.live t := by
      obtain ⟨_, e, _, he⟩ := hs.typed.2 d x.val y hy
      exact he.1
    refine ⟨⟨y, hyLive⟩, hy, ?_⟩
    intro z hz
    exact Subtype.ext (unique z.val hz)
  · intro d hd p y x z hpx hxy hpz hzy
    exact Subtype.ext (hs.keys d hd p.val y.val x.val z.val hpx hxy hpz hzy)
  · intro d c hc p hp
    exact (inRange_iff _ (τ.fiberEquiv h t d p)).mpr (hs.multiplicities d c hc p.val hp)
  · intro d hd p hp
    exact (inRange_iff _ (τ.childEquiv h t d p)).mpr (hs.groups d hd p.val hp)
  · intro d e x hd he
    exact hs.disjoint d e x.val hd he

/-- Admission keeps WellFormed/Supported explicit at the public fragment boundary. -/
theorem admissible_projection (h : τ.Admissible m) (t : Nat) :
    StructuralSatisfies m (τ.snapshot h.2.2 t) := τ.snapshot_structural h.2.2 t

-- [proof->req~behavioral-identities~1]
theorem snapshot_parent_stable (h : τ.Valid m) {i j : Nat} {d e : Fin n}
    {p x : τ.Live i} {q y : τ.Live j}
    (hi : (τ.snapshot h i).contains d p x)
    (hj : (τ.snapshot h j).contains e q y) (same : x.val = y.val) : p.val = q.val := by
  apply Option.some.inj
  exact hi.1.2.2.symm.trans ((congrArg τ.identities.parent same).trans hj.1.2.2)

/-- Distinct bag heads cannot be collapsed by projection, even at equal targets. -/
theorem snapshot_distinct (t : Nat) {x y : τ.Live t} (hne : x.val ≠ y.val) : x ≠ y :=
  fun he => hne (congrArg Subtype.val he)

end Trace

-- [impl->req~behavioral-snapshot-bridge~1]
/-- Explicit stable correspondence for the converse. `head` names the direct-type
witness and its complete super closure; `contains` names the actual parent witness.
Existence is not inferred from arbitrary overlapping structural extents. -/
structure StaticCorrespondence {n : Nat} {U : Type u} (m : EffectiveCore n)
    (s : Configuration (Fin n) U) (ids : Identities (Fin n) U) : Prop where
  identities : ids.Valid m
  root : ids.root = s.root
  head : ∀ d x, x ∈ s.head d ↔ m.Ancestor (ids.directType x) d
  contains : ∀ d p x, s.contains d p x ↔
    ids.parent x = some p ∧ m.Ancestor (ids.directType x) d ∧ m.family.parent d ≠ none

namespace StaticCorrespondence
variable {n : Nat} {U : Type u} {m : EffectiveCore n}
    {s : Configuration (Fin n) U} {ids : Identities (Fin n) U}
    (c : StaticCorrespondence m s ids)

-- [impl->req~behavioral-traces~1]
/-- All structural objects are live, with fixed dereferences at every natural time. -/
def constant (_c : StaticCorrespondence m s ids) : Trace (Fin n) U where
  identities := ids
  live _ := Set.univ
  deref _ := s.deref

private theorem configuration_ext {C : Type} {a b : Configuration C U}
    (hr : a.root = b.root) (hh : a.head = b.head)
    (hc : a.contains = b.contains) (hd : a.deref = b.deref) : a = b := by
  cases a
  cases b
  cases hr
  cases hh
  cases hc
  cases hd
  rfl

-- [proof->req~behavioral-snapshot-bridge~1]
theorem constant_raw (t : Nat) : (c.constant).raw m t = s := by
  apply configuration_ext
  · exact c.root
  · funext d
    apply Set.ext
    intro x
    exact (by simpa [Trace.raw, constant] using (c.head d x).symm)
  · funext d p x
    apply propext
    simpa [Trace.raw, Trace.ParentAt, constant] using (c.contains d p x).symm
  · rfl

/-- A satisfying structural model embeds with exactly the stated stable witnesses. -/
theorem constant_valid (hs : StructuralSatisfies m s) : (c.constant).Valid m where
  identities := c.identities
  root_live _ := Set.mem_univ _
  parent_live _ _ _ _ _ := Set.mem_univ _
  states t := by
    have he := c.constant_raw t
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [he]; exact hs.1
    · rw [he]; simpa only [constant, c.root] using hs.2.1.1
    · rw [he]; simpa only [constant, c.root] using hs.2.1.2.1
    · rw [he]; exact hs.2.2.1
    · rw [he]; exact hs.2.2.2.1
    · rw [he]; exact hs.2.2.2.2.1
    · rw [he]; exact hs.2.2.2.2.2.1
    · rw [he]; exact hs.2.2.2.2.2.2.1
    · rw [he]; exact hs.2.2.2.2.2.2.2.1
    · rw [he]; exact hs.2.2.2.2.2.2.2.2.1
    · rw [he]; exact hs.2.2.2.2.2.2.2.2.2

theorem constant_admissible (wf : m.WellFormed) (support : m.Supported)
    (hs : StructuralSatisfies m s) : (c.constant).Admissible m :=
  ⟨wf, support, c.constant_valid hs⟩

/-- The live carrier is equivalent to the original carrier, not merely injected. -/
def constantEquiv (t : Nat) : (c.constant).Live t ≃ U where
  toFun := Subtype.val
  invFun x := ⟨x, Set.mem_univ _⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- [proof->req~behavioral-snapshot-bridge~1]
/-- Complete fieldwise recovery through the live-carrier equivalence. -/
theorem constant_snapshot (hs : StructuralSatisfies m s) (t : Nat) :
    (c.constantEquiv t) ((c.constant).snapshot (c.constant_valid hs) t).root = s.root ∧
    (∀ d x, x ∈ ((c.constant).snapshot (c.constant_valid hs) t).head d ↔
      c.constantEquiv t x ∈ s.head d) ∧
    (∀ d p x, ((c.constant).snapshot (c.constant_valid hs) t).contains d p x ↔
      s.contains d (c.constantEquiv t p) (c.constantEquiv t x)) ∧
    (∀ d x y, ((c.constant).snapshot (c.constant_valid hs) t).deref d x y ↔
      s.deref d (c.constantEquiv t x) (c.constantEquiv t y)) := by
  refine ⟨c.root, ?_, ?_, ?_⟩
  · intro d x
    change x.val ∈ ((c.constant).raw m t).head d ↔ x.val ∈ s.head d
    rw [c.constant_raw]
  · intro d p x
    change ((c.constant).raw m t).contains d p.val x.val ↔ s.contains d p.val x.val
    rw [c.constant_raw]
  · intros; rfl

-- [proof->req~behavioral-traces~1]
theorem constant_starts (t : Nat) (x : U) : (c.constant).Starts t x ↔ t = 0 := by
  simp [Trace.Starts, constant]

theorem constant_never_ends (t : Nat) (x : U) : ¬ (c.constant).Ends t x := by
  simp [Trace.Ends, constant]

end StaticCorrespondence
end Clafer.Behavioral
