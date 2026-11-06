module

public import Clafer.Behavioral.Structural

/-! # Exact compatibility with the guarded static fragment

The larger 0.5.7 meaning does not alter `EffectiveCore.Supported` or the
existing snapshot/constant-trace theorems. On that domain the extra inherited
clauses reduce to the existing ones, and containment reachability is derived.
-/

@[expose] public section
namespace Clafer.Behavioral.Structural
open Semantics MCS DPGraph.Predicates
universe u

namespace Common
variable {n : Nat} {U : Type u} {m : EffectiveCore n}

theorem ancestor_cases (support : m.Supported) {d a : Fin n} (h : m.Ancestor d a) :
    d = a ∨ m.family.isAbstract a = true := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ edge _ => exact Or.inr (support.2.2.1 _ _ edge).1

theorem reference_ancestor_eq (support : m.Supported) {d a : Fin n}
    (h : m.Ancestor d a) (ref : m.family.reference a ≠ .basic) : d = a := by
  rcases ancestor_cases support h with he | ha
  · exact he
  · exact (ref (support.2.1 a ha).2.1).elim

theorem owner_eq (support : m.Supported) {d o : Fin n}
    (owner : InheritedReference.Owner m.family d o) : d = o :=
  reference_ancestor_eq support owner.ancestor owner.has_reference

theorem child_iff (support : m.Supported) (s : Configuration (Fin n) U) (d : Fin n) (p x : U) :
    Semantics.Groups.ChildObjects m.family s d p x ↔ s.Child m d p x := by
  constructor
  · rintro ⟨a, ha, c, hc, hx⟩
    rcases ancestor_cases support ha with he | habs
    · exact ⟨c, he ▸ hc, hx⟩
    · exact ((support.2.1 a habs).2.2.1 c hc).elim
  · rintro ⟨c, hc, hx⟩
    exact ⟨d, .refl, c, hc, hx⟩

theorem groups_iff (support : m.Supported)
    (agree : ∀ d, m.group d = (m.family.group d).effective.range)
    (τ : Trace (Fin n) U) (t : Nat) :
    Groups (Core.ofEffective m) τ t ↔ (τ.raw m t).Groups m := by
  unfold Groups Configuration.Groups Semantics.Groups.Holds
  simp only [Core.ofEffective]
  apply forall_congr'
  intro d
  apply imp_congr_right
  intro _
  rw [← agree d]
  constructor
  · intro h p hp
    exact (inRange_iff _ (Equiv.subtypeEquivRight (fun x => child_iff support _ d p x))).mp
      (h ⟨p, hp⟩)
  · intro h p
    exact (inRange_iff _ (Equiv.subtypeEquivRight (fun x => child_iff support _ d p.val x))).mpr
      (h p.val p.property)

theorem coherent (support : m.Supported) {τ : Trace (Fin n) U} {t : Nat}
    (h : τ.StateValid m t) : ReferenceCoherent τ t := by
  intro d e x y z hy hz
  obtain ⟨hx, a, ha, _⟩ := h.typed.2 d x y hy
  obtain ⟨hx', b, hb, _⟩ := h.typed.2 e x z hz
  have rd : m.family.reference d ≠ .basic := by intro he; simp [he, ReferenceTo.target] at ha
  have re : m.family.reference e ≠ .basic := by intro he; simp [he, ReferenceTo.target] at hb
  have he : d = e := (h.disjoint d e x hx hx').elim
    (fun p => reference_ancestor_eq support p re)
    (fun p => (reference_ancestor_eq support p rd).symm)
  subst e
  exact (h.references d a ha x hx).unique hy hz

theorem keys_iff (support : m.Supported) (τ : Trace (Fin n) U) (t : Nat) :
    Keys (Core.ofEffective m) τ t ↔ (τ.raw m t).Keys m := by
  constructor
  · intro h d hd p y x z hpx hxy hpz hzy
    have ref : m.family.reference d ≠ .basic := by
      intro he
      simp [he, ReferenceTo.kind] at hd
    exact h d d (.declared ref) hd p y x z hpx
      ⟨d, .declared ref, ⟨hpx.1.2.1, hpx.2.1⟩, hxy⟩ hpz
      ⟨d, .declared ref, ⟨hpz.1.2.1, hpz.2.1⟩, hzy⟩
  · intro h d o owner hd p y x z hpx hxy hpz hzy
    have he := owner_eq support owner
    subst o
    exact h d hd p y x z hpx ((InheritedReference.deref_owner owner x y).mp hxy).2
      hpz ((InheritedReference.deref_owner owner z y).mp hzy).2

/-- Local static guards rule out abstract parents of ordinary objects. The
declared parent rank then proves actual root reachability, with no extra axiom. -/
theorem reachable (wf : m.WellFormed) (support : m.Supported)
    {τ : Trace (Fin n) U} (h : τ.Valid m) (t : Nat) :
    ∀ x ∈ τ.live t, (τ.raw m t).Reaches x := by
  obtain ⟨rank, decrease⟩ := wf.1.parent_rank
  suffices ∀ k, ∀ x, rank (τ.identities.directType x) = k →
      x ∈ τ.live t → (τ.raw m t).Reaches x from fun x hx => this _ x rfl hx
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro x hk hx
    by_cases hr : x = τ.identities.root
    · subst x; exact .refl
    obtain ⟨p, hp⟩ := h.identities.parent_exists x hr
    obtain ⟨c, hc, hpc⟩ := h.identities.parent_typed x p hp
    have pc : τ.identities.directType p = c := by
      rcases ancestor_cases support hpc with he | ha
      · exact he
      · exact ((support.2.1 c ha).2.2.1 _ hc).elim
    have less : rank (τ.identities.directType p) < k := by
      rw [pc, ← hk]; exact decrease _ _ hc
    have reach := ih _ less p rfl (h.parent_live t x p hx hp)
    exact reach.tail ⟨τ.identities.directType x,
      ⟨h.parent_live t x p hx hp, hx, hp⟩, .refl, by simp [hc]⟩

end Common

-- [proof->req~behavioral-structural-compatibility~1]
theorem Core.ofEffective_wellFormed {n : Nat} {m : EffectiveCore n}
    (wf : m.WellFormed) (support : m.Supported)
    (agree : ∀ d, m.group d = (m.family.group d).effective.range) :
    (Core.ofEffective m).WellFormed where
  root_origin := wf.1.root_origin
  root_shape := ⟨wf.1.root_shape.1, wf.1.root_shape.2.1,
    wf.1.root_shape.2.2.1, wf.1.root_shape.2.2.2, wf.1.root_shape.2.2.2⟩
  primitive_shape := wf.1.primitive_shape
  unique_primitive := wf.1.unique_primitive
  authored_effective := fun _ h => h
  parentless_abstract := wf.1.parentless_abstract
  refined_parent := by
    intro d s p hs hp
    change m.family.parent s = some p at hp
    have hd := wf.1.inheritance_parent d s hs (by simp [hp])
    exact ⟨p, hd.trans hp, .refl⟩
  reference_refinement := by
    intro d s o a b hs owner _ _
    have he := Common.owner_eq support owner
    subst o
    exact (owner.has_reference (support.2.1 s (support.2.2.1 d s hs).1).2.1).elim
  parent_rank := wf.1.parent_rank
  super_rank := wf.1.super_rank
  ids := wf.2.1
  multiplicity_bounds := wf.1.valid_bounds
  group_bounds := wf.2.2
  group_agrees := agree

-- [proof->req~behavioral-structural-compatibility~1]
/-- Exact trace-validity equivalence, not just a map in one direction. Existing
snapshot and constant-embedding theorems therefore retain their full domain. -/
theorem valid_iff_common {n : Nat} {U : Type u} {m : EffectiveCore n}
    (wf : m.WellFormed) (support : m.Supported)
    (agree : ∀ d, m.group d = (m.family.group d).effective.range)
    (τ : Trace (Fin n) U) : Valid (Core.ofEffective m) τ ↔ τ.Valid m := by
  constructor
  · intro h
    refine ⟨⟨h.identities.root_type, h.identities.root_only, h.identities.concrete,
      h.identities.root_parent, h.identities.parent_exists, h.identities.parent_typed⟩,
      h.root_live, h.parent_live, ?_⟩
    intro t
    have hs := h.states t
    exact ⟨hs.typed, hs.root_head, hs.root_separate, hs.inherits, hs.abstracts,
      hs.parents, hs.references, (Common.keys_iff support τ t).mp hs.keys,
      hs.multiplicities, (Common.groups_iff support agree τ t).mp hs.groups, hs.disjoint⟩
  · intro h
    refine ⟨⟨h.identities.root_type, h.identities.root_only, h.identities.concrete,
      h.identities.root_parent, h.identities.parent_exists, h.identities.parent_typed⟩,
      h.root_live, h.parent_live, ?_⟩
    intro t
    have hs := h.states t
    exact ⟨hs.typed, hs.root_head, hs.root_separate, hs.inherits, hs.abstracts,
      hs.parents, hs.references, Common.coherent support hs,
      (Common.keys_iff support τ t).mpr hs.keys, hs.multiplicities,
      (Common.groups_iff support agree τ t).mpr hs.groups, hs.disjoint,
      Common.reachable wf support h t⟩

end Clafer.Behavioral.Structural
