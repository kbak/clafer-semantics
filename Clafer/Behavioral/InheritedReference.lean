module

public import Clafer.Behavioral.ReferenceObservation

/-!
# Inherited reference observations

0.5.7 static S9 and temporal T8: explicit dereference uses the nearest declared
reference in the super chain. Its inherited views restrict the same relation
on the same head identity. These source observations do not elaborate names or
weaken the historical effective-core admission guards.
-/

@[expose] public section
namespace Clafer.Behavioral.InheritedReference
open Semantics MCS

universe u
variable {C : Type} {U : Type u}

-- [impl->req~behavioral-inherited-reference-observation~1]
/-- Read `family.reference` as declarations at each node, not a preflattened
table. A nearer declaration stops lookup; an all-basic chain has no owner. -/
inductive Owner (f : Family C) : C → C → Prop
  | declared {d} (ref : f.reference d ≠ .basic) : Owner f d d
  | inherited {d s o} (basic : f.reference d = .basic)
      (super : f.super d = some s) (owner : Owner f s o) : Owner f d o

-- [proof->req~behavioral-inherited-reference-observation~1]
theorem Owner.unique {f : Family C} {d a b : C}
    (ha : Owner f d a) (hb : Owner f d b) : a = b := by
  induction ha with
  | declared ref =>
    cases hb with
    | declared => rfl
    | inherited basic => exact (ref basic).elim
  | @inherited d s a basic super owner ih =>
    cases hb with
    | declared ref => exact (ref basic).elim
    | @inherited _ s' _ _ super' owner' =>
      have he : s' = s := Option.some.inj (super'.symm.trans super)
      subst s'
      exact ih owner'

theorem Owner.ancestor {f : Family C} {d o : C} (h : Owner f d o) :
    Groups.Ancestor f d o := by
  induction h with
  | declared => exact .refl
  | inherited _ super _ ih => exact ih.head super

theorem Owner.has_reference {f : Family C} {d o : C} (h : Owner f d o) :
    f.reference o ≠ .basic := by
  induction h with
  | declared ref => exact ref
  | inherited _ _ _ ih => exact ih

theorem no_owner {f : Family C} {d o : C}
    (basic : ∀ a, Groups.Ancestor f d a → f.reference a = .basic) :
    ¬ Owner f d o := fun h => h.has_reference (basic o h.ancestor)

theorem Owner.target {f : Family C} {d o : C} (h : Owner f d o) :
    ∃ c, (f.reference o).target = some c := by
  have hn := h.has_reference
  cases hr : f.reference o with
  | basic => exact (hn hr).elim
  | set c => exact ⟨c, rfl⟩
  | bag c => exact ⟨c, rfl⟩

/-- The view retains the original head coordinate; it creates no new link or
head identity. Owner lookup concerns declarations, not the target's name. -/
def deref (f : Family C) (s : Configuration C U) (d : C) (x y : U) : Prop :=
  ∃ o, Owner f d o ∧ x ∈ s.head d ∧ s.deref o x y

theorem deref_owner {f : Family C} {s : Configuration C U} {d o : C}
    (owner : Owner f d o) (x y : U) :
    deref f s d x y ↔ x ∈ s.head d ∧ s.deref o x y := by
  constructor
  · rintro ⟨o', ho, hx, hy⟩
    have he := ho.unique owner
    subst o'
    exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨o, owner, hx, hy⟩

theorem own_reference {f : Family C} {s : Configuration C U} {d : C}
    (ref : f.reference d ≠ .basic) (x y : U) :
    deref f s d x y ↔ x ∈ s.head d ∧ s.deref d x y :=
  deref_owner (.declared ref) x y

/-- Two inherited views of one owner agree on shared heads, even when their
declaration contexts differ. No equality of entire head extents is assumed. -/
theorem shared_head {f : Family C} {s : Configuration C U} {d e o : C}
    (hd : Owner f d o) (he : Owner f e o) {x : U}
    (xd : x ∈ s.head d) (xe : x ∈ s.head e) (y : U) :
    deref f s d x y ↔ deref f s e x y := by
  rw [deref_owner hd, deref_owner he]
  simp only [xd, xe]

variable {n : Nat} {m : EffectiveCore n} (τ : Trace (Fin n) U)

/-- Exact agreement with the existing declared-reference observation on valid
states; validity supplies the head-membership premise rather than assuming it. -/
theorem declared_agreement (valid : τ.Valid m) {t : Nat} {d : Fin n}
    (ref : m.family.reference d ≠ .basic) (x y : U) :
    deref m.family (τ.raw m t) d x y ↔ τ.deref t d x y := by
  rw [own_reference ref]
  exact ⟨fun h => h.2, fun h => ⟨((valid.states t).typed.2 d x y h).1, h⟩⟩

theorem target_live (valid : τ.Valid m) {t : Nat} {d : Fin n} {x y : U}
    (h : deref m.family (τ.raw m t) d x y) : y ∈ τ.live t := by
  obtain ⟨o, _, _, hy⟩ := h
  exact ((valid.states t).typed.2 o x y hy).2.choose_spec.2.1

theorem absent_head {t : Nat} {d : Fin n} {x y : U}
    (hx : x ∉ τ.live t) : ¬ deref m.family (τ.raw m t) d x y := by
  rintro ⟨_, _, h, _⟩
  exact hx h.1

/-- Owner functionality transfers to the inherited view. This does not assume
that the subtype's own declaration contains a reference annotation. -/
theorem functional (valid : τ.Valid m) {t : Nat} {d : Fin n} {x y z : U}
    (hy : deref m.family (τ.raw m t) d x y)
    (hz : deref m.family (τ.raw m t) d x z) : y = z := by
  obtain ⟨o, owner, hx, hy⟩ := hy
  have hz' := ((deref_owner owner x z).mp hz).2
  obtain ⟨c, hc⟩ := owner.target
  have head : x ∈ (τ.raw m t).head o := ⟨hx.1, hx.2.trans owner.ancestor⟩
  obtain ⟨a, _, unique⟩ := (valid.states t).references o c hc x head
  exact (unique y hy).trans (unique z hz').symm

end Clafer.Behavioral.InheritedReference
