module

public import DPGraph.Span.Composition

/-!
# Relation reduction and the adopted composition correction

SoSyM B.1 Theorems 1–2; B.2.1 as corrected in issue #4 (Q1). General pullback
composition agrees with existential relational composition after reduction.
Isomorphism requires joint endpoint injectivity. See `docs/sources.md` for the
source conflict, selected correction and the two-path counterexample.
-/

@[expose] public section

universe u v z w w'

namespace DPGraph

-- [impl->req~span-relation-composition~1]
/-- Existential relational composition in source-to-target order. -/
def relationComp {A : Type u} {B : Type v} {C : Type z}
    (R : A → B → Prop) (S : B → C → Prop) (a : A) (c : C) : Prop :=
  ∃ b, R a b ∧ S b c

/-- Single-valuedness allows a source to have no target. -/
def SingleValued {A : Type u} {B : Type v} (R : A → B → Prop) : Prop :=
  ∀ ⦃a b b'⦄, R a b → R a b' → b = b'

/-- At most one intermediate object, without an existence requirement. -/
def UniqueIntermediate {A : Type u} {B : Type v} {C : Type z}
    (R : A → B → Prop) (S : B → C → Prop) : Prop :=
  ∀ ⦃a c b b'⦄, R a b → S b c → R a b' → S b' c → b = b'

namespace Span

variable {A : Type u} {B : Type v} {C : Type z}

-- [impl->req~span-set-valuedness~1]
/-- A relation has at most one link for each endpoint pair (SoSyM B.1). -/
def ofRelation (R : A → B → Prop) : Span.{u, v, max u v} A B where
  Link := { p : A × B // R p.1 p.2 }
  source p := p.1.1
  target p := p.1.2

theorem red_ofRelation (R : A → B → Prop) : (ofRelation R).red = R := by
  funext a b
  apply propext
  constructor
  · rintro ⟨⟨⟨a', b'⟩, h⟩, hs, ht⟩
    cases hs
    cases ht
    exact h
  · intro h
    exact ⟨⟨(a, b), h⟩, rfl, rfl⟩

theorem ofRelation_jointlyInjective (R : A → B → Prop) :
    (ofRelation R).JointlyInjective := by
  intro l m h
  exact Subtype.ext h

-- [proof->req~span-family-correspondence~1]
/-- B.1 Theorem 2: joint injectivity is precisely fiberwise injectivity. -/
theorem jointlyInjective_iff_fiberwise (q : Span.{u, v, w} A B) :
    q.JointlyInjective ↔ ∀ a, Function.Injective (q.toFamily.eval a) := by
  constructor
  · intro h a l m he
    apply Subtype.ext
    exact h (Prod.ext (l.2.trans m.2.symm) he)
  · intro h l m he
    have hs := congrArg Prod.fst he
    have ht := congrArg Prod.snd he
    exact congrArg Subtype.val (@h (q.source l) ⟨l, rfl⟩ ⟨m, hs.symm⟩ ht)

/-- The canonical quotient of links to their endpoint pair. -/
def toRelation (q : Span.{u, v, w} A B) (l : q.Link) : (ofRelation q.red).Link :=
  ⟨(q.source l, q.target l), ⟨l, rfl, rfl⟩⟩

theorem toRelation_surjective (q : Span.{u, v, w} A B) :
    Function.Surjective q.toRelation := by
  rintro ⟨⟨a, b⟩, l, hs, ht⟩
  refine ⟨l, Subtype.ext ?_⟩
  exact Prod.ext hs ht

/-- B.1 Theorem 2, constructing the isomorphism when no parallel links occur. -/
noncomputable def relationIso (q : Span.{u, v, w} A B) (h : q.JointlyInjective) :
    Iso q (ofRelation q.red) where
  equiv := Equiv.ofBijective q.toRelation
    ⟨fun _ _ he => h (congrArg Subtype.val he), q.toRelation_surjective⟩
  source_eq _ := rfl
  target_eq _ := rfl

theorem jointlyInjective_of_iso {q : Span.{u, v, w} A B}
    {r : Span.{u, v, w'} A B} (e : Iso q r) (h : r.JointlyInjective) :
    q.JointlyInjective := by
  intro l m he
  apply e.equiv.injective
  apply h
  apply Prod.ext
  · exact (e.source_eq l).trans ((congrArg Prod.fst he).trans (e.source_eq m).symm)
  · exact (e.target_eq l).trans ((congrArg Prod.snd he).trans (e.target_eq m).symm)

-- [proof->req~span-set-valuedness~1]
theorem jointlyInjective_iff_iso_relation (q : Span.{u, v, w} A B) :
    q.JointlyInjective ↔ Nonempty (Iso q (ofRelation q.red)) := by
  constructor
  · intro h
    exact ⟨q.relationIso h⟩
  · rintro ⟨e⟩
    exact jointlyInjective_of_iso e (ofRelation_jointlyInjective q.red)

-- [proof->req~span-relation-composition~1]
/-- Adopted Q1 correction: no injectivity, finiteness or decidability assumptions. -/
theorem red_comp (q : Span.{u, v, w} A B) (r : Span.{v, z, w'} B C) :
    (q.comp r).red = relationComp q.red r.red := by
  funext a c
  apply propext
  constructor
  · rintro ⟨⟨⟨l, m⟩, h⟩, hs, ht⟩
    exact ⟨q.target l, ⟨l, hs, rfl⟩, ⟨m, h.symm, ht⟩⟩
  · rintro ⟨b, ⟨l, hs, ht⟩, ⟨m, hs', ht'⟩⟩
    exact ⟨⟨(l, m), ht.trans hs'.symm⟩, hs, ht'⟩

/-- The canonical map for the right-hand relation in `red_comp`. -/
def compToRelation (q : Span.{u, v, w} A B) (r : Span.{v, z, w'} B C)
    (p : (q.comp r).Link) : (ofRelation (relationComp q.red r.red)).Link :=
  ⟨(q.source p.1.1, r.target p.1.2),
    q.target p.1.1, ⟨p.1.1, rfl, rfl⟩, ⟨p.1.2, p.2.symm, rfl⟩⟩

theorem compToRelation_surjective (q : Span.{u, v, w} A B)
    (r : Span.{v, z, w'} B C) : Function.Surjective (q.compToRelation r) := by
  rintro ⟨⟨a, c⟩, b, ⟨l, hs, ht⟩, ⟨m, hs', ht'⟩⟩
  refine ⟨⟨(l, m), ht.trans hs'.symm⟩, Subtype.ext ?_⟩
  exact Prod.ext hs ht'

/-- Precisely the injectivity of `(l,m) ↦ (sq l,tr m)` is additionally needed. -/
noncomputable def compRelationIso (q : Span.{u, v, w} A B)
    (r : Span.{v, z, w'} B C) (h : (q.comp r).JointlyInjective) :
    Iso (q.comp r) (ofRelation (relationComp q.red r.red)) where
  equiv := Equiv.ofBijective (q.compToRelation r)
    ⟨fun _ _ he => h (congrArg Subtype.val he), q.compToRelation_surjective r⟩
  source_eq _ := rfl
  target_eq _ := rfl

theorem comp_iso_relation_iff (q : Span.{u, v, w} A B)
    (r : Span.{v, z, w'} B C) :
    Nonempty (Iso (q.comp r) (ofRelation (relationComp q.red r.red))) ↔
      (q.comp r).JointlyInjective := by
  constructor
  · rintro ⟨e⟩
    exact jointlyInjective_of_iso e (ofRelation_jointlyInjective _)
  · intro h
    exact ⟨q.compRelationIso r h⟩

/-- For spans with injective endpoint pairings, only the intermediate object can vary. -/
theorem comp_jointlyInjective_iff_uniqueIntermediate
    (q : Span.{u, v, w} A B) (r : Span.{v, z, w'} B C)
    (hq : q.JointlyInjective) (hr : r.JointlyInjective) :
    (q.comp r).JointlyInjective ↔ UniqueIntermediate q.red r.red := by
  constructor
  · intro h a c b b' hab hbc hab' hb'c
    rcases hab with ⟨l, hs, ht⟩
    rcases hbc with ⟨m, hs', ht'⟩
    rcases hab' with ⟨l', hls, hlt⟩
    rcases hb'c with ⟨m', hms, hmt⟩
    have he : (⟨(l, m), ht.trans hs'.symm⟩ : (q.comp r).Link) =
        ⟨(l', m'), hlt.trans hms.symm⟩ :=
      h (Prod.ext (hs.trans hls.symm) (ht'.trans hmt.symm))
    exact ht.symm.trans ((congrArg (fun p => q.target p.1.1) he).trans hlt)
  · intro h p p' he
    have hs : q.source p.1.1 = q.source p'.1.1 := congrArg Prod.fst he
    have ht : r.target p.1.2 = r.target p'.1.2 := congrArg Prod.snd he
    have hb : q.target p.1.1 = q.target p'.1.1 := h
      ⟨p.1.1, rfl, rfl⟩ ⟨p.1.2, p.2.symm, rfl⟩
      ⟨p'.1.1, hs.symm, rfl⟩ ⟨p'.1.2, p'.2.symm, ht.symm⟩
    apply Subtype.ext
    exact Prod.ext (hq (Prod.ext hs hb))
      (hr (Prod.ext (p.2.symm.trans (hb.trans p'.2)) ht))

/-- The specialization to the canonical relation spans. -/
theorem relations_comp_jointlyInjective_iff (R : A → B → Prop) (S : B → C → Prop) :
    ((ofRelation R).comp (ofRelation S)).JointlyInjective ↔ UniqueIntermediate R S := by
  simpa only [red_ofRelation] using
    comp_jointlyInjective_iff_uniqueIntermediate (ofRelation R) (ofRelation S)
      (ofRelation_jointlyInjective R) (ofRelation_jointlyInjective S)

end Span

theorem uniqueIntermediate_of_singleValued {A : Type u} {B : Type v} {C : Type z}
    {R : A → B → Prop} {S : B → C → Prop} (h : SingleValued R) :
    UniqueIntermediate R S := by
  intro a c b b' hab _ hab' _
  exact h hab hab'

theorem uniqueIntermediate_of_converse_singleValued
    {A : Type u} {B : Type v} {C : Type z}
    {R : A → B → Prop} {S : B → C → Prop} (h : SingleValued (fun c b => S b c)) :
    UniqueIntermediate R S := by
  intro a c b b' _ hbc _ hb'c
  exact h hbc hb'c

namespace Span

variable {A : Type u} {B : Type v} {C : Type z}

theorem relations_comp_injective_of_first_singleValued
    (R : A → B → Prop) (S : B → C → Prop) (h : SingleValued R) :
    ((ofRelation R).comp (ofRelation S)).JointlyInjective :=
  (relations_comp_jointlyInjective_iff R S).mpr (uniqueIntermediate_of_singleValued h)

theorem relations_comp_injective_of_converse_second_singleValued
    (R : A → B → Prop) (S : B → C → Prop) (h : SingleValued (fun c b => S b c)) :
    ((ofRelation R).comp (ofRelation S)).JointlyInjective :=
  (relations_comp_jointlyInjective_iff R S).mpr
    (uniqueIntermediate_of_converse_singleValued h)

end Span
end DPGraph
