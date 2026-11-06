module

public import DPGraph.Predicates.Relational

/-!
[impl->req~reusable-span-laws~1]
[proof->req~reusable-span-laws~1]
-/

/-! # Ambient navigation and relational reduction

SoSyM Appendix 2 mapping reduction and composition (accepted Q1), Table 3,
and Appendix 4 navigation. Reduction is existential; the source spans retain
all original links. Singleton images require single-valued/total link fibers.
-/

@[expose] public section
universe u w
namespace DPGraph.Predicates

/-- Relational image of ambient objects, retaining witnesses of traversed links.
Duplicate links to one object do not become distinct elements of a set. -/
def navigationImage {U : Type u} {A B : Set U}
    (q : DPGraph.Span.{u,u,max u w} A B) (values : Set U) : Set U :=
  {y | ∃ l, (q.source l).val ∈ values ∧ (q.target l).val = y}

@[simp] theorem navigationImage_empty {U : Type u} {A B : Set U}
    (q : DPGraph.Span.{u,u,max u w} A B) : navigationImage q ∅ = ∅ := by
  ext y
  simp [navigationImage]

theorem navigationImage_subset {U : Type u} {A B : Set U}
    (q : DPGraph.Span.{u,u,max u w} A B) (values : Set U) :
    navigationImage q values ⊆ B := by
  rintro y ⟨l, _, rfl⟩
  exact (q.target l).property

theorem navigationImage_singleton {U : Type u} {A B : Set U}
    (q : DPGraph.Span.{u,u,max u w} A B) (hs : SingleValued q) (l : q.Link) :
    navigationImage q {(q.source l).val} = {(q.target l).val} := by
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    have he : q.source k = q.source l := Subtype.ext (Set.mem_singleton_iff.mp hk)
    rw [hs he]
    exact Set.mem_singleton _
  · intro hy
    exact ⟨l, Set.mem_singleton _, (Set.mem_singleton_iff.mp hy).symm⟩

/-- 1..1 link multiplicity implies singleton object image, rather than assuming it. -/
theorem navigationImage_one {U : Type u} {A B : Set U}
    (q : DPGraph.Span.{u,u,max u w} A B)
    (hq : TargetMultiplicity (⟨1, .finite 1⟩ : Range) q) (a : A) :
    ∃ b : B, navigationImage q {a.val} = {b.val} := by
  obtain ⟨ht, hs⟩ := (one_iff_total_single q).mp hq
  obtain ⟨l, hl⟩ := ht a
  exact ⟨q.target l, hl ▸ navigationImage_singleton q hs l⟩

/-- The ordinary functional reference discipline supplies the required 1..1. -/
theorem function_one {A B : Type u} (f : A → B) :
    TargetMultiplicity (⟨1, .finite 1⟩ : Range) (DPGraph.Span.ofFunction f) := by
  intro a
  refine ⟨⟨⟨fun _ => ⟨a, rfl⟩, fun _ _ _ => Subsingleton.elim _ _⟩⟩,
    ⟨⟨fun _ => 0, ?_⟩⟩⟩
  intro x y _
  exact Subtype.ext (x.property.trans y.property.symm)

theorem navigationImage_function {U : Type u} {A B : Set U} (f : A → B) (a : A) :
    navigationImage.{u,0} (DPGraph.Span.ofFunction f) {a.val} = {(f a).val} :=
  navigationImage_singleton.{u,0} (DPGraph.Span.ofFunction f) Function.injective_id a

/-- Existential reduction is explicit; the original span and its links remain
available in the model. Parallel links never become extra relation tuples. -/
def ambientRelation {U : Type u} {A B : Set U}
    (q : DPGraph.Span.{u,u,max u w} A B) : Set (U × U) :=
  {p | ∃ l, (q.source l).val = p.1 ∧ (q.target l).val = p.2}

def relationalImage {U : Type u} (A : Set U) (R : Set (U × U)) : Set U :=
  {y | ∃ x, x ∈ A ∧ (x,y) ∈ R}

def relationalJoin {U : Type u} (R S : Set (U × U)) : Set (U × U) :=
  {p | ∃ y, (p.1,y) ∈ R ∧ (y,p.2) ∈ S}

theorem image_span {U : Type u} {A B : Set U}
    (q : DPGraph.Span.{u,u,max u w} A B) (S : Set U) :
    relationalImage S (ambientRelation q) = navigationImage q S := by
  ext y
  constructor
  · rintro ⟨x,hx,l,hs,ht⟩
    exact ⟨l, hs.symm ▸ hx, ht⟩
  · rintro ⟨l,hs,ht⟩
    exact ⟨(q.source l).val, hs, l, rfl, ht⟩

/-- Q1: reduce only after constructing the composable pair of original links. -/
theorem join_span {U : Type u} {A B C : Set U}
    (q : DPGraph.Span.{u,u,max u w} A B)
    (r : DPGraph.Span.{u,u,max u w} B C) :
    relationalJoin (ambientRelation q) (ambientRelation r) = ambientRelation (q.comp r) := by
  ext p
  constructor
  · rintro ⟨y,⟨l,hs,ht⟩,⟨k,ks,kt⟩⟩
    exact ⟨⟨(l,k), Subtype.ext (ht.trans ks.symm)⟩,hs,kt⟩
  · rintro ⟨l,hs,ht⟩
    exact ⟨(q.target l.val.1).val, ⟨l.val.1,hs,rfl⟩,
      ⟨l.val.2,(congrArg Subtype.val l.property).symm,ht⟩⟩

/-- Relabeling links keeps the same reduced relation while preserving the
original bijection for clients which count links. -/
theorem ambientRelation_iso {U : Type u} {A B : Set U}
    {q r : DPGraph.Span.{u,u,max u w} A B} (h : DPGraph.Span.Iso q r) :
    ambientRelation q = ambientRelation r := by
  ext p
  constructor
  · rintro ⟨l,hs,ht⟩
    exact ⟨h.equiv l, (congrArg Subtype.val (h.source_eq l)).trans hs,
      (congrArg Subtype.val (h.target_eq l)).trans ht⟩
  · rintro ⟨l,hs,ht⟩
    exact ⟨h.equiv.symm l, (congrArg Subtype.val (h.symm.source_eq l)).trans hs,
      (congrArg Subtype.val (h.symm.target_eq l)).trans ht⟩

end DPGraph.Predicates
