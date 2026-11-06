module

public import Clafer.Constraints.DenotationLaws

/-! # Typed collection meaning and local cardinality obligations

SoSyM D.3–D.4. Collections have total set meanings even when their extents
are infinite. Finiteness is derived locally for a counted typed collection;
integer extraction retains its independent singleton obligation.
-/

@[expose] public section
universe u w
namespace Clafer.Constraints

def Collection.Typed {s : Support} {U : Type u} (m : IntegerBinding.{u,w} s U)
    (k : Collection s) : Set (k.Carrier U) → Prop :=
  match k with
  | .objects x => fun S => S ⊆ (m.model.obj x : Set U)
  | .relation x y => fun S => ∀ p ∈ S,
      (m.model.obj x : Set U) p.1 ∧ (m.model.obj y : Set U) p.2

private def CollectionResult {s : Support} {U : Type u} (m : IntegerBinding.{u,w} s U) :
    (t : Ty s) → Option (Value U t) → Prop
  | .boolean, _ => True
  | .integer, _ => True
  | .collection k, r => ∃ S, r = Option.some S ∧ k.Typed m S

/-- Every collection constructor denotes a set of objects/tuples of its
intrinsic type. Structural admissibility concerns model and variable membership,
not the success of an evaluator. -/
private theorem collection_result {s : Support} {U : Type u}
    (m : IntegerBinding.{u,w} s U) {Γ t} (e : Expr s Γ t)
    (ρ : Environment s U Γ) (hρ : ρ.Admissible m) :
    CollectionResult m t (e.denote m ρ) := by
  induction e with
  | empty k =>
    refine ⟨∅, rfl, ?_⟩
    cases k <;> simp [Collection.Typed]
  | this => exact ⟨{ρ.this},rfl,by intro x hx; cases Set.mem_singleton_iff.mp hx; exact hρ.1⟩
  | extent x => exact ⟨m.model.obj x,rfl,Set.Subset.refl _⟩
  | var v => exact ⟨{ρ.lookup v},rfl,by intro x hx; cases Set.mem_singleton_iff.mp hx; exact hρ.2 _ v⟩
  | map f =>
    refine ⟨ambientRelation (m.model.map (s.arrow f)),rfl,?_⟩
    rintro p ⟨l,hs,ht⟩
    exact ⟨hs ▸ ((m.model.map (s.arrow f)).source l).property,
      ht ▸ ((m.model.map (s.arrow f)).target l).property⟩
  | @setOp Γ k op a b iha ihb =>
    obtain ⟨A,ha,hA⟩ := iha ρ hρ
    obtain ⟨B,hb,hB⟩ := ihb ρ hρ
    refine ⟨collectionOp op A B,by simp [Expr.denote,lift₂,ha,hb],?_⟩
    cases k <;> cases op
    all_goals simp only [Collection.Typed,collectionOp] at hA hB ⊢
    · exact Set.union_subset hA hB
    · exact Set.Subset.trans Set.sdiff_subset hA
    · exact Set.Subset.trans Set.inter_subset_left hA
    · intro p hp; rcases hp with ha | hb; exact hA p ha; exact hB p hb
    · intro p hp; exact hA p hp.1
    · intro p hp; exact hA p hp.1
  | image a b iha ihb =>
    obtain ⟨A,ha,hA⟩ := iha ρ hρ
    obtain ⟨B,hb,hB⟩ := ihb ρ hρ
    refine ⟨relationalImage A B,by simp [Expr.denote,lift₂,ha,hb],?_⟩
    rintro y ⟨x,_,hxy⟩
    exact (hB (x,y) hxy).2
  | join a b iha ihb =>
    obtain ⟨A,ha,hA⟩ := iha ρ hρ
    obtain ⟨B,hb,hB⟩ := ihb ρ hρ
    refine ⟨relationalJoin A B,by simp [Expr.denote,lift₂,ha,hb],?_⟩
    rintro p ⟨y,hy,hz⟩
    exact ⟨(hA (p.1,y) hy).1,(hB (y,p.2) hz).2⟩
  | widenObjects h a iha =>
    obtain ⟨A,ha,hA⟩ := iha ρ hρ
    exact ⟨A,ha,hA.trans (m.widen_subset h)⟩
  | widenRelation h k a iha =>
    obtain ⟨A,ha,hA⟩ := iha ρ hρ
    refine ⟨A,ha,?_⟩
    intro p hp
    exact ⟨m.widen_subset h (hA p hp).1,m.widen_subset k (hA p hp).2⟩
  | _ => trivial

theorem Expr.collection_meaning {s : Support} {U : Type u}
    (m : IntegerBinding.{u,w} s U) {Γ k} (e : Expr s Γ (.collection k))
    (ρ : Environment s U Γ) (hρ : ρ.Admissible m) :
    ∃ S, e.denote m ρ = Option.some S ∧ k.Typed m S :=
  collection_result m e ρ hρ

/-- Finiteness of the selected result's class suffices for cardinality.
No finiteness of unrelated classes or the ambient universe is needed. -/
theorem Expr.cardinality_objects_defined {s : Support} {U : Type u}
    (m : IntegerBinding.{u,w} s U) {Γ x} (e : Expr s Γ (.collection (.objects x)))
    (ρ : Environment s U Γ) (hρ : ρ.Admissible m)
    (hf : (m.model.obj x : Set U).Finite) :
    (Expr.cardinality e).Defined m ρ := by
  obtain ⟨S,hS,ht⟩ := e.collection_meaning m ρ hρ
  refine ⟨⟨(S.ncard : Int)⟩,?_⟩
  simp [Expr.denote,hS,finiteCard_finite S (hf.subset ht)]

/-- Binary cardinality uses a finite product of just its endpoint extents. -/
theorem Expr.cardinality_relation_defined {s : Support} {U : Type u}
    (m : IntegerBinding.{u,w} s U) {Γ x y}
    (e : Expr s Γ (.collection (.relation x y)))
    (ρ : Environment s U Γ) (hρ : ρ.Admissible m)
    (hx : (m.model.obj x : Set U).Finite) (hy : (m.model.obj y : Set U).Finite) :
    (Expr.cardinality e).Defined m ρ := by
  obtain ⟨S,hS,ht⟩ := e.collection_meaning m ρ hρ
  have hf : S.Finite := (hx.prod hy).subset ht
  exact ⟨⟨(S.ncard : Int)⟩,by simp [Expr.denote,hS,finiteCard_finite S hf]⟩

/-- Typed membership supplies the primitive-domain half of singleton extraction.
The singleton obligation is still substantive, and is derived from the source
map bounds for Appendix 6 by VersionNavigation.denotation_defined. -/
theorem Expr.integerOf_singleton_defined {s : Support} {U : Type u}
    (m : IntegerBinding.{u,w} s U) {Γ x}
    (e : Expr s Γ (.collection (.objects x))) (primitive : s.integer x = true)
    (ρ : Environment s U Γ) (hρ : ρ.Admissible m)
    (S : Set U) (hS : e.denote m ρ = Option.some S) (one : S.ncard = 1) :
    (Expr.integerOf primitive e).Defined m ρ := by
  obtain ⟨T,hT,ht⟩ := e.collection_meaning m ρ hρ
  have he : T = S := Option.some.inj (hT.symm.trans hS)
  subst T
  obtain ⟨a,ha⟩ := Set.ncard_eq_one.mp one
  subst S
  have hd := m.singleton_defined primitive (ht (Set.mem_singleton a))
  exact ⟨⟨m.realization.decode a⟩, by simp [Expr.denote,hS,hd]⟩

/-- Quantified bodies need definedness only at well-typed bound objects.
Admissible domain membership supplies that condition before lexical extension. -/
theorem Expr.all_defined {s : Support} {U : Type u} {Γ}
    (m : IntegerBinding.{u,w} s U) (ρ : Environment s U Γ)
    (hρ : ρ.Admissible m) (b : Local s) (fresh : ∀ old ∈ Γ, old.id ≠ b.id)
    (domain : Expr s Γ (.collection (.objects b.element)))
    (body : Expr s (b :: Γ) .boolean)
    (hb : ∀ x, (m.model.obj b.element : Set U) x →
      body.Defined m (ρ.push b x)) :
    (Expr.all b fresh domain body).Defined m ρ := by
  obtain ⟨S,hS,hT⟩ := domain.collection_meaning m ρ hρ
  refine ⟨⟨∀ x ∈ S, body.denote m (ρ.push b x) = Option.some ⟨True⟩⟩,?_⟩
  simp only [denote_all,hS,Option.bind_some]
  exact universal_defined _ _ (fun x hx => hb x (hT hx))

end Clafer.Constraints
