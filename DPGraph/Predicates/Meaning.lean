module

public import DPGraph.Predicates.Signature
public import DPGraph.Span
public import Mathlib.Data.Fintype.Basic

/-!
[impl->req~predicate-commutation~1]
[impl->req~predicate-cover~1]
[impl->req~predicate-disjointness~1]
[impl->req~predicate-inverse~1]
[impl->req~predicate-key~1]
[impl->req~predicate-multiplicity~1]
[impl->req~predicate-unary-maps~1]
[proof->req~predicate-commutation~1]
[proof->req~predicate-cover~1]
[proof->req~predicate-disjointness~1]
[proof->req~predicate-inverse~1]
[proof->req~predicate-key~1]
[proof->req~predicate-multiplicity~1]
[proof->req~predicate-unary-maps~1]
-/

/-!
# Link-sensitive predicate meanings

SoSyM Table 3 (PDF p.13), §6.1.1–2/Figure 21 (PDF pp.18–20), A.1 and B.1–3
(PDF pp.28–30), interpreted with B.1 link-renaming equivalence and accepted Q1/Q8.
Endpoints stay fixed under the invariance theorems. No predicate assumes finite
objects or links; only the family arity and finite range bounds use natural numbers.
-/

@[expose] public section

universe u v z w w' w'' w₁ w₂ w₃

namespace DPGraph.Predicates

variable {A : Type u} {B : Type v} {C : Type z}

/-- Opposite maps agree after leg swapping, not categorical inversion. -/
def Inverse (q : Span.{u,v,w} A B) (r : Span.{v,u,w'} B A) : Prop :=
  Nonempty (Span.Iso q.inverse r)

/-- Every composable link pair is retained (accepted Q1). -/
def Commutation (q : Span.{u,v,w} A B) (r : Span.{v,z,w'} B C)
    (s : Span.{u,z,w''} A C) : Prop := Nonempty (Span.Iso (q.comp r) s)

/-- Equality of output bags, including repeated target values. -/
structure BagEquiv (q : Span.{u,v,w} A B) (a a' : A) where
  equiv : q.toFamily.Index a ≃ q.toFamily.Index a'
  target_eq : ∀ l, q.target (equiv l).1 = q.target l.1

def Key {n : Nat} {B : Fin n → Type v} (q : ∀ i, Span.{u,v,w} A (B i)) : Prop :=
  ∀ a a', (∀ i, Nonempty (BagEquiv (q i) a a')) → a = a'

def Cover {n : Nat} {A : Fin n → Type u} (q : ∀ i, Span.{u,v,w} (A i) B) : Prop :=
  ∀ b, ∃ i, ∃ l : (q i).Link, (q i).target l = b

/-- Accepted Q8: different members have disjoint images in the common target. -/
def Disjoint {n : Nat} {A : Fin n → Type u} (q : ∀ i, Span.{u,v,w} (A i) B) : Prop :=
  ∀ i j, i ≠ j → ∀ (l : (q i).Link) (m : (q j).Link), (q i).target l ≠ (q j).target m

def SetValued (q : Span.{u,v,w} A B) : Prop := q.JointlyInjective
def Total (q : Span.{u,v,w} A B) : Prop := Function.Surjective q.source
def SingleValued (q : Span.{u,v,w} A B) : Prop := Function.Injective q.source

/-- Inclusion fixes ambient objects, even across distinct subset memberships. -/
def Inclusion {U : Type u} {A B : Set U} (q : Span.{u,u,w} A B) : Prop :=
  Function.Bijective q.source ∧ ∀ l, (q.target l).val = (q.source l).val

/-- Cardinal bounds on a type, without assigning zero cardinality to infinity. -/
def InRange (range : Range) (F : Type w) : Prop :=
  Nonempty (Fin range.lower ↪ F) ∧ match range.upper with
    | .finite n => Nonempty (F ↪ Fin n)
    | .unbounded => True

def TargetMultiplicity (range : Range) (q : Span.{u,v,w} A B) : Prop :=
  ∀ a, InRange range (q.toFamily.Index a)

def SourceMultiplicity (range : Range) (q : Span.{u,v,w} A B) : Prop :=
  TargetMultiplicity range q.inverse

theorem inverse_symmetry (q : Span.{u,v,w} A B) (r : Span.{v,u,w'} B A) :
    Inverse q r ↔ Inverse r q :=
  ⟨fun ⟨e⟩ => ⟨e.inverse.symm⟩, fun ⟨e⟩ => ⟨e.inverse.symm⟩⟩

theorem inverse_iff {q : Span.{u,v,w} A B} {q' : Span.{u,v,w₁} A B}
    {r : Span.{v,u,w'} B A} {r' : Span.{v,u,w₂} B A}
    (e : Span.Iso q q') (f : Span.Iso r r') : Inverse q r ↔ Inverse q' r' :=
  ⟨fun ⟨h⟩ => ⟨e.inverse.symm.trans (h.trans f)⟩,
   fun ⟨h⟩ => ⟨e.inverse.trans (h.trans f.symm)⟩⟩

theorem commutation_iff {q : Span.{u,v,w} A B} {q' : Span.{u,v,w₁} A B}
    {r : Span.{v,z,w'} B C} {r' : Span.{v,z,w₂} B C}
    {s : Span.{u,z,w''} A C} {s' : Span.{u,z,w₃} A C}
    (e : Span.Iso q q') (f : Span.Iso r r') (g : Span.Iso s s') :
    Commutation q r s ↔ Commutation q' r' s' :=
  ⟨fun ⟨h⟩ => ⟨(e.comp f).symm.trans (h.trans g)⟩,
   fun ⟨h⟩ => ⟨(e.comp f).trans (h.trans g.symm)⟩⟩

def BagEquiv.transport {q : Span.{u,v,w} A B} {r : Span.{u,v,w'} A B}
    (e : Span.Iso q r) {a a' : A} (h : BagEquiv q a a') : BagEquiv r a a' where
  equiv := (e.symm.fiberEquiv a).trans (h.equiv.trans (e.fiberEquiv a'))
  target_eq l := by
    change r.target (e.fiberEquiv a' (h.equiv (e.symm.fiberEquiv a l))).val = _
    rw [e.fiberEquiv_target, h.target_eq, e.symm.fiberEquiv_target]

theorem key_iff {n : Nat} {B : Fin n → Type v}
    {q : ∀ i, Span.{u,v,w} A (B i)} {r : ∀ i, Span.{u,v,w'} A (B i)}
    (e : ∀ i, Span.Iso (q i) (r i)) : Key q ↔ Key r := by
  constructor
  · intro h a a' hh
    exact h a a' (fun i => (hh i).map (BagEquiv.transport (e i).symm))
  · intro h a a' hh
    exact h a a' (fun i => (hh i).map (BagEquiv.transport (e i)))

theorem cover_iff {n : Nat} {A : Fin n → Type u}
    {q : ∀ i, Span.{u,v,w} (A i) B} {r : ∀ i, Span.{u,v,w'} (A i) B}
    (e : ∀ i, Span.Iso (q i) (r i)) : Cover q ↔ Cover r := by
  constructor
  · intro h b
    obtain ⟨i, l, hl⟩ := h b
    exact ⟨i, (e i).equiv l, ((e i).target_eq l).trans hl⟩
  · intro h b
    obtain ⟨i, l, hl⟩ := h b
    exact ⟨i, (e i).equiv.symm l, ((e i).symm.target_eq l).trans hl⟩

theorem disjoint_iff {n : Nat} {A : Fin n → Type u}
    {q : ∀ i, Span.{u,v,w} (A i) B} {r : ∀ i, Span.{u,v,w'} (A i) B}
    (e : ∀ i, Span.Iso (q i) (r i)) : Disjoint q ↔ Disjoint r := by
  constructor
  · intro h i j hij l m he
    apply h i j hij ((e i).equiv.symm l) ((e j).equiv.symm m)
    exact ((e i).symm.target_eq l).trans (he.trans ((e j).symm.target_eq m).symm)
  · intro h i j hij l m he
    apply h i j hij ((e i).equiv l) ((e j).equiv m)
    exact ((e i).target_eq l).trans (he.trans ((e j).target_eq m).symm)

theorem setValued_iff {q : Span.{u,v,w} A B} {r : Span.{u,v,w'} A B}
    (e : Span.Iso q r) : SetValued q ↔ SetValued r :=
  ⟨Span.jointlyInjective_of_iso e.symm, Span.jointlyInjective_of_iso e⟩

theorem total_fibers (q : Span.{u,v,w} A B) :
    Total q ↔ ∀ a, Nonempty (q.toFamily.Index a) := by
  constructor
  · intro h a; obtain ⟨l, hl⟩ := h a; exact ⟨⟨l, hl⟩⟩
  · intro h a; obtain ⟨l, hl⟩ := h a; exact ⟨l, hl⟩

theorem singleValued_fibers (q : Span.{u,v,w} A B) :
    SingleValued q ↔ ∀ a, Subsingleton (q.toFamily.Index a) := by
  constructor
  · intro h a; exact ⟨fun l m => Subtype.ext (h (l.2.trans m.2.symm))⟩
  · intro h l m he
    exact congrArg Subtype.val (@Subsingleton.elim _ (h (q.source l)) ⟨l, rfl⟩ ⟨m, he.symm⟩)

theorem total_iff {q : Span.{u,v,w} A B} {r : Span.{u,v,w'} A B}
    (e : Span.Iso q r) : Total q ↔ Total r := by
  rw [total_fibers, total_fibers]
  exact forall_congr' (fun a => ⟨fun h => h.map (e.fiberEquiv a),
    fun h => h.map (e.symm.fiberEquiv a)⟩)

theorem singleValued_iff {q : Span.{u,v,w} A B} {r : Span.{u,v,w'} A B}
    (e : Span.Iso q r) : SingleValued q ↔ SingleValued r := by
  rw [singleValued_fibers, singleValued_fibers]
  apply forall_congr'
  intro a
  exact ⟨fun h => ⟨fun l m => (e.symm.fiberEquiv a).injective (@Subsingleton.elim _ h _ _)⟩,
    fun h => ⟨fun l m => (e.fiberEquiv a).injective (@Subsingleton.elim _ h _ _)⟩⟩

theorem singleValued_setValued {q : Span.{u,v,w} A B} (h : SingleValued q) :
    SetValued q := fun _ _ he => h (congrArg Prod.fst he)

theorem setValued_characterization (q : Span.{u,v,w} A B) :
    SetValued q ↔ Nonempty (Span.Iso q (Span.ofRelation q.red)) :=
  q.jointlyInjective_iff_iso_relation

theorem inclusion_iff {U : Type u} {A B : Set U}
    {q : Span.{u,u,w} A B} {r : Span.{u,u,w'} A B} (e : Span.Iso q r) :
    Inclusion q ↔ Inclusion r := by
  have forward : ∀ {q : Span.{u,u,w} A B} {r : Span.{u,u,w'} A B},
      Span.Iso q r → Inclusion q → Inclusion r := by
    intro q r e h
    refine ⟨⟨(singleValued_iff e).mp h.1.1, (total_iff e).mp h.1.2⟩, ?_⟩
    intro l
    exact (congrArg Subtype.val (e.symm.target_eq l)).symm.trans
      ((h.2 _).trans (congrArg Subtype.val (e.symm.source_eq l)))
  exact ⟨forward e, fun h => by
    refine ⟨⟨(singleValued_iff e).mpr h.1.1, (total_iff e).mpr h.1.2⟩, ?_⟩
    intro l
    simpa only [e.target_eq, e.source_eq] using h.2 (e.equiv l)⟩

theorem inclusion_subset {U : Type u} {A B : Set U} {q : Span.{u,u,w} A B}
    (h : Inclusion q) : A ⊆ B := by
  intro a ha
  obtain ⟨l, hl⟩ := h.1.2 ⟨a, ha⟩
  have he : (q.target l).val = a := (h.2 l).trans (congrArg Subtype.val hl)
  exact he ▸ (q.target l).property

/-- The unique link at a has exactly a's underlying object as target. -/
theorem inclusion_identity {U : Type u} {A B : Set U} {q : Span.{u,u,w} A B}
    (h : Inclusion q) (a : A) : ∃! l, q.source l = a ∧ (q.target l).val = a.val := by
  obtain ⟨l, hl⟩ := h.1.2 a
  exact ⟨l, ⟨hl, (h.2 l).trans (congrArg Subtype.val hl)⟩,
    fun m hm => h.1.1 (hm.1.trans hl.symm)⟩

theorem inRange_iff (range : Range) {F : Type w} {G : Type w'} (e : F ≃ G) :
    InRange range F ↔ InRange range G := by
  constructor
  · rintro ⟨⟨lo⟩, hi⟩
    refine ⟨⟨lo.trans e.toEmbedding⟩, ?_⟩
    cases hu : range.upper with
    | unbounded => trivial
    | finite n =>
      simp only [hu] at hi ⊢
      obtain ⟨hi⟩ := hi
      exact ⟨e.symm.toEmbedding.trans hi⟩
  · rintro ⟨⟨lo⟩, hi⟩
    refine ⟨⟨lo.trans e.symm.toEmbedding⟩, ?_⟩
    cases hu : range.upper with
    | unbounded => trivial
    | finite n =>
      simp only [hu] at hi ⊢
      obtain ⟨hi⟩ := hi
      exact ⟨e.toEmbedding.trans hi⟩

theorem targetMultiplicity_iff (range : Range)
    {q : Span.{u,v,w} A B} {r : Span.{u,v,w'} A B} (e : Span.Iso q r) :
    TargetMultiplicity range q ↔ TargetMultiplicity range r :=
  forall_congr' (fun a => inRange_iff range (e.fiberEquiv a))

theorem sourceMultiplicity_iff (range : Range)
    {q : Span.{u,v,w} A B} {r : Span.{u,v,w'} A B} (e : Span.Iso q r) :
    SourceMultiplicity range q ↔ SourceMultiplicity range r :=
  targetMultiplicity_iff range e.inverse

theorem source_target_duality (range : Range) (q : Span.{u,v,w} A B) :
    SourceMultiplicity range q ↔ TargetMultiplicity range q.inverse := Iff.rfl

theorem target_source_duality (range : Range) (q : Span.{u,v,w} A B) :
    TargetMultiplicity range q ↔ SourceMultiplicity range q.inverse := Iff.rfl

/-- Under set-valuedness each link is uniquely identified by its target in a fiber. -/
noncomputable def distinctValuesEquiv (q : Span.{u,v,w} A B) (h : SetValued q) (a : A) :
    q.toFamily.Index a ≃ {b : B // q.red a b} :=
  Equiv.ofBijective (fun l => ⟨q.target l.1, ⟨l.1, l.2, rfl⟩⟩)
    ⟨fun l m he => (q.jointlyInjective_iff_fiberwise.mp h a) (congrArg Subtype.val he), by
      rintro ⟨b, l, hs, ht⟩
      exact ⟨⟨l, hs⟩, Subtype.ext ht⟩⟩

theorem targetMultiplicity_distinct (range : Range) (q : Span.{u,v,w} A B)
    (h : SetValued q) : TargetMultiplicity range q ↔
      ∀ a, InRange range {b : B // q.red a b} :=
  forall_congr' (fun a => inRange_iff range (distinctValuesEquiv q h a))

theorem setValued_fibers (q : Span.{u,v,w} A B) :
    SetValued q ↔ ∀ a, Function.Injective (q.toFamily.eval a) :=
  q.jointlyInjective_iff_fiberwise

theorem setValued_inverse (q : Span.{u,v,w} A B) :
    SetValued q.inverse ↔ SetValued q := by
  constructor <;> intro h l m he <;> exact h (congrArg Prod.swap he)

theorem sourceMultiplicity_distinct (range : Range) (q : Span.{u,v,w} A B)
    (h : SetValued q) : SourceMultiplicity range q ↔
      ∀ b, InRange range {a : A // q.inverse.red b a} :=
  targetMultiplicity_distinct range q.inverse ((setValued_inverse q).mpr h)

theorem key_zero {B : Fin 0 → Type v} (q : ∀ i, Span.{u,v,w} A (B i)) :
    Key q ↔ Subsingleton A :=
  ⟨fun h => ⟨fun a a' => h a a' (fun i => Fin.elim0 i)⟩,
    fun h _ _ _ => @Subsingleton.elim _ h _ _⟩

theorem cover_zero {A : Fin 0 → Type u} (q : ∀ i, Span.{u,v,w} (A i) B) :
    Cover q ↔ IsEmpty B :=
  ⟨fun h => ⟨fun b => by obtain ⟨i, _⟩ := h b; exact Fin.elim0 i⟩,
    fun h b => (h.false b).elim⟩

theorem disjoint_zero {A : Fin 0 → Type u} (q : ∀ i, Span.{u,v,w} (A i) B) :
    Disjoint q := fun i => Fin.elim0 i

end DPGraph.Predicates
