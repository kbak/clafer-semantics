module

public import DPGraph.Predicates
public import DPGraph.Span.Examples
public import Mathlib.Data.Fintype.EquivFin

/-!
# Checked predicate boundaries

Table 3/A.1/§6.1.1–2 and the accepted Q1/Q8 corrections. These witnesses
exercise actual link types, including repeated targets and an infinite fiber.
Finiteness and decidable equality are local to individual finite examples.
-/

@[expose] public section

namespace DPGraph.Predicates.Examples

open CategoryTheory Arity

/-- Every link has the same endpoints; its type still records multiplicity. -/
def copies (F : Type) : Span Unit Unit where
  Link := F
  source _ := ()
  target _ := ()

def copiesFiber (F : Type) (a : Unit) : (copies F).toFamily.Index a ≃ F where
  toFun := Subtype.val
  invFun l := ⟨l, Subsingleton.elim _ _⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- [impl->req~predicate-examples~1]
def two : Span Unit Unit := copies (Fin 2)
def one : Span Unit Unit := copies (Fin 1)

-- [proof->req~predicate-multiplicity~1]
theorem two_range : TargetMultiplicity ⟨2, .finite 2⟩ two := by
  intro a
  apply (inRange_iff _ (copiesFiber (Fin 2) a)).mpr
  exact ⟨⟨Function.Embedding.refl _⟩, ⟨Function.Embedding.refl _⟩⟩

-- [proof->req~predicate-unary-maps~1]
theorem two_not_setValued : ¬ SetValued two := by
  intro h
  have he : (0 : Fin 2) = 1 := h (show ((), ()) = ((), ()) from rfl)
  exact (by decide : (0 : Fin 2) ≠ 1) he

theorem two_not_singleValued : ¬ SingleValued two :=
  fun h => two_not_setValued (singleValued_setValued h)

theorem one_singleValued : SingleValued one := by
  change Function.Injective (fun _ : Fin 1 => ())
  exact fun _ _ _ => Subsingleton.elim _ _
theorem one_setValued : SetValued one := singleValued_setValued one_singleValued
theorem one_total : Total one := by intro a; cases a; exact ⟨(0 : Fin 1), rfl⟩

theorem copies_finite_range (m k n : Nat) :
    TargetMultiplicity ⟨m, .finite n⟩ (copies (Fin k)) ↔ m ≤ k ∧ k ≤ n := by
  constructor
  · intro h
    obtain ⟨⟨lo⟩, ⟨hi⟩⟩ := (inRange_iff _ (copiesFiber (Fin k) ())).mp (h ())
    exact ⟨by simpa using Fintype.card_le_of_injective lo lo.injective,
      by simpa using Fintype.card_le_of_injective hi hi.injective⟩
  · rintro ⟨hlo, hhi⟩ a
    apply (inRange_iff _ (copiesFiber (Fin k) a)).mpr
    exact ⟨⟨⟨fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hlo⟩,
      fun _ _ h => Fin.ext (congrArg (fun x : Fin k => x.val) h)⟩⟩,
      ⟨⟨fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hhi⟩,
      fun _ _ h => Fin.ext (congrArg (fun x : Fin n => x.val) h)⟩⟩⟩

theorem two_range_wide : TargetMultiplicity ⟨1, .finite 3⟩ two :=
  (copies_finite_range 1 2 3).mpr (by decide)
theorem two_upper_fails : ¬ TargetMultiplicity ⟨0, .finite 1⟩ two := by
  rw [two, copies_finite_range]; decide
theorem two_lower_fails : ¬ TargetMultiplicity ⟨3, .finite 4⟩ two := by
  rw [two, copies_finite_range]; decide
theorem one_not_two : ¬ TargetMultiplicity ⟨2, .finite 2⟩ one := by
  rw [one, copies_finite_range]; decide

theorem empty_range : TargetMultiplicity ⟨0, .finite 0⟩ (copies (Fin 0)) :=
  (copies_finite_range 0 0 0).mpr (by decide)
theorem empty_singleValued : SingleValued (copies (Fin 0)) :=
  fun l => Fin.elim0 l

theorem empty_not_total : ¬ Total (copies (Fin 0)) := by
  intro h; obtain ⟨l, _⟩ := h (); exact Fin.elim0 l

theorem infinite_unbounded (m : Nat) : TargetMultiplicity ⟨m, .unbounded⟩ (copies Nat) := by
  intro a
  apply (inRange_iff _ (copiesFiber Nat a)).mpr
  exact ⟨⟨⟨Fin.val, Fin.val_injective⟩⟩, trivial⟩

theorem infinite_not_finite (m n : Nat) : ¬ TargetMultiplicity ⟨m, .finite n⟩ (copies Nat) := by
  intro h
  obtain ⟨_, ⟨hi⟩⟩ := (inRange_iff _ (copiesFiber Nat ())).mp (h ())
  exact not_injective_infinite_finite hi hi.injective

/-- Outgoing count two, incoming count one. -/
def split : Span Unit Bool where
  Link := Bool
  source _ := ()
  target := id

theorem split_setValued : SetValued split := fun _ _ h => congrArg Prod.snd h

theorem split_not_singleValued : ¬ SingleValued split :=
  fun h => Bool.false_ne_true (h (show split.source false = split.source true from rfl))

theorem split_source_one : SourceMultiplicity ⟨1, .finite 1⟩ split := by
  intro b
  let e : split.inverse.toFamily.Index b ≃ Fin 1 :=
    { toFun := fun _ => 0
      invFun := fun _ => ⟨b, rfl⟩
      left_inv := fun l => Subtype.ext l.2.symm
      right_inv := fun _ => Subsingleton.elim _ _ }
  exact (inRange_iff _ e).mpr ⟨⟨Function.Embedding.refl _⟩, ⟨Function.Embedding.refl _⟩⟩

theorem split_target_not_one : ¬ TargetMultiplicity ⟨1, .finite 1⟩ split := by
  intro h
  obtain ⟨_, ⟨hi⟩⟩ := h ()
  have he := hi.injective (Subsingleton.elim (hi ⟨false, rfl⟩) (hi ⟨true, rfl⟩))
  exact Bool.false_ne_true (congrArg Subtype.val he)

theorem reversal : TargetMultiplicity ⟨1, .finite 1⟩ split.inverse := split_source_one

/-- Relabeling even into a larger universe preserves the actual links. -/
def liftedTwo : Span.{0,0,1} Unit Unit where
  Link := ULift.{1} (Fin 2)
  source _ := ()
  target _ := ()

def twoRelabel : Span.Iso two liftedTwo where
  equiv := Equiv.ulift.symm
  source_eq _ := rfl
  target_eq _ := rfl

-- [proof->req~predicate-inverse~1]
theorem relabeled_inverse : Inverse two liftedTwo.inverse :=
  ⟨twoRelabel.inverse⟩
-- [proof->req~predicate-commutation~1]
theorem relabeled_commutation : Commutation two (Span.identity Unit) liftedTwo :=
  ⟨(Span.rightUnit two).trans twoRelabel⟩
theorem relabeled_range : TargetMultiplicity ⟨2, .finite 2⟩ liftedTwo :=
  (targetMultiplicity_iff _ twoRelabel).mp two_range

/-- Reuse #4's two-path counterexample: equal reductions do not commute. -/
theorem reduction_not_commutation :
    (Span.Examples.first.comp Span.Examples.second).red =
      (Span.ofRelation (relationComp Span.Examples.first.red Span.Examples.second.red)).red ∧
    ¬ Commutation Span.Examples.first Span.Examples.second
      (Span.ofRelation (relationComp Span.Examples.first.red Span.Examples.second.red)) := by
  refine ⟨?_, Span.Examples.two_path_not_iso⟩
  rw [Span.red_ofRelation, Span.red_comp]

/-- false has one copy of (), true has two copies of the same value. -/
def bagKey : Span Bool Unit where
  Link := Option Bool
  source | none => false | some _ => true
  target _ := ()

def falseFiber : bagKey.toFamily.Index false ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨none, rfl⟩
  left_inv := by rintro ⟨l, hl⟩; cases l with
    | none => rfl
    | some b => cases hl
  right_inv _ := rfl

theorem bags_differ : ¬ Nonempty (BagEquiv bagKey false true) := by
  rintro ⟨e⟩
  let f := e.equiv.symm.trans falseFiber
  have he := f.injective (Subsingleton.elim (f ⟨some false, rfl⟩) (f ⟨some true, rfl⟩))
  have hh : some false = some true := congrArg Subtype.val he
  cases hh

-- [proof->req~predicate-key~1]
theorem bagKey_key : Key (fun _ : Fin 1 => bagKey) := by
  intro a a' h
  cases a <;> cases a'
  · rfl
  · exact (bags_differ (h 0)).elim
  · obtain ⟨e⟩ := h 0
    apply False.elim
    apply bags_differ
    exact ⟨⟨e.equiv.symm, fun _ => rfl⟩⟩
  · rfl

theorem bagKey_not_setValued : ¬ SetValued bagKey := by
  intro h
  have he : some false = some true := h (show
    (bagKey.source (some false), bagKey.target (some false)) =
    (bagKey.source (some true), bagKey.target (some true)) from rfl)
  cases he

theorem bagKey_same_support : bagKey.red false = bagKey.red true := by
  funext b
  cases b
  apply propext
  exact ⟨fun _ => ⟨some false, rfl, rfl⟩, fun _ => ⟨none, rfl, rfl⟩⟩

/-- All components of a two-member tuple return the same singleton bag. -/
def constantBag : Span Bool Unit where
  Link := Bool
  source := id
  target _ := ()

def equalBags : BagEquiv constantBag false true where
  equiv :=
    { toFun := fun _ => ⟨true, rfl⟩
      invFun := fun _ => ⟨false, rfl⟩
      left_inv := fun l => Subtype.ext l.2.symm
      right_inv := fun l => Subtype.ext l.2.symm }
  target_eq _ := rfl

theorem equal_tuple_not_key : ¬ Key (fun _ : Fin 2 => constantBag) :=
  fun h => Bool.false_ne_true (h false true (fun _ => ⟨equalBags⟩))

/-- Two singleton images partition Bool. -/
def singletonImage (b : Bool) : Span Unit Bool where
  Link := Unit
  source _ := ()
  target _ := b

def partition (i : Fin 2) : Span Unit Bool := singletonImage (i.val == 1)

-- [proof->req~predicate-cover~1]
theorem partition_cover : Cover partition := by
  intro b
  cases b
  · exact ⟨0, (), rfl⟩
  · exact ⟨1, (), rfl⟩

-- [proof->req~predicate-disjointness~1]
theorem partition_disjoint : Disjoint partition := by
  intro i j hij l m h
  apply hij
  have hi := i.isLt
  have hj := j.isLt
  have hh : (i.val == 1) = (j.val == 1) := h
  apply Fin.ext
  have ci : i.val = 0 ∨ i.val = 1 := by omega
  have cj : j.val = 0 ∨ j.val = 1 := by omega
  rcases ci with hi | hi <;> rcases cj with hj | hj <;> simp_all

/-- Cover/disjointness also accept bags with duplicate links within each member. -/
def bagPartition (i : Fin 2) : Span Unit Bool where
  Link := Fin 2
  source _ := ()
  target _ := (i.val == 1)

theorem bag_partition_cover : Cover bagPartition := by
  intro b; cases b
  · exact ⟨0, (0 : Fin 2), rfl⟩
  · exact ⟨1, (0 : Fin 2), rfl⟩

theorem bag_partition_disjoint : Disjoint bagPartition :=
  fun i j hij _ _ h => partition_disjoint i j hij () () h

theorem bag_partition_not_setValued (i : Fin 2) : ¬ SetValued (bagPartition i) := by
  intro h
  exact (by decide : (0 : Fin 2) ≠ 1) (h (show
    ((bagPartition i).source (0 : Fin 2), (bagPartition i).target (0 : Fin 2)) =
    ((bagPartition i).source (1 : Fin 2), (bagPartition i).target (1 : Fin 2)) from rfl))

theorem repeated_not_cover : ¬ Cover (fun _ : Fin 2 => singletonImage false) := by
  intro h
  obtain ⟨i, l, he⟩ := h true
  exact Bool.false_ne_true he

theorem repeated_not_disjoint : ¬ Disjoint (fun _ : Fin 2 => singletonImage false) := by
  intro h
  exact h 0 1 (by decide) () () rfl

def emptyDomain : Span Empty Bool where
  Link := Empty
  source := id
  target := Empty.elim

theorem empty_domain_disjoint : Disjoint (fun _ : Fin 2 => emptyDomain) :=
  fun _ _ _ l => Empty.elim l

theorem empty_domain_not_cover : ¬ Cover (fun _ : Fin 2 => emptyDomain) := by
  intro h; obtain ⟨_, l, _⟩ := h false; exact Empty.elim l

/-- Inclusion witnesses share ambient objects across distinct subsets. -/
def literal {U : Type u} {A B : Set U} (h : A ⊆ B) : Span.{u,u,u} A B where
  Link := A
  source := id
  target a := ⟨a.val, h a.property⟩

theorem literal_inclusion {U : Type u} {A B : Set U} (h : A ⊆ B) :
    Inclusion (literal h) := ⟨Function.bijective_id, fun _ => rfl⟩

def properInclusion : Span ({false} : Set Bool) (Set.univ : Set Bool) :=
  literal (Set.subset_univ _)

theorem proper_inclusion : Inclusion properInclusion := literal_inclusion _

theorem empty_inclusion : Inclusion (literal (Set.empty_subset (Set.univ : Set Bool))) :=
  literal_inclusion _

def permutation : Span (Set.univ : Set Bool) (Set.univ : Set Bool) where
  Link := {b : Bool // b ∈ (Set.univ : Set Bool)}
  source := id
  target b := ⟨!b.val, trivial⟩

theorem permutation_bijective : Function.Bijective permutation.target := by
  constructor
  · intro a b h
    apply Subtype.ext
    have hh := congrArg (fun b => !b.val) h
    simpa [permutation] using hh
  · intro b; exact ⟨⟨!b.val, trivial⟩, Subtype.ext (Bool.not_not b.val)⟩

theorem permutation_not_inclusion : ¬ Inclusion permutation :=
  fun h => Bool.false_ne_true (h.2 ⟨false, trivial⟩).symm

def duplicatedIdentity : Span (Set.univ : Set Unit) (Set.univ : Set Unit) where
  Link := Bool
  source _ := ⟨(), trivial⟩
  target _ := ⟨(), trivial⟩

theorem duplicate_identity_not_inclusion : ¬ Inclusion duplicatedIdentity :=
  fun h => Bool.false_ne_true (h.1.1 (show duplicatedIdentity.source false =
    duplicatedIdentity.source true from rfl))

-- [proof->req~predicate-arities~1]
/-- Empty-family consequences keep a nonempty, isolated central arity vertex. -/
theorem zero_centers_nonempty : Nonempty (fanOut 0) ∧ Nonempty (fanIn 0) :=
  ⟨fanOut_zero_nonempty, fanIn_zero_nonempty⟩
theorem zero_key_unit : Key (fun i : Fin 0 => Fin.elim0 i : Fin 0 → Span Unit Unit) :=
  (key_zero _).mpr inferInstance
theorem zero_key_bool_fails : ¬ Key (fun i : Fin 0 => Fin.elim0 i : Fin 0 → Span Bool Unit) := by
  intro h
  exact Bool.false_ne_true (@Subsingleton.elim _ ((key_zero _).mp h) false true)
theorem zero_cover_empty : Cover (fun i : Fin 0 => Fin.elim0 i : Fin 0 → Span Unit Empty) :=
  (cover_zero _).mpr inferInstance
theorem zero_cover_unit_fails : ¬ Cover (fun i : Fin 0 => Fin.elim0 i : Fin 0 → Span Unit Unit) :=
  fun h => ((cover_zero _).mp h).false ()
theorem zero_disjoint : Disjoint (fun i : Fin 0 => Fin.elim0 i : Fin 0 → Span Unit Unit) :=
  disjoint_zero _

/-- The empty argument list still binds a nonempty semantic central set. -/
def zeroOutDiagram : fanOut 0 ⥤q semanticGraph Unit :=
  outDiagram (A := Set.univ) (B := fun _ => Set.univ) (fun i => Fin.elim0 i)

def zeroInDiagram : fanIn 0 ⥤q semanticGraph Unit :=
  inDiagram (A := fun _ => Set.univ) (B := Set.univ) (fun i => Fin.elim0 i)

theorem zero_binding_nonempty : (zeroOutDiagram.obj .center : Set Unit).Nonempty ∧
    (zeroInDiagram.obj .center : Set Unit).Nonempty := ⟨⟨(), trivial⟩, ⟨(), trivial⟩⟩

-- [proof->req~predicate-interpretation~1]
theorem zero_diagram_key : zeroOutDiagram ∈ (interpretation Unit).meaning (.key 0) := by
  apply (key_zero _).mpr
  exact ⟨fun a b => Subtype.ext (Subsingleton.elim a.val b.val)⟩

theorem zero_diagram_not_cover : zeroInDiagram ∉ (interpretation Unit).meaning (.cover 0) :=
  fun h => ((cover_zero _).mp h).false ⟨(), trivial⟩

theorem zero_diagram_disjoint : zeroInDiagram ∈ (interpretation Unit).meaning (.disjoint 0) :=
  disjoint_zero _

/-- Repeated bindings in real graph maps, including the same underlying source. -/
def shared : Span (Set.univ : Set Unit) (Set.univ : Set Unit) := literal (fun _ h => h)
def repeatedDiagram := inDiagram (fun _ : Fin 2 => shared)

theorem repeated_diagram_rejected :
    repeatedDiagram ∉ (interpretation Unit).meaning (.disjoint 2) := by
  intro h
  exact h 0 1 (by decide) ⟨(), trivial⟩ ⟨(), trivial⟩ rfl

def disjointFormula : Formula signature (fanIn 2) := ⟨.disjoint 2, Prefunctor.id _⟩

theorem rejected_formula : ¬ (interpretation Unit).Satisfies repeatedDiagram disjointFormula :=
  repeated_diagram_rejected

def coverFormula : Formula signature (fanIn 2) := ⟨.cover 2, Prefunctor.id _⟩
def collapse : fanIn 2 ⥤q fanIn 2 where
  obj | .center => .center | .member _ => .member 0
  map | .edge _ => .edge 0

theorem collapse_not_identity : collapse ≠ Prefunctor.id (fanIn 2) := by
  intro h
  have he := congrArg (fun f => f.obj (.member 1)) h
  have hh : (0 : Fin 2) = 1 := FanIn.member.inj he
  exact (by decide : (0 : Fin 2) ≠ 1) hh

def sourceGraph : DPGraph signature := ⟨fanIn 2, {coverFormula}⟩
def targetGraph : DPGraph signature := ⟨fanIn 2, {coverFormula.translate collapse}⟩
def collapseHom : Hom sourceGraph targetGraph where
  toPrefunctor := collapse
  preserves := by intro φ h; change φ = coverFormula at h; subst φ; rfl

def targetModel : (interpretation Unit).Model targetGraph :=
  ⟨repeatedDiagram, by
    intro φ h
    change φ = coverFormula.translate collapse at h
    subst φ
    change Cover (fun _ : Fin 2 => shared)
    intro b
    exact ⟨0, b, rfl⟩⟩

def restrictedModel : (interpretation Unit).Model sourceGraph :=
  (interpretation Unit).reduct collapseHom targetModel

-- [proof->req~predicate-examples~1]
theorem restricted_model : (interpretation Unit).IsModel sourceGraph restrictedModel.val :=
  restrictedModel.property

theorem translation_interoperates :
    (interpretation Unit).Satisfies repeatedDiagram (coverFormula.translate collapse) ↔
      (interpretation Unit).Satisfies (collapse.comp repeatedDiagram) coverFormula :=
  (interpretation Unit).satisfies_translate coverFormula collapse repeatedDiagram

theorem reduct_identity : (interpretation Unit).reduct (Hom.id targetGraph) targetModel =
    targetModel := (interpretation Unit).reduct_id targetModel

theorem reduct_composition :
    (interpretation Unit).reduct (collapseHom.comp (Hom.id targetGraph)) targetModel =
      (interpretation Unit).reduct collapseHom
        ((interpretation Unit).reduct (Hom.id targetGraph) targetModel) :=
  (interpretation Unit).reduct_comp collapseHom (Hom.id targetGraph) targetModel

/-- Object universe 1, link universe 3, semantic arrow universe 4. -/
def largeIdentity : Span.{1,1,3} (Set.univ : Set (ULift.{1} Unit))
    (Set.univ : Set (ULift.{1} Unit)) where
  Link := ULift.{3} {x : ULift.{1} Unit // x ∈ (Set.univ : Set (ULift.{1} Unit))}
  source := ULift.down
  target := ULift.down

-- [proof->req~setmap-semantic-graph~1]
theorem larger_universe_interpretation :
    unaryDiagram.{1,3} largeIdentity ∈ (interpretation.{1,3} (ULift.{1} Unit)).meaning .inclusion :=
  ⟨⟨ULift.down_injective, fun a => ⟨⟨a⟩, rfl⟩⟩, fun _ => rfl⟩

end DPGraph.Predicates.Examples
