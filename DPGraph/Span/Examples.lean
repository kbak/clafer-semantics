module

public import DPGraph.Span

/-!
# Span witnesses

Kernel-checked boundary cases for SoSyM B.1–B.2. The two-path example explains
why B.2.1 needs the adopted Q1 correction. All finite types are local to these
examples; the library theorems have no finiteness assumption.
-/

@[expose] public section

namespace DPGraph.Span.Examples

-- [impl->req~span-examples~1]
/-- Two distinct links share both endpoints. -/
def parallel : Span Unit Unit where
  Link := Bool
  source _ := ()
  target _ := ()

-- [proof->req~span-representation~1]
theorem parallel_links : (false : parallel.Link) ≠ true ∧
    parallel.source false = parallel.source true ∧
    parallel.target false = parallel.target true := ⟨Bool.false_ne_true, rfl, rfl⟩

theorem parallel_not_jointlyInjective : ¬ parallel.JointlyInjective := by
  intro h
  exact Bool.false_ne_true (h (show ((), ()) = ((), ()) from rfl))

theorem parallel_reduction (a b : Unit) : parallel.red a b := by
  cases a
  cases b
  exact ⟨false, rfl, rfl⟩

/-- Every fiber is empty, even though the endpoint types are inhabited. -/
def empty : Span Unit Bool where
  Link := Empty
  source := Empty.elim
  target := Empty.elim

theorem empty_fibers (a : Unit) : IsEmpty (empty.toFamily.Index a) :=
  ⟨fun l => Empty.elim l.1⟩

theorem empty_reduction (a : Unit) (b : Bool) : ¬ empty.red a b := by
  rintro ⟨l, _⟩
  exact Empty.elim l

def empty_family : IndexedFamily Unit Bool where
  Index _ := Empty
  eval _ := Empty.elim

def empty_family_roundtrip : IndexedFamily.Equivalence
    empty_family.toSpan.toFamily empty_family := empty_family.spanFamilyEquivalence

def empty_span_roundtrip : Iso empty.toFamily.toSpan empty := empty.familySpanIso

/-- The source type itself may also be empty. -/
def empty_endpoints : Span Empty Empty := identity Empty

theorem empty_endpoints_no_links : IsEmpty empty_endpoints.Link := ⟨Empty.elim⟩

/-- One source, two intermediate objects, one target (SoSyM B.2.1). -/
def firstRelation (_ : Unit) (_ : Bool) : Prop := True
def secondRelation (_ : Bool) (_ : Unit) : Prop := True

def first : Span Unit Bool := ofRelation firstRelation
def second : Span Bool Unit := ofRelation secondRelation

def path (b : Bool) : (first.comp second).Link :=
  ⟨(⟨((), b), trivial⟩, ⟨(b, ()), trivial⟩), rfl⟩

/-- Exactly two composite links, distinguished by the intermediate object. -/
def twoPaths : Bool ≃ (first.comp second).Link where
  toFun := path
  invFun p := p.1.1.1.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨⟨⟨a, b⟩, hq⟩, ⟨⟨b', c⟩, hr⟩⟩, h⟩
    cases a
    cases c
    cases h
    rfl

theorem paths_distinct : path false ≠ path true := by
  intro h
  exact Bool.false_ne_true (twoPaths.injective h)

/-- Exactly one reduced endpoint pair. -/
def oneReducedPair : (ofRelation (relationComp first.red second.red)).Link ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨((), ()), false, ⟨⟨((), false), trivial⟩, rfl, rfl⟩,
    ⟨⟨(false, ()), trivial⟩, rfl, rfl⟩⟩
  left_inv := by rintro ⟨⟨a, c⟩, h⟩; cases a; cases c; rfl
  right_inv := by intro a; cases a; rfl

theorem two_path_reduction : (first.comp second).red =
    relationComp first.red second.red := red_comp first second

theorem second_singleValued : SingleValued secondRelation := by
  intro b c c' _ _
  exact Subsingleton.elim c c'

theorem two_path_not_jointlyInjective : ¬ (first.comp second).JointlyInjective := by
  intro h
  exact paths_distinct (h (show
    ((first.comp second).source (path false), (first.comp second).target (path false)) =
    ((first.comp second).source (path true), (first.comp second).target (path true)) from rfl))

/-- A single-valued second input still does not imply the stronger isomorphism. -/
theorem two_path_not_iso : ¬ Nonempty
    (Iso (first.comp second) (ofRelation (relationComp first.red second.red))) := by
  intro h
  exact two_path_not_jointlyInjective ((comp_iso_relation_iff first second).mp h)

-- [proof->req~span-examples~1]
theorem second_singleValued_not_sufficient : SingleValued secondRelation ∧
    ¬ Nonempty (Iso (first.comp second) (ofRelation (relationComp first.red second.red))) :=
  ⟨second_singleValued, two_path_not_iso⟩

/-- Unique intermediate objects do not prevent parallel input links. -/
theorem parallel_uniqueIntermediate : UniqueIntermediate parallel.red (identity Unit).red := by
  intro a c b b' _ _ _ _
  exact Subsingleton.elim b b'

theorem parallel_composite_not_iso : ¬ Nonempty (Iso (parallel.comp (identity Unit))
    (ofRelation (relationComp parallel.red (identity Unit).red))) := by
  intro h
  have hj := (comp_iso_relation_iff parallel (identity Unit)).mp h
  exact parallel_not_jointlyInjective (jointlyInjective_of_iso (rightUnit parallel).symm hj)

/-- A partial first relation is enough: totality is unnecessary. -/
def partialFirst (a b : Bool) : Prop := a = false ∧ b = true

theorem partialFirst_singleValued : SingleValued partialFirst := by
  intro a b b' h h'
  exact h.2.trans h'.2.symm

theorem partialFirst_not_total : ¬ ∀ a, ∃ b, partialFirst a b := by
  intro h
  rcases h true with ⟨b, hb⟩
  exact Bool.noConfusion hb.1

theorem partial_first_composite_injective :
    ((ofRelation partialFirst).comp second).JointlyInjective :=
  relations_comp_injective_of_first_singleValued partialFirst secondRelation
    partialFirst_singleValued

theorem partial_converse_composite_injective :
    (first.comp (ofRelation (fun b a => partialFirst a b))).JointlyInjective :=
  relations_comp_injective_of_converse_second_singleValued firstRelation
    (fun b a => partialFirst a b) partialFirst_singleValued

/-- Endpoints and links occupy three different universes. -/
def large : Span.{1, 2, 3} (ULift.{1} Unit) (ULift.{2} Bool) where
  Link := ULift.{3} Bool
  source _ := ⟨()⟩
  target l := ⟨l.down⟩

def large_roundtrip : Iso large.toFamily.toSpan large := large.familySpanIso

def large_family_roundtrip : IndexedFamily.Equivalence
    large.toFamily.toSpan.toFamily large.toFamily := large.toFamily.spanFamilyEquivalence

def large_left_unit : Iso ((identity (ULift.{1} Unit)).comp large) large := leftUnit large

def large_right_unit : Iso (large.comp (identity (ULift.{2} Bool))) large := rightUnit large

def large_associator : Iso ((large.comp large.inverse).comp large)
    (large.comp (large.inverse.comp large)) := associator large large.inverse large

def large_family_composition : IndexedFamily.Equivalence
    (large.comp large.inverse).toFamily (large.toFamily.comp large.inverse.toFamily) :=
  compFamilyEquivalence large large.inverse

theorem large_relation_composition : (large.comp large.inverse).red =
    relationComp large.red large.inverse.red := red_comp large large.inverse

theorem large_jointlyInjective : large.JointlyInjective := by
  intro l m h
  have ht := congrArg (fun p => p.2.down) h
  cases l
  cases m
  cases ht
  rfl

/-- The relation head lies in Type 2, while the original links lie in Type 3. -/
noncomputable def large_relation_iso : Iso large (ofRelation large.red) :=
  large.relationIso large_jointlyInjective

/-- Here a Type 0 head rises to Type 2 on the source-fiber roundtrip. -/
def raisedSource : Span.{2, 0, 0} (ULift.{2} Unit) Unit where
  Link := Bool
  source _ := ⟨()⟩
  target _ := ()

def raisedSource_roundtrip : Iso raisedSource.toFamily.toSpan raisedSource :=
  raisedSource.familySpanIso

def raisedFamily : IndexedFamily.{2, 0, 0} (ULift.{2} Unit) Bool where
  Index _ := Bool
  eval _ i := i

def raisedFamily_roundtrip : IndexedFamily.Equivalence
    raisedFamily.toSpan.toFamily raisedFamily := raisedFamily.spanFamilyEquivalence

end DPGraph.Span.Examples
