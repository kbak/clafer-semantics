module

public import Clafer.Syntax

/-!
# Individual Clafer Shapes

SoSyM §5.2/Figure 16, §5.3/Table 4, §5.5/Figure 18, §6.2.3/Figure 23.
These are local role graphs, not the MCS metamodel or a gluing construction.
The accepted correction to §5.3.4 retains the head of top-level abstracts.
-/

@[expose] public section
namespace Clafer
open CategoryTheory

namespace Roles

inductive ClassRole where | head | source | target
  deriving DecidableEq
inductive MapRole where | head | parent | dereference | target
  deriving DecidableEq

instance : Fintype ClassRole := ⟨{.head, .source, .target}, by intro r; cases r <;> simp⟩
instance : Fintype MapRole :=
  ⟨{.head, .parent, .dereference, .target}, by intro r; cases r <;> simp⟩

def classPresent (k : Kind) (parent : Bool) : ClassRole → Bool
  | .head => true | .source => parent | .target => k != .basic

def mapPresent (k : Kind) (parent : Bool) : MapRole → Bool
  | .head | .parent => parent
  | .dereference => k != .basic
  | .target => parent && k != .basic

def source : MapRole → ClassRole
  | .head | .target => .source | .parent | .dereference => .head
def target : MapRole → ClassRole
  | .head => .head | .parent => .source | .dereference | .target => .target

abbrev Class (k : Kind) (parent : Bool) := {r : ClassRole // classPresent k parent r = true}
abbrev Map (k : Kind) (parent : Bool) := {r : MapRole // mapPresent k parent r = true}

theorem endpoints_present (k : Kind) (p : Bool) (r : MapRole)
    (h : mapPresent k p r = true) :
    classPresent k p (source r) = true ∧ classPresent k p (target r) = true := by
  cases k <;> cases p <;> cases r <;>
    simp_all [classPresent, mapPresent, source, target]

/-- Existing Quiver hom types retain the arrow role and enforce both endpoints. -/
abbrev Arrow {k : Kind} {p : Bool} (a b : Class k p) :=
  {r : MapRole // mapPresent k p r = true ∧ source r = a.val ∧ target r = b.val}
instance (k : Kind) (p : Bool) : Quiver (Class k p) := ⟨Arrow⟩
abbrev graph (k : Kind) (p : Bool) : Quiv := Quiv.of (Class k p)

def head (k : Kind) (p : Bool) : Class k p := ⟨.head, rfl⟩
def mapSource {k : Kind} {p : Bool} (m : Map k p) : Class k p :=
  ⟨source m.val, (endpoints_present k p m.val m.property).1⟩
def mapTarget {k : Kind} {p : Bool} (m : Map k p) : Class k p :=
  ⟨target m.val, (endpoints_present k p m.val m.property).2⟩
def arrow {k : Kind} {p : Bool} (m : Map k p) : mapSource m ⟶ mapTarget m :=
  ⟨m.val, m.property, rfl, rfl⟩

-- [proof->req~clafer-individual-shapes~1]
theorem incidence {k : Kind} {p : Bool} {a b : Class k p} (e : a ⟶ b) :
    source e.val = a.val ∧ target e.val = b.val := ⟨e.property.2.1, e.property.2.2⟩

theorem no_basic_target (p : Bool) (c : Class .basic p) : c.val ≠ .target := by
  intro h
  have := c.property
  simp_all [classPresent]

theorem no_parent_source (k : Kind) (c : Class k false) : c.val ≠ .source := by
  intro h
  have := c.property
  simp_all [classPresent]

theorem no_parent_maps (k : Kind) (m : Map k false) : m.val = .dereference := by
  obtain ⟨r, hr⟩ := m
  cases r with
  | dereference => rfl
  | head | parent => exact Bool.noConfusion hr
  | target => cases k <;> exact Bool.noConfusion hr

theorem root_only_head (c : Class .basic false) : c = head .basic false := by
  apply Subtype.ext
  obtain ⟨r, hr⟩ := c
  cases r with
  | head => rfl
  | source | target => exact Bool.noConfusion hr

theorem root_no_maps : IsEmpty (Map .basic false) := by
  constructor
  rintro ⟨r, hr⟩
  cases r <;> simp_all [mapPresent]

-- [proof->req~clafer-finite-traversal~1]
theorem classes_finite (k : Kind) (p : Bool) : Finite (Class k p) := inferInstance
theorem arrows_finite (k : Kind) (p : Bool) :
    Finite (Σ a b : Class k p, (a ⟶ b)) := by
  apply Finite.of_injective (fun e : Σ a b : Class k p, (a ⟶ b) => e.2.2.val)
  rintro ⟨a, b, e⟩ ⟨c, d, f⟩ he
  change e.val = f.val at he
  have ha : a = c := Subtype.ext
    (e.property.2.1.symm.trans ((congrArg source he).trans f.property.2.1))
  have hb : b = d := Subtype.ext
    (e.property.2.2.symm.trans ((congrArg target he).trans f.property.2.2))
  subst c
  subst d
  have hf : e = f := Subtype.ext he
  subst f
  rfl

/-- Table 4: only a bag reference's composite target map has bag mode.
Set references additionally require the parent/dereference key in full semantics. -/
def mode (k : Kind) (r : MapRole) : FormalCD.MapMode :=
  if k = .referenceBag ∧ r = .target then .bag else .ordinary

def needsReferenceKey (k : Kind) (p : Bool) : Bool := k == .referenceSet && p

end Roles

-- [impl->req~clafer-individual-shapes~1]
/-- An individual shape recipe with typed optional roles. Abstractness is an
AST property; the presence of a parent determines its local topology. -/
structure Shape where
  kind : Kind
  hasParent : Bool
  name : String
  multiplicity : DPGraph.Predicates.Range

abbrev Shape.carrier (s : Shape) : Quiv := Roles.graph s.kind s.hasParent

/-- Decode only the local role inventory; no recursive compilation/cojoining claim. -/
def Located.shape (d : Located) : Shape :=
  ⟨d.declaration.reference.kind, d.parent.isSome, d.declaration.name,
    d.declaration.multiplicity.effective⟩

theorem Located.shape_has_head (d : Located) : Nonempty d.shape.carrier :=
  ⟨Roles.head _ _⟩

theorem Located.parentless_has_no_source (d : Located) (h : d.parent = none)
    (c : d.shape.carrier) : c.val ≠ .source := by
  have hc := c.property
  intro he
  simp [Located.shape, h, Roles.classPresent, he] at hc

/-- A realization in the delivered FormalCD API. Identity need not be recovered
from display names. Full MCS constraints and semantic satisfaction are separate. -/
structure Shape.Realization {R : FormalCD.Registry} (s : Shape) (D : FormalCD.Raw R) where
  binding : s.carrier ⥤q D.carrier
  modes : ∀ {a b} (e : a ⟶ b), D.mode (binding.map e) = Roles.mode s.kind e.val

namespace Shape
open Roles

/-- Optional inclusion roles exist exactly where both shapes have that class
role. The head role is consequently always included when a super is selected. -/
abbrev SharedClass (sub sup : Shape) :=
  {r : ClassRole // classPresent sub.kind sub.hasParent r = true ∧
    classPresent sup.kind sup.hasParent r = true}

def SharedClass.subClass {sub sup : Shape} (r : SharedClass sub sup) : sub.carrier :=
  ⟨r.val, r.property.1⟩
def SharedClass.superClass {sub sup : Shape} (r : SharedClass sub sup) : sup.carrier :=
  ⟨r.val, r.property.2⟩

def headInclusion (sub sup : Shape) : SharedClass sub sup := ⟨.head, rfl, rfl⟩

structure Inclusions {R : FormalCD.Registry} {D : FormalCD.Raw R} {sub sup : Shape}
    (a : sub.Realization D) (b : sup.Realization D) where
  map : (r : SharedClass sub sup) →
    a.binding.obj r.subClass ⟶ b.binding.obj r.superClass
  inclusion : ∀ r, D.mode (map r) = .inclusion

theorem Inclusions.declared {R : FormalCD.Registry} {D : FormalCD.Raw R} {sub sup : Shape}
    {a : sub.Realization D} {b : sup.Realization D} (i : Inclusions a b)
    (h : D.WellFormed) (r : SharedClass sub sup) :
    FormalCD.inclusionFormula (i.map r) ∈ D.declarations :=
  h.inclusion_decl (i.map r) (i.inclusion r)

/-- No super gives no inclusion family; a super requires every shared role. -/
def OptionalInclusions {R : FormalCD.Registry} {D : FormalCD.Raw R} {sub : Shape}
    (a : sub.Realization D) (super : Option Shape) : Type _ :=
  match super with
  | none => PUnit
  | some sup => Σ b : sup.Realization D, Inclusions a b

theorem inclusion_roles_finite (sub sup : Shape) : Finite (SharedClass sub sup) := inferInstance

theorem no_source_inclusion {sub sup : Shape} (h : sub.hasParent = false)
    (r : SharedClass sub sup) : r.val ≠ .source := by
  intro he
  have hr := r.property.1
  simp [classPresent, he, h] at hr

end Shape
end Clafer
