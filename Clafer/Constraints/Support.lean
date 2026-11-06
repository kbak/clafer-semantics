module

public import Clafer.Syntax

/-!
[impl->req~clafer-core-binding~1]
[impl->req~clafer-core-support~1]
[impl->req~clafer-core-typing~1]
[impl->req~clafer-integer-extraction~1]
[proof->req~clafer-core-support~1]
-/

/-!
# Resolved constraint support

SoSyM §6.2.2/Figure 22 and D.2–D.3.2. A finite occurrence graph supplies
resolved class and map identities. Its binding into a future compiled diagram
is separate from expression typing and from any interpretation of predicates.
-/

@[expose] public section
namespace Clafer.Constraints
open CategoryTheory

inductive MapKind where
  | head | parent | dereference | target | inclusion
  deriving DecidableEq, Repr

structure MapRef (n : Nat) where
  owner : DeclId
  kind : MapKind
  source : Fin n
  target : Fin n
  name : String := ""

/-- Positions are identities of support occurrences, even when their resolved
IDs or display names repeat. No minimality or deduplication is assumed. -/
structure Support where
  classCount : Nat
  mapCount : Nat
  classId : Fin classCount → DeclId
  mapRef : Fin mapCount → MapRef classCount
  context : Fin classCount
  /-- Explicit primitive annotation, checked against the resolved AST. -/
  integer : Fin classCount → Bool := fun _ => false

abbrev Support.Vertex (s : Support) := Fin s.classCount
abbrev Support.Edge (s : Support) := Fin s.mapCount

def Support.Arrow (s : Support) (x y : s.Vertex) :=
  {e : s.Edge // (s.mapRef e).source = x ∧ (s.mapRef e).target = y}

/-- Bundle the incidence with this support: different supports with the same
vertex count need not have the same arrows. -/
abbrev Support.graph (s : Support) : Quiv := @Quiv.of s.Vertex ⟨s.Arrow⟩

def Support.arrow (s : Support) (e : s.Edge) :
    s.Arrow (s.mapRef e).source (s.mapRef e).target := ⟨e, rfl, rfl⟩

theorem Support.incidence (s : Support) {x y : s.Vertex} (e : s.Arrow x y) :
    (s.mapRef e.val).source = x ∧ (s.mapRef e.val).target = y := e.property

/-- Map roles are checked against actual resolved declarations, not supplied
as arbitrary endpoint equations. Target maps are parent-to-reference-target. -/
def Support.MapResolved (s : Support) (a : AST) (e : s.Edge) : Prop :=
  ∃ d ∈ a.entries, d.declaration.id = (s.mapRef e).owner ∧
    match (s.mapRef e).kind with
    | .head => d.parent = some (s.classId (s.mapRef e).source) ∧
        d.declaration.id = s.classId (s.mapRef e).target
    | .parent => d.declaration.id = s.classId (s.mapRef e).source ∧
        d.parent = some (s.classId (s.mapRef e).target)
    | .dereference => d.declaration.id = s.classId (s.mapRef e).source ∧
        d.declaration.reference.target = some (s.classId (s.mapRef e).target)
    | .target => d.parent = some (s.classId (s.mapRef e).source) ∧
        d.declaration.reference.target = some (s.classId (s.mapRef e).target)
    | .inclusion => d.declaration.id = s.classId (s.mapRef e).source ∧
        d.declaration.super = some (s.classId (s.mapRef e).target)

structure Support.Resolved (s : Support) (a : AST) : Prop where
  classes : ∀ v, a.Known (s.classId v)
  maps : ∀ e, s.MapResolved a e
  integers : ∀ v, s.integer v = true →
    ∃ d ∈ a.entries, d.declaration.id = s.classId v ∧
      d.declaration.origin = .primitive .int

/-- A direct super edge, with its declaration occurrence retained. -/
def DirectSuper (a : AST) (sub sup : DeclId) : Prop :=
  ∃ d ∈ a.entries, d.declaration.id = sub ∧ d.declaration.super = some sup

inductive Extends (a : AST) : DeclId → DeclId → Prop where
  | refl (x) : Extends a x x
  | direct {x y} : DirectSuper a x y → Extends a x y
  | trans {x y z} : Extends a x y → Extends a y z → Extends a x z

theorem Extends.preserves {a : AST} {p : DeclId → Prop}
    (step : ∀ x y, DirectSuper a x y → p x → p y)
    {x y} (h : Extends a x y) : p x → p y := by
  induction h with
  | refl => exact id
  | direct h => exact step _ _ h
  | trans _ _ h₁ h₂ => exact fun hx => h₂ (h₁ hx)

/-- Explicit widening evidence; elaboration may insert these paths. Equal
resolved IDs also permit movement between distinct support occurrences. -/
inductive Widen (s : Support) : s.Vertex → s.Vertex → Type where
  | same {x y} : s.classId x = s.classId y → Widen s x y
  | inclusion (e : s.Edge) : (s.mapRef e).kind = .inclusion →
      Widen s (s.mapRef e).source (s.mapRef e).target
  | trans {x y z} : Widen s x y → Widen s y z → Widen s x z

def Widen.refl {s : Support} (x : s.Vertex) : Widen s x x := .same rfl

/-- Widening can only follow equal identities or actual inheritance edges.
This is a resolution/typing result, not a semantic inclusion theorem. -/
theorem Widen.resolved {s : Support} {a : AST} (h : s.Resolved a)
    {x y} (w : Widen s x y) : Extends a (s.classId x) (s.classId y) := by
  induction w with
  | same he => rw [he]; exact .refl _
  | inclusion e hk =>
      obtain ⟨d, hd, _, hm⟩ := h.maps e
      simp only [hk] at hm
      exact .direct ⟨d, hd, hm⟩
  | trans _ _ h₁ h₂ => exact .trans h₁ h₂

/-- Every recorded boundary occurrence has its own position. The support may
also contain intermediate navigation/inheritance vertices and unused vertices. -/
structure Support.Boundary (s : Support) (c : ConstraintBoundary) where
  context_eq : s.classId s.context = c.context
  occurrence : c.Occurrence → s.Vertex
  occurrence_eq : ∀ i, s.classId (occurrence i) = c.referenced i
  domain : (b : Fin c.binders.length) → Fin c.binders[b].domainOccurrences.length → s.Vertex
  domain_eq : ∀ b i, s.classId (domain b i) = c.binders[b].domainOccurrences[i]

end Clafer.Constraints
