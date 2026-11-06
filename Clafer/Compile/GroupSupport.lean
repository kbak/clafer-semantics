module

public import Clafer.Compile.EffectiveCore
public import Clafer.Compile.Basic
public import Clafer.Semantics.Interpretation

/-!
[impl->req~clafer-compile-formulas~1]
[impl->req~clafer-compile-groups~1]
[proof->req~clafer-compile-groups~1]
-/

/-!
# Group arities and meanings

SoSyM §4.2.1, §6.2.2, B.4 Definition 8 and Appendix 3; D6 as recorded in
docs/group-compilation.md. Abstract groups supply effective bounds at concrete
contexts. Child objects retain ambient identity across inherited head maps.
-/

@[expose] public section
namespace Clafer.Compile.Groups
open CategoryTheory MCS DPGraph DPGraph.Predicates

variable {C : Type} (f : Family C)

/-- Reflexive super hierarchy, selected from resolved identities. -/
def Ancestor (p s : C) : Prop :=
  Relation.ReflTransGen (fun c s => f.super c = some s) p s

abbrev Ancestors (p : C) := {s : C // Ancestor f p s}

/-- Each inventory entry is a declaration head, never its reference target. -/
abbrev Child (p : C) := Σ s : Ancestors f p, {c : C // f.parent c = some s.val}

abbrev Vertex (p : C) := Ancestors f p ⊕ Child f p

inductive Edge (p : C) : Vertex f p → Vertex f p → Type where
  | head (c : Child f p) : Edge p (.inl c.1) (.inr c)
  | inclusion (s t : Ancestors f p) (h : f.super s.val = some t.val) :
      Edge p (.inl s) (.inl t)

def arity (p : C) : Quiv := @Quiv.of (Vertex f p) ⟨Edge f p⟩

def context (p : C) : arity f p := .inl ⟨p, .refl⟩

def boundVertex {p : C} : Vertex f p → C
  | .inl s => s.val
  | .inr c => c.2.val

def headArrow {p : C} (c : Child f p) : f.canonicalRoles.Arrow c.1.val c.2.val := by
  refine ⟨.ordinary c.2.val ⟨.head, by simp [Clafer.Roles.mapPresent, Family.shape, c.2.property]⟩, ?_, rfl⟩
  change (f.parent c.2.val).getD c.2.val = c.1.val
  simp [c.2.property]

/-- Full binding includes context, super vertices, child heads and every
selected head/inclusion arrow. No identity-support roles are invented. -/
def binding (p : C) : arity f p ⥤q f.canonicalRoles.graph where
  obj := boundVertex f
  map
    | .head c => headArrow f c
    | .inclusion s t h =>
        ⟨.inclusion ⟨s.val, t.val, Shape.headInclusion _ _, h⟩, rfl, rfl⟩

@[simp] theorem binding_context (p : C) : (binding f p).obj (context f p) = p := rfl

theorem child_iff (p c : C) :
    (∃ k : Child f p, k.2.val = c) ↔ ∃ s, Ancestor f p s ∧ f.parent c = some s := by
  constructor
  · rintro ⟨⟨s, c', hc⟩, rfl⟩; exact ⟨s.val, s.property, hc⟩
  · rintro ⟨s, hs, hc⟩; exact ⟨⟨⟨s, hs⟩, ⟨c, hc⟩⟩, rfl⟩

instance [Finite C] (p : C) : Finite (Child f p) := inferInstance

/-- One generated symbol for every concrete context, including empty groups. -/
abbrev Id := {p : C // f.isAbstract p = false}

def signature : DPGraph.Signature := ⟨Id f, fun p => arity f p.val⟩

def formula (p : Id f) : Formula (signature f) f.canonicalRoles.graph :=
  ⟨p, binding f p.val⟩

/-- Union by ambient identity: multiple paths or parallel links witnessing the
same child object do not create extra occurrences. Reference targets are unused. -/
def Objects {U : Type} {p : C} (d : arity f p ⥤q semanticGraph U)
    (x y : U) : Prop :=
  ∃ c : Child f p, ∃ l : (d.map (.head c)).Link,
    ((d.map (.head c)).source l).val = x ∧
    ((d.map (.head c)).target l).val = y

def meaning {U : Type} (p : Id f) (d : arity f p.val ⥤q semanticGraph U) : Prop :=
  ∀ x : Subtype (d.obj (context f p.val)),
    InRange (f.group p.val).effective.range {y : U // Objects f d x.val y}

def interpretation (U : Type) : Interpretation (signature f) (semanticGraph U) :=
  ⟨meaning f⟩

/-- The independent structural statement: same parent identity and the union
of selected containment fibers. #66 must supply any realization of these maps. -/
def ChildObjects {U : Type} (s : Semantics.Configuration C U) (p : C) (x y : U) : Prop :=
  ∃ a, Ancestor f p a ∧ ∃ c, f.parent c = some a ∧ s.contains c x y

def Holds {U : Type} (s : Semantics.Configuration C U) (p : C) : Prop :=
  ∀ x : s.head p,
    InRange (f.group p).effective.range {y : U // ChildObjects f s p x.val y}

end Clafer.Compile.Groups
