module

public import Clafer.Semantics.Structural
public import Clafer.MCS.Laws

/-!
# Shared-object/span realization of structural roles

SoSyM B.1–B.5, §6.2.3–5. Ordinary relation links have tuple identities;
the derived target map uses the adopted Q1 pullback, including parallel links.
This realizes the actual canonical role graph used by structural Compile.
-/

@[expose] public section
namespace Clafer.Semantics
open CategoryTheory DPGraph DPGraph.Predicates MCS

namespace Configuration
variable {n : Nat} {U : Type} (m : EffectiveCore n) (s : Configuration (Fin n) U)

def headMap (d : Fin n) :
    Span (s.head ((m.family.parent d).getD d)) (s.head d) :=
  Span.ofRelation (fun p x => s.contains d p.val x.val)

def derefMap (d : Fin n) :
    Span (s.head d) (s.head ((m.family.reference d).target.getD d)) :=
  Span.ofRelation (fun x t => s.deref d x.val t.val)

def targetMap (d : Fin n) := (s.headMap m d).comp (s.derefMap m d)

def ordinaryMap (d : Fin n)
    (r : Clafer.Roles.Map (m.family.shape d).kind (m.family.shape d).hasParent) :
    Span (s.head (m.family.canonicalRoles.source (.ordinary d r)))
      (s.head (m.family.canonicalRoles.target (.ordinary d r))) :=
  match r with
  | ⟨.head, _⟩ => s.headMap m d
  | ⟨.parent, _⟩ => (s.headMap m d).inverse
  | ⟨.dereference, _⟩ => s.derefMap m d
  | ⟨.target, _⟩ => s.targetMap m d

def inclusionMap (r : m.family.InclusionSlot) :
    Span (s.head (m.family.canonicalRoles.source (.inclusion r)))
      (s.head (m.family.canonicalRoles.target (.inclusion r))) :=
  Span.ofRelation (fun a b => a.val = b.val)

-- [impl->req~clafer-structural-satisfaction~1]
/-- Every structural role has a concrete interpretation, with shared class
objects inherited from the canonical cojoining rather than cloned by role. -/
def interpret : m.family.canonicalRoles.graph ⥤q semanticGraph U where
  obj := s.head
  map := by
    rintro a b ⟨e, rfl, rfl⟩
    cases e with
    | ordinary d r => exact s.ordinaryMap m d r
    | inclusion r => exact s.inclusionMap m r

theorem headMap_setValued (d : Fin n) : SetValued (s.headMap m d) :=
  Span.ofRelation_jointlyInjective _

theorem derefMap_setValued (d : Fin n) : SetValued (s.derefMap m d) :=
  Span.ofRelation_jointlyInjective _

theorem parent_inverse (d : Fin n) :
    Inverse (s.headMap m d) (s.headMap m d).inverse := ⟨Span.Iso.refl _⟩

theorem target_commutes (d : Fin n) :
    Commutation (s.headMap m d) (s.derefMap m d) (s.targetMap m d) :=
  ⟨Span.Iso.refl _⟩

/-- Finite head counts will therefore count containment links, not targets. -/
def headFiberEquiv (typed : s.Typed m) (d p : Fin n)
    (hp : m.family.parent d = some p) (x : s.head p) :
    (s.headMap m d).toFamily.Index
      ⟨x.val, by simp [hp]⟩ ≃
      {y : U // s.contains d x.val y} where
  toFun l := ⟨l.val.val.2.val, by
    have he : l.val.val.1.val = x.val := congrArg Subtype.val l.property
    have hq : s.contains d l.val.val.1.val l.val.val.2.val := l.val.property
    rw [he] at hq
    exact hq⟩
  invFun y := ⟨⟨(⟨x.val, by simp [hp]⟩,
      ⟨y.val, (typed.1 d x.val y.val y.property).1⟩), y.property⟩, rfl⟩
  left_inv l := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext l.property.symm rfl
  right_inv _ := rfl

theorem head_multiplicity_iff (typed : s.Typed m) (d p : Fin n)
    (hp : m.family.parent d = some p) :
    TargetMultiplicity (m.family.multiplicity d) (s.headMap m d) ↔
      ∀ x, (x ∈ s.head p) → InRange (m.family.multiplicity d) {y : U // s.contains d x y} := by
  simp only [TargetMultiplicity]
  constructor
  · intro h x hx
    exact (inRange_iff _ (s.headFiberEquiv m typed d p hp ⟨x, hx⟩)).mp (h _)
  · intro h x
    have hx := x.property
    change x.val ∈ s.head ((m.family.parent d).getD d) at hx
    have hx' : (x.val ∈ s.head p) := by simpa only [hp, Option.getD_some] using hx
    exact (inRange_iff _ (s.headFiberEquiv m typed d p hp ⟨x.val, hx'⟩)).mpr (h _ hx')

end Configuration

-- [proof->req~clafer-structural-satisfaction~1]
/-- Ordinary maps can always be represented by their relation tuples under
set-valuedness; reference composite links are transported, never collapsed. -/
theorem ordinary_representation {A B C : Type}
    (q : Span A B) (r : Span B C) (hq : SetValued q) (hr : SetValued r) :
    Nonempty (Span.Iso q (Span.ofRelation q.red)) ∧
    Nonempty (Span.Iso r (Span.ofRelation r.red)) ∧
    Nonempty (Span.Iso (q.comp r)
      ((Span.ofRelation q.red).comp (Span.ofRelation r.red))) :=
  ⟨⟨q.relationIso hq⟩, ⟨r.relationIso hr⟩, ⟨(q.relationIso hq).comp (r.relationIso hr)⟩⟩

end Clafer.Semantics
