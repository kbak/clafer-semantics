module

public import Clafer.Behavioral.StructuralObservation
public import Clafer.Behavioral.CapturedStatic
public import Clafer.Constraints.DenotationInvariance

/-! # Full current-state support bindings

SoSyM §6.2.2/Appendix 4 and behavioral §5 expression equations. A resolved
support keeps every vertex and map occurrence. Target-map links retain the
intermediate reference head, so equal targets never collapse bag occurrences.
Only the expression evaluator takes the explicit existential relation reduct.
-/

@[expose] public section
namespace Clafer.Behavioral.StructuralBinding
open Semantics Constraints DPGraph DPGraph.Predicates CategoryTheory
universe u

variable {n : Nat} {U : Type u} (m : Structural.Core n) (τ : Trace (Fin n) U) (t : Nat)

-- [impl->req~behavioral-reference-atoms~1]
def Link (d : Fin n) : MapKind → Type u
  | .head => {p : U × U // (τ.raw m.toEffectiveCore t).contains d p.1 p.2}
  | .parent => {p : U × U // p.2 ∈ (τ.raw m.toEffectiveCore t).head d ∧ τ.ParentAt t p.1 p.2}
  | .dereference => {p : U × U // InheritedReference.deref m.family (τ.raw m.toEffectiveCore t) d p.1 p.2}
  | .target => {p : U × U × U // (τ.raw m.toEffectiveCore t).contains d p.1 p.2.1 ∧
      InheritedReference.deref m.family (τ.raw m.toEffectiveCore t) d p.2.1 p.2.2}
  | .inclusion => (τ.raw m.toEffectiveCore t).head d

def source (d : Fin n) : (k : MapKind) → Link m τ t d k → U
  | .head, l => l.val.1
  | .parent, l => l.val.2
  | .dereference, l => l.val.1
  | .target, l => l.val.1
  | .inclusion, l => l.val

def target (d : Fin n) : (k : MapKind) → Link m τ t d k → U
  | .head, l => l.val.2
  | .parent, l => l.val.1
  | .dereference, l => l.val.2
  | .target, l => l.val.2.2
  | .inclusion, l => l.val

def transport {d e : Fin n} {a b : MapKind} (hd : d = e) (hk : a = b) :
    Link m τ t d a ≃ Link m τ t e b := by
  subst e; subst b; exact Equiv.refl _

theorem source_transport {d e : Fin n} {a b : MapKind} (hd : d = e) (hk : a = b)
    (l : Link m τ t d a) :
    source m τ t e b (transport m τ t hd hk l) = source m τ t d a l := by
  subst e; subst b; rfl

theorem target_transport {d e : Fin n} {a b : MapKind} (hd : d = e) (hk : a = b)
    (l : Link m τ t d a) :
    target m τ t e b (transport m τ t hd hk l) = target m τ t d a l := by
  subst e; subst b; rfl

def span (d : Fin n) (k : MapKind) {A B : Set U}
    (typed : ∀ l : Link m τ t d k, source m τ t d k l ∈ A ∧ target m τ t d k l ∈ B) :
    Span A B where
  Link := Link m τ t d k
  source l := ⟨source m τ t d k l, (typed l).1⟩
  target l := ⟨target m τ t d k l, (typed l).2⟩

theorem span_inclusion (d : Fin n) (k : MapKind) {A B : Set U}
    (typed : ∀ l : Link m τ t d k, source m τ t d k l ∈ A ∧ target m τ t d k l ∈ B)
    (hk : k = .inclusion) (ha : A = (τ.raw m.toEffectiveCore t).head d) :
    Inclusion (span m τ t d k typed) := by
  subst k; subst A
  constructor
  · constructor
    · intro x y h; exact Subtype.ext (congrArg Subtype.val h)
    · intro x; exact ⟨x, rfl⟩
  · intro l; rfl

/-- The full resolved support and its endpoint obligations. `typed` is a local
typing obligation on actual links, not an assumed expression-agreement theorem.
Parentless abstract contexts may need a specialized support for their actual
parent view; this interface never invents a declaration parent. -/
structure Resolution (s : Support) where
  classOf : s.Vertex → Fin n
  owner : s.Edge → Fin n
  class_identity : ∀ v, s.classId v = m.id (classOf v)
  owner_identity : ∀ e, (s.mapRef e).owner = m.id (owner e)
  typed : ∀ e (l : Link m τ t (owner e) (s.mapRef e).kind),
    source m τ t _ _ l ∈ (τ.raw m.toEffectiveCore t).head (classOf (s.mapRef e).source) ∧
    target m τ t _ _ l ∈ (τ.raw m.toEffectiveCore t).head (classOf (s.mapRef e).target)
  inclusion_source : ∀ e, (s.mapRef e).kind = .inclusion →
    classOf (s.mapRef e).source = owner e

/-- Declaration-resolved roles on the ordinary typed navigation domain. An
abstract context with heterogeneous actual parents instead uses `SetExpr.parent`;
its ambient identity relation does not pretend to have a single parent class. -/
def Role (d a b : Fin n) : MapKind → Prop
  | .head => m.family.parent d = some a ∧ b = d
  | .parent => a = d ∧ m.family.parent d = some b
  | .dereference => a = d ∧ ∃ o, InheritedReference.Owner m.family d o ∧
      (m.family.reference o).target = some b
  | .target => m.family.parent d = some a ∧ ∃ o, InheritedReference.Owner m.family d o ∧
      (m.family.reference o).target = some b
  | .inclusion => a = d ∧ m.toEffectiveCore.Ancestor d b

-- [proof->req~behavioral-reference-atoms~1]
theorem role_typed (valid : Structural.Valid m τ) {d a b : Fin n} {k : MapKind}
    (role : Role m d a b k) (l : Link m τ t d k) :
    source m τ t d k l ∈ (τ.raw m.toEffectiveCore t).head a ∧
      target m τ t d k l ∈ (τ.raw m.toEffectiveCore t).head b := by
  have parentTyped {d p x} (link : (τ.raw m.toEffectiveCore t).contains d p x) {a}
      (ha : m.family.parent d = some a) : p ∈ (τ.raw m.toEffectiveCore t).head a := by
    obtain ⟨_, c, hc, hp⟩ := (valid.states t).typed.1 d p x link
    have eq := Option.some.inj (hc.symm.trans ha)
    exact eq ▸ hp
  cases k with
  | head =>
    rcases role with ⟨ha, rfl⟩
    exact ⟨parentTyped l.property ha, ((valid.states t).typed.1 _ _ _ l.property).1⟩
  | parent =>
    rcases role with ⟨rfl, hb⟩
    exact ⟨l.property.1, parentTyped ⟨l.property.2, l.property.1.2, by rw [hb]; simp⟩ hb⟩
  | dereference =>
    rcases role with ⟨rfl, o, ho, hb⟩
    have hx := (InheritedReference.deref_owner ho _ _).mp l.property
    exact ⟨hx.1, valid.target_typed ho hb l.property⟩
  | target =>
    rcases role with ⟨ha, o, ho, hb⟩
    exact ⟨parentTyped l.property.1 ha, valid.target_typed ho hb l.property.2⟩
  | inclusion =>
    rcases role with ⟨rfl, hb⟩
    exact ⟨l.property, l.property.1, l.property.2.trans hb⟩

/-- Construct the endpoint proofs from state validity and resolved declaration
roles; clients do not supply a static expression-agreement assertion. -/
def Resolution.ofRoles {s : Support} (valid : Structural.Valid m τ)
    (classes : s.Vertex → Fin n) (owners : s.Edge → Fin n)
    (classIds : ∀ v, s.classId v = m.id (classes v))
    (ownerIds : ∀ e, (s.mapRef e).owner = m.id (owners e))
    (roles : ∀ e, Role m (owners e) (classes (s.mapRef e).source)
      (classes (s.mapRef e).target) (s.mapRef e).kind) : Resolution m τ t s where
  classOf := classes
  owner := owners
  class_identity := classIds
  owner_identity := ownerIds
  typed e := role_typed m τ t valid (roles e)
  inclusion_source e he := by
    have h := roles e
    rw [he] at h
    exact h.1

namespace Resolution
variable {m τ t} {s : Support} (r : Resolution m τ t s)

def map {a b : s.Vertex} (e : s.Arrow a b) :
    Span ((τ.raw m.toEffectiveCore t).head (r.classOf a))
      ((τ.raw m.toEffectiveCore t).head (r.classOf b)) :=
  span m τ t (r.owner e.val) (s.mapRef e.val).kind (fun l =>
    ⟨by simpa only [e.property.1] using (r.typed e.val l).1,
      by simpa only [e.property.2] using (r.typed e.val l).2⟩)

def model : s.graph ⥤q semanticGraph.{u,0} U where
  obj a := (τ.raw m.toEffectiveCore t).head (r.classOf a)
  map := r.map

-- [proof->req~behavioral-reference-atoms~1]
theorem inclusion (e : s.Edge) (he : (s.mapRef e).kind = .inclusion) :
    Inclusion (r.map (s.arrow e)) := by
  apply span_inclusion
  · exact he
  · exact congrArg (τ.raw m.toEffectiveCore t).head (r.inclusion_source e he)

-- [impl->req~behavioral-reference-atoms~1]
def binding (ids : Function.Injective m.id) (R : IntegerRealization U)
    (integers : ∀ v, s.integer v = true → (τ.raw m.toEffectiveCore t).head (r.classOf v) = R.domain) :
    IntegerBinding.{u,0} s U where
  realization := R
  model := r.model
  same_id a b h := congrArg (τ.raw m.toEffectiveCore t).head
    (ids ((r.class_identity a).symm.trans (h.trans (r.class_identity b))))
  inclusion := r.inclusion
  integer_domain := integers

theorem relation (e : s.Edge) :
    ambientRelation (r.map (s.arrow e)) =
      {p | ∃ l : Link m τ t (r.owner e) (s.mapRef e).kind,
        source m τ t _ _ l = p.1 ∧ target m τ t _ _ l = p.2} := rfl

theorem dereference_relation (e : s.Edge) (he : (s.mapRef e).kind = .dereference) :
    ambientRelation (r.map (s.arrow e)) =
      {p | InheritedReference.deref m.family (τ.raw m.toEffectiveCore t) (r.owner e) p.1 p.2} := by
  rw [relation, he]
  simp only [Link, source, target]
  ext p
  constructor
  · rintro ⟨⟨⟨x, y⟩, h⟩, rfl, rfl⟩; exact h
  · intro h; exact ⟨⟨p, h⟩, rfl, rfl⟩

theorem target_relation (e : s.Edge) (he : (s.mapRef e).kind = .target) :
    ambientRelation (r.map (s.arrow e)) =
      {p | ∃ x, (τ.raw m.toEffectiveCore t).contains (r.owner e) p.1 x ∧
        InheritedReference.deref m.family (τ.raw m.toEffectiveCore t) (r.owner e) x p.2} := by
  rw [relation, he]
  simp only [Link, source, target]
  ext p
  constructor
  · rintro ⟨⟨⟨a, x, y⟩, hx, hy⟩, rfl, rfl⟩; exact ⟨x, hx, hy⟩
  · rintro ⟨x, hx, hy⟩; exact ⟨⟨⟨p.1, x, p.2⟩, hx, hy⟩, rfl, rfl⟩

theorem parent_relation (e : s.Edge) (he : (s.mapRef e).kind = .parent) :
    ambientRelation (r.map (s.arrow e)) =
      {p | p.1 ∈ (τ.raw m.toEffectiveCore t).head (r.owner e) ∧ τ.ParentAt t p.2 p.1} := by
  rw [relation, he]
  simp only [Link, source, target]
  ext p
  constructor
  · rintro ⟨⟨⟨a, x⟩, hx⟩, rfl, rfl⟩; exact hx
  · intro h; exact ⟨⟨⟨p.2, p.1⟩, h⟩, rfl, rfl⟩

-- [proof->req~behavioral-reference-atoms~1]
/-- Repeated map occurrences keep the same entire link carrier, not only an
equal relation reduct. Endpoint typing may use different support occurrences. -/
theorem coherent (ids : Function.Injective m.id) (R : IntegerRealization U)
    (integers : ∀ v, s.integer v = true → (τ.raw m.toEffectiveCore t).head (r.classOf v) = R.domain) :
    (r.binding ids R integers).Coherent := by
  intro e f ho hk
  have owner : r.owner e = r.owner f :=
    ids ((r.owner_identity e).symm.trans (ho.trans (r.owner_identity f)))
  refine ⟨⟨transport m τ t owner hk, ?_, ?_⟩⟩
  · intro l
    exact source_transport m τ t owner hk l
  · intro l
    exact target_transport m τ t owner hk l

theorem static_agreement (ids : Function.Injective m.id) (R : IntegerRealization U)
    (integers : ∀ v, s.integer v = true → (τ.raw m.toEffectiveCore t).head (r.classOf v) = R.domain)
    {Γ ty} (e : Expr s Γ ty) (ρ : Behavioral.Environment U Γ.length)
    (σ : Constraints.Environment s U Γ) (same : CapturedStatic.Compatible ρ σ)
    (present : ρ.this ∈ τ.live t) :
    CapturedStatic.eval (τ.live t) (r.binding ids R integers) e ρ =
      e.denote (r.binding ids R integers) σ :=
  CapturedStatic.agrees _ _ _ _ _ same present

end Resolution
end Clafer.Behavioral.StructuralBinding
