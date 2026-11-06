module

public import Clafer.Behavioral.InheritedReference
public import Clafer.Behavioral.GroupObservation

/-!
# Structural meaning for the behavioral profile

SoSyM §5.3.4–5, §5.5 and Appendix 5; behavioral §5 Definitions 1–3,
with 0.5.7 S3/S4/S6/S7/S9 and T8/T11. Authored abstract types, ordinary
inherited fields and reference targets are distinct. The old effective-core
admission predicate is deliberately not used for this larger source domain.
-/

@[expose] public section
namespace Clafer.Behavioral.Structural
open Semantics MCS DPGraph.Predicates

universe u

-- [impl->req~behavioral-structural-compatibility~1]
/-- Effective bounds are supplied by elaboration; authored abstractness is
retained, never reconstructed from the effective flag. References are declared
annotations, with nearest-owner lookup provided by `InheritedReference.Owner`. -/
structure Core (n : Nat) extends EffectiveCore n where
  authoredAbstract : Fin n → Bool

namespace Core
variable {n : Nat} (m : Core n)

/-- Resolved 0.5.7 structural admission. The frontend owns names/defaults and
primitive promotions. Here reference targets are explicit declaration views. -/
structure WellFormed : Prop where
  root_origin : ∀ d, m.family.origin d = .syntheticRoot ↔ d = m.family.root
  root_shape : m.family.parent m.family.root = none ∧
    m.family.reference m.family.root = .basic ∧ m.family.super m.family.root = none ∧
    m.authoredAbstract m.family.root = false ∧ m.family.isAbstract m.family.root = false
  primitive_shape : ∀ d p, m.family.origin d = .primitive p →
    m.family.parent d = some m.family.root ∧ m.family.reference d = .basic ∧
    m.family.super d = none
  unique_primitive : ∀ d e p, m.family.origin d = .primitive p →
    m.family.origin e = .primitive p → d = e
  authored_effective : ∀ d, m.authoredAbstract d = true → m.family.isAbstract d = true
  parentless_abstract : ∀ d, m.family.parent d = none → d ≠ m.family.root →
    m.authoredAbstract d = true
  refined_parent : ∀ d s p, m.family.super d = some s → m.family.parent s = some p →
    ∃ q, m.family.parent d = some q ∧ m.toEffectiveCore.Ancestor q p
  reference_refinement : ∀ d s o a b,
    m.family.super d = some s → InheritedReference.Owner m.family s o →
    (m.family.reference d).target = some a → (m.family.reference o).target = some b →
    m.toEffectiveCore.Ancestor a b ∧
      (m.family.reference d).kind.CanExtend (m.family.reference o).kind
  parent_rank : ∃ rank : Fin n → Nat, ∀ d p, m.family.parent d = some p → rank p < rank d
  super_rank : ∃ rank : Fin n → Nat, ∀ d s, m.family.super d = some s → rank s < rank d
  ids : Function.Injective m.id
  multiplicity_bounds : ∀ d, ValidRange (m.family.multiplicity d)
  group_bounds : ∀ d, ValidRange (m.group d)
  group_agrees : ∀ d, m.group d = (m.family.group d).effective.range

/-- Embedding of effective input does not enlarge its historical admission. -/
def ofEffective (m : EffectiveCore n) : Core n := ⟨m, m.family.isAbstract⟩

end Core

variable {n : Nat} {U : Type u} (m : Core n) (τ : Trace (Fin n) U)

-- [impl->req~behavioral-structural-compatibility~1]
structure IdentitiesValid : Prop where
  root_type : τ.identities.directType τ.identities.root = m.family.root
  root_only : ∀ x, τ.identities.directType x = m.family.root → x = τ.identities.root
  concrete : ∀ x, m.authoredAbstract (τ.identities.directType x) = false
  root_parent : τ.identities.parent τ.identities.root = none
  parent_exists : ∀ x, x ≠ τ.identities.root → ∃ p, τ.identities.parent x = some p
  parent_typed : ∀ x p, τ.identities.parent x = some p →
    ∃ c, m.family.parent (τ.identities.directType x) = some c ∧
      m.toEffectiveCore.Ancestor (τ.identities.directType p) c

def Abstracts (t : Nat) : Prop :=
  ∀ d, m.authoredAbstract d = true →
    (∀ x, x ∈ (τ.raw m.toEffectiveCore t).head d →
      ∃ c, m.family.super c = some d ∧ x ∈ (τ.raw m.toEffectiveCore t).head c) ∧
    (∀ c e, m.family.super c = some d → m.family.super e = some d → c ≠ e →
      ∀ x, ¬ (x ∈ (τ.raw m.toEffectiveCore t).head c ∧
        x ∈ (τ.raw m.toEffectiveCore t).head e))

def Groups (t : Nat) : Prop := ∀ d, m.authoredAbstract d = false →
  Semantics.Groups.Holds m.family (τ.raw m.toEffectiveCore t) d

-- [impl->req~behavioral-reference-atoms~1]
/-- One source link per head (behavioral Definition 2), even when reference
annotations are refined. Invalid raw links remain visible to typedness. -/
def ReferenceCoherent (t : Nat) : Prop :=
  ∀ d e x y z, τ.deref t d x y → τ.deref t e x z → y = z

/-- Set uniqueness is scoped by the declaration's containment fiber. A
parentless abstract does not merge separate concrete child declarations into
one set. Inherited reference kinds apply to their existing subtype heads. -/
def Keys (t : Nat) : Prop :=
  ∀ d o, InheritedReference.Owner m.family d o →
    (m.family.reference o).kind = .referenceSet →
    ∀ p y x z, (τ.raw m.toEffectiveCore t).contains d p x →
      InheritedReference.deref m.family (τ.raw m.toEffectiveCore t) d x y →
      (τ.raw m.toEffectiveCore t).contains d p z →
      InheritedReference.deref m.family (τ.raw m.toEffectiveCore t) d z y → x = z

-- [impl->req~behavioral-structural-compatibility~1]
structure StateValid (t : Nat) : Prop where
  typed : (τ.raw m.toEffectiveCore t).Typed m.toEffectiveCore
  root_head : ∀ x, x ∈ (τ.raw m.toEffectiveCore t).head m.family.root ↔ x = τ.identities.root
  root_separate : ∀ d, d ≠ m.family.root → τ.identities.root ∉ (τ.raw m.toEffectiveCore t).head d
  inherits : (τ.raw m.toEffectiveCore t).Inherits m.toEffectiveCore
  abstracts : Abstracts m τ t
  parents : (τ.raw m.toEffectiveCore t).Parents m.toEffectiveCore
  references : (τ.raw m.toEffectiveCore t).References m.toEffectiveCore
  coherent : ReferenceCoherent τ t
  keys : Keys m τ t
  multiplicities : (τ.raw m.toEffectiveCore t).Multiplicities m.toEffectiveCore
  groups : Groups m τ t
  disjoint : (τ.raw m.toEffectiveCore t).DeclarationDisjoint m.toEffectiveCore
  /-- Definition 2 requires an actual containment tree; local typing alone
  must not admit an orphan component or a containment cycle. -/
  reachable : ∀ x ∈ τ.live t, (τ.raw m.toEffectiveCore t).Reaches x

structure Valid : Prop where
  identities : IdentitiesValid m τ
  root_live : ∀ t, τ.identities.root ∈ τ.live t
  parent_live : ∀ t x p, x ∈ τ.live t → τ.identities.parent x = some p → p ∈ τ.live t
  states : ∀ t, StateValid m τ t

def Admissible : Prop := m.WellFormed ∧ Valid m τ

namespace Valid
variable {m τ} (h : Valid m τ)
include h

-- [proof->req~behavioral-reference-atoms~1]
theorem inherited_reference {t : Nat} {d o : Fin n}
    (owner : InheritedReference.Owner m.family d o) {x : U}
    (hx : x ∈ (τ.raw m.toEffectiveCore t).head d) :
    ∃! y, InheritedReference.deref m.family (τ.raw m.toEffectiveCore t) d x y := by
  obtain ⟨c, hc⟩ := owner.target
  have ho : x ∈ (τ.raw m.toEffectiveCore t).head o := ⟨hx.1, hx.2.trans owner.ancestor⟩
  obtain ⟨y, hy, unique⟩ := (h.states t).references o c hc x ho
  refine ⟨y, (InheritedReference.deref_owner owner x y).mpr ⟨hx, hy⟩, ?_⟩
  intro z hz
  exact unique z ((InheritedReference.deref_owner owner x z).mp hz).2

theorem target_typed {t : Nat} {d o c : Fin n}
    (owner : InheritedReference.Owner m.family d o)
    (target : (m.family.reference o).target = some c) {x y : U}
    (link : InheritedReference.deref m.family (τ.raw m.toEffectiveCore t) d x y) :
    y ∈ (τ.raw m.toEffectiveCore t).head c := by
  have rawLink := ((InheritedReference.deref_owner owner x y).mp link).2
  obtain ⟨_, c', hc', hy⟩ := (h.states t).typed.2 o x y rawLink
  have he : c' = c := Option.some.inj (hc'.symm.trans target)
  exact he ▸ hy

theorem target_live {t : Nat} {d : Fin n} {x y : U}
    (link : InheritedReference.deref m.family (τ.raw m.toEffectiveCore t) d x y) :
    y ∈ τ.live t := by
  obtain ⟨o, owner, hx, hy⟩ := link
  obtain ⟨c, hc⟩ := owner.target
  exact (h.target_typed owner hc ⟨o, owner, hx, hy⟩).1

theorem refined_reference_agrees {t : Nat} {d e : Fin n} {x y z : U}
    (hd : InheritedReference.deref m.family (τ.raw m.toEffectiveCore t) d x y)
    (he : InheritedReference.deref m.family (τ.raw m.toEffectiveCore t) e x z) : y = z := by
  obtain ⟨o, _, _, hy⟩ := hd
  obtain ⟨p, _, _, hz⟩ := he
  exact (h.states t).coherent o p x y z hy hz

theorem finite_targets {t : Nat} {d : Fin n}
    (finite : ((τ.raw m.toEffectiveCore t).head d).Finite) :
    {y | ∃ x, InheritedReference.deref m.family (τ.raw m.toEffectiveCore t) d x y}.Finite := by
  classical
  apply Set.Finite.subset (finite.biUnion (t := fun x =>
    {y | InheritedReference.deref m.family (τ.raw m.toEffectiveCore t) d x y}) (fun x _ => ?_))
  · intro y hy
    obtain ⟨x, link⟩ := hy
    exact Set.mem_iUnion₂.mpr ⟨x, link.choose_spec.2.1, link⟩
  · apply Set.Subsingleton.finite
    intro y hy z hz
    exact h.refined_reference_agrees hy hz

end Valid

/-- Context views restrict the same child occurrences and actual parent. -/
def View (t : Nat) (d q : Fin n) : Set U :=
  {x | x ∈ (τ.raw m.toEffectiveCore t).head d ∧
    ∃ p, (τ.raw m.toEffectiveCore t).contains d p x ∧ p ∈ (τ.raw m.toEffectiveCore t).head q}

-- [proof->req~behavioral-structural-compatibility~1]
theorem view_same_parent {t : Nat} {d q r : Fin n} {p x : U}
    (hq : p ∈ (τ.raw m.toEffectiveCore t).head q)
    (hr : p ∈ (τ.raw m.toEffectiveCore t).head r) :
    (p ∈ (τ.raw m.toEffectiveCore t).head q ∧ (τ.raw m.toEffectiveCore t).contains d p x) ↔
      (p ∈ (τ.raw m.toEffectiveCore t).head r ∧ (τ.raw m.toEffectiveCore t).contains d p x) := by
  simp only [hq, hr]

theorem view_parent_unique {t : Nat} {d e : Fin n} {p q x : U}
    (hp : (τ.raw m.toEffectiveCore t).contains d p x)
    (hq : (τ.raw m.toEffectiveCore t).contains e q x) : p = q :=
  τ.parent_stable hp.1 hq.1

-- [proof->req~behavioral-structural-compatibility~1]
theorem view_covers (h : Valid m τ) {t : Nat} {d p : Fin n}
    (parent : m.family.parent d = some p) {x : U}
    (member : x ∈ (τ.raw m.toEffectiveCore t).head d) : x ∈ View m τ t d p := by
  obtain ⟨q, hq, _⟩ := (h.states t).parents d p parent x member
  obtain ⟨_, c, hc, hqc⟩ := (h.states t).typed.1 d q x hq
  have he : c = p := Option.some.inj (hc.symm.trans parent)
  exact ⟨member, q, hq, he ▸ hqc⟩

theorem Valid.top_level_parent (h : Valid m τ) {t : Nat} {x p : U}
    (hp : τ.ParentAt t p x)
    (top : m.family.parent (τ.identities.directType x) = some m.family.root) :
    p = τ.identities.root := by
  obtain ⟨c, hc, hpc⟩ := h.identities.parent_typed x p hp.2.2
  have he : c = m.family.root := Option.some.inj (hc.symm.trans top)
  subst c
  exact ((h.states t).root_head p).mp ⟨hp.1, hpc⟩

theorem Valid.context_parent_present (h : Valid m τ) {t : Nat} {x : U}
    (live : x ∈ τ.live t) : x = τ.identities.root ∨
      ∃ p, τ.identities.parent x = some p ∧ p ∈ τ.live t := by
  by_cases root : x = τ.identities.root
  · exact Or.inl root
  · obtain ⟨p, hp⟩ := h.identities.parent_exists x root
    exact Or.inr ⟨p, hp, h.parent_live t x p live hp⟩

end Clafer.Behavioral.Structural
