module

public import Clafer.Semantics.Bridge

-- [proof->req~clafer-structural-satisfaction~1]

/-!
# Normalizing interpreted structural models

SoSyM B.1–B.5 and §6.2.4–5. An arbitrary model of the selected local bank
has a relational representative. Ordinary defaults justify reduction; inverse,
triangle and inclusion declarations determine the remaining maps up to link
isomorphism. No model-to-checker equivalence is assumed.
-/

@[expose] public section
namespace Clafer.Semantics
open CategoryTheory DPGraph DPGraph.Predicates MCS Compile

variable {n : Nat} {U : Type} (m : EffectiveCore n)

namespace SpanModel
variable (g : m.family.canonicalRoles.graph ⥤q semanticGraph.{0,0} U)

def extent (d : Fin n) : Set U := g.obj d

/-- Read a declared ordinary role with its actual interpreted link carrier. -/
def map (d : Fin n) (r : Clafer.Roles.Map (m.family.shape d).kind
    (m.family.shape d).hasParent) := g.map (LocalId.edge (.ordinary d r))

noncomputable def head (d : Fin n) :
    Span (extent m g ((m.family.parent d).getD d)) (extent m g d) :=
  if hp : (m.family.shape d).hasParent = true then map m g d ⟨.head, hp⟩
  else Span.ofRelation (fun _ _ => False)

noncomputable def deref (d : Fin n) :
    Span (extent m g d) (extent m g ((m.family.reference d).target.getD d)) :=
  if hr : (m.family.shape d).kind ≠ .basic then
    map m g d ⟨.dereference, by simpa [Clafer.Roles.mapPresent] using hr⟩
  else Span.ofRelation (fun _ _ => False)

theorem head_active (d : Fin n) (hp : (m.family.shape d).hasParent = true) :
    head m g d = map m g d ⟨.head, hp⟩ := dite_eq_left hp

theorem deref_active (d : Fin n) (hr : (m.family.shape d).kind ≠ .basic) :
    deref m g d = map m g d ⟨.dereference, by simpa [Clafer.Roles.mapPresent] using hr⟩ :=
  dite_eq_left hr

theorem head_inactive (d : Fin n) (hp : ¬ (m.family.shape d).hasParent = true) :
    head m g d = Span.ofRelation (fun _ _ => False) := dite_eq_right hp

theorem deref_inactive (d : Fin n) (hr : ¬ (m.family.shape d).kind ≠ .basic) :
    deref m g d = Span.ofRelation (fun _ _ => False) := dite_eq_right hr

def ambient {A B : Set U} (q : Span A B) (x y : U) : Prop :=
  ∃ hx : x ∈ A, ∃ hy : y ∈ B, q.red ⟨x, hx⟩ ⟨y, hy⟩

@[simp] theorem ambient_subtype {A B : Set U} (q : Span A B) (x : A) (y : B) :
    ambient q x.val y.val ↔ q.red x y := by
  constructor
  · rintro ⟨_, _, h⟩; exact h
  · intro h; exact ⟨x.property, y.property, h⟩

noncomputable def normalize (root : U) : Configuration (Fin n) U where
  root := root
  head := extent m g
  contains d := ambient (head m g d)
  deref d := ambient (deref m g d)

variable (root : U)

theorem typed : (normalize m g root).Typed m := by
  constructor
  · intro d p x h
    obtain ⟨hp, hx, he⟩ := h
    refine ⟨hx, ?_⟩
    by_cases hh : (m.family.shape d).hasParent = true
    · exact ⟨_, Configuration.parent_present m d hh, hp⟩
    · simp [head, hh, Span.red_ofRelation] at he
  · intro d x t h
    obtain ⟨hx, ht, he⟩ := h
    refine ⟨hx, ?_⟩
    by_cases hh : (m.family.shape d).kind ≠ .basic
    · exact ⟨_, Configuration.target_present m d hh, ht⟩
    · simp [deref, hh, Span.red_ofRelation] at he

@[simp] theorem normalized_head (d : Fin n) :
    (normalize m g root).headMap m d = Span.ofRelation (head m g d).red := by
  unfold Configuration.headMap normalize
  congr 1
  funext p x
  exact propext (ambient_subtype _ p x)

@[simp] theorem normalized_deref (d : Fin n) :
    (normalize m g root).derefMap m d = Span.ofRelation (deref m g d).red := by
  unfold Configuration.derefMap normalize
  congr 1
  funext x t
  exact propext (ambient_subtype _ x t)

variable (model : (interpretation U).IsModel (localFormulas m.family).diagram g)

include model in
theorem holds (l : LocalId m.family) :
    (interpretation U).Satisfies g l.formula := model _ ⟨l, rfl⟩

include model in
theorem head_setValued (d : Fin n) : SetValued (head m g d) := by
  by_cases hp : (m.family.shape d).hasParent = true
  · rw [head_active m g d hp]
    exact holds m g model (.setValued d ⟨.head, hp⟩ (by cases (m.family.shape d).kind <;> rfl))
  · rw [head_inactive m g d hp]
    exact Span.ofRelation_jointlyInjective _

include model in
theorem deref_setValued (d : Fin n) : SetValued (deref m g d) := by
  by_cases hr : (m.family.shape d).kind ≠ .basic
  · rw [deref_active m g d hr]
    exact holds m g model (.setValued d ⟨.dereference, _⟩ (by
        change Clafer.Roles.mode (m.family.shape d).kind .dereference = .ordinary
        cases (m.family.shape d).kind <;> rfl))
  · rw [deref_inactive m g d hr]
    exact Span.ofRelation_jointlyInjective _

noncomputable def headIso (d : Fin n) :
    Span.Iso (head m g d) ((normalize m g root).headMap m d) := by
  rw [normalized_head]
  exact (head m g d).relationIso (head_setValued m g model d)

noncomputable def derefIso (d : Fin n) :
    Span.Iso (deref m g d) ((normalize m g root).derefMap m d) := by
  rw [normalized_deref]
  exact (deref m g d).relationIso (deref_setValued m g model d)

noncomputable def parentIso (d : Fin n) (hp : (m.family.shape d).hasParent = true) :
    Span.Iso (map m g d ⟨.parent, hp⟩) ((normalize m g root).headMap m d).inverse := by
  have h : Inverse (map m g d ⟨.head, hp⟩) (map m g d ⟨.parent, hp⟩) :=
    holds m g model (.inverse d hp)
  have e := Classical.choice h
  have he : head m g d = map m g d ⟨.head, hp⟩ := head_active m g d hp
  rw [← he] at e
  exact e.symm.trans (headIso m g root model d).inverse

noncomputable def targetIso (d : Fin n) (hp : (m.family.shape d).hasParent = true)
    (hr : (m.family.shape d).kind ≠ .basic) :
    Span.Iso (map m g d ⟨.target, by simp [Clafer.Roles.mapPresent, hp, hr]⟩)
      ((normalize m g root).targetMap m d) := by
  have h : Commutation (map m g d ⟨.head, hp⟩)
      (map m g d ⟨.dereference, by simpa [Clafer.Roles.mapPresent] using hr⟩)
      (map m g d ⟨.target, by simp [Clafer.Roles.mapPresent, hp, hr]⟩) :=
    holds m g model (.commutation d hp hr)
  have e := Classical.choice h
  have he : head m g d = map m g d ⟨.head, hp⟩ := head_active m g d hp
  have hd : deref m g d = map m g d ⟨.dereference, by simpa [Clafer.Roles.mapPresent] using hr⟩ :=
    deref_active m g d hr
  rw [← he, ← hd] at e
  exact e.symm.trans ((headIso m g root model d).comp (derefIso m g root model d))

export DPGraph.Predicates (inclusionIso)

/-- The actual interpreted inheritance role is normalized simultaneously with
the ordinary, inverse and composite maps. -/
noncomputable def inheritedIso (d e : Fin n) (he : m.family.super d = some e) :
    Span.Iso (g.map (LocalId.edge (.inclusion ⟨d, e, Shape.headInclusion _ _, he⟩)))
      ((normalize m g root).inclusionMap m ⟨d, e, Shape.headInclusion _ _, he⟩) :=
  inclusionIso _ (holds m g model (.inclusion ⟨d, e, Shape.headInclusion _ _, he⟩))

include model in
theorem local_conditions (wf : m.WellFormed) (support : m.Supported) :
    (normalize m g root).LocalConditions m := by
  let s := normalize m g root
  have typed := typed m g root
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d e he
    have h : Inclusion (g.map (LocalId.edge (.inclusion
        ⟨d, e, Shape.headInclusion _ _, he⟩))) :=
      holds m g model (.inclusion ⟨d, e, Shape.headInclusion _ _, he⟩)
    exact inclusion_subset h
  · intro d p hp
    have hh : (m.family.shape d).hasParent = true := by simp [Family.shape, hp]
    apply (s.parent_one_iff m typed d p hp).mp
    exact (targetMultiplicity_iff one (parentIso m g root model d hh)).mp
      (holds m g model (.multiplicity d ⟨.parent, hh⟩))
  · intro d t ht
    have hr : (m.family.shape d).kind ≠ .basic := by
      cases h : m.family.reference d <;> simp_all [Family.shape, ReferenceTo.kind, ReferenceTo.target]
    apply (s.deref_one_iff m typed d t ht).mp
    apply (targetMultiplicity_iff one (derefIso m g root model d)).mp
    rw [deref_active m g d hr]
    exact holds m g model (.multiplicity d ⟨.dereference, _⟩)
  · intro d hk p t x y hpx hxt hpy hyt
    have hr : (m.family.shape d).kind ≠ .basic := by simp [Family.shape, hk]
    have hp := Configuration.reference_has_parent m wf support d hr
    have sv : SetValued (s.targetMap m d) :=
      (setValued_iff (targetIso m g root model d hp hr)).mp
        (holds m g model (.setValued d ⟨.target, by simp [Clafer.Roles.mapPresent, hp, hr]⟩
          (by simp [Clafer.Roles.mode, Family.shape, hk])))
    have xp := typed.1 d p x hpx
    have yp := typed.1 d p y hpy
    have xt := typed.2 d x t hxt
    have pt : p ∈ s.head ((m.family.parent d).getD d) := by
      obtain ⟨c, hc, h⟩ := xp.2; simpa [hc] using h
    have tt : t ∈ s.head ((m.family.reference d).target.getD d) := by
      obtain ⟨c, hc, h⟩ := xt.2; simpa [hc] using h
    let l : (s.targetMap m d).Link :=
      ⟨(⟨(⟨p, pt⟩, ⟨x, xp.1⟩), hpx⟩, ⟨(⟨x, xp.1⟩, ⟨t, tt⟩), hxt⟩), rfl⟩
    let k : (s.targetMap m d).Link :=
      ⟨(⟨(⟨p, pt⟩, ⟨y, yp.1⟩), hpy⟩, ⟨(⟨y, yp.1⟩, ⟨t, tt⟩), hyt⟩), rfl⟩
    exact congrArg (fun z => z.val.1.val.2.val) (sv (a₁ := l) (a₂ := k) rfl)
  · intro d p hp
    have hh : (m.family.shape d).hasParent = true := by simp [Family.shape, hp]
    apply (s.head_multiplicity_iff m typed d p hp).mp
    apply (targetMultiplicity_iff _ (headIso m g root model d)).mp
    rw [head_active m g d hh]
    exact holds m g model (.multiplicity d ⟨.head, hh⟩)

include model in
/-- Global obligations are explicit additions to the exact local Compile bank.
This normalization theorem covers arbitrary link carriers, not just candidates. -/
theorem normalize_satisfies (wf : m.WellFormed) (support : m.Supported)
    (global : (normalize m g root).GlobalConditions m) :
    StructuralSatisfies m (normalize m g root) :=
  ((normalize m g root).structural_split m).mpr
    ⟨typed m g root, global, local_conditions m g root model wf support⟩

end SpanModel
end Clafer.Semantics
