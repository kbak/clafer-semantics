module

public import Clafer.Compile.EffectiveCore
public import Clafer.Semantics.Relational

/-!
[impl->req~clafer-structural-satisfaction~1]
[proof->req~clafer-effective-core~1]
[proof->req~clafer-structural-satisfaction~1]
-/

/-!
# Correspondence with the selected compiled structural diagram

SoSyM §6.2.4–5, B.4–B.5. The local bank is exactly `Compile.localFormulas`,
not a caller-supplied equivalent specification. Global root, abstract and group
clauses supplement that bank; no claim is made that local Shapes generate them.
-/

@[expose] public section
namespace Clafer.Semantics
open CategoryTheory DPGraph DPGraph.Predicates MCS Compile

namespace Configuration
variable {n : Nat} {U : Type} (m : EffectiveCore n) (s : Configuration (Fin n) U)

theorem parent_present (d : Fin n) (h : (m.family.shape d).hasParent = true) :
    m.family.parent d = some ((m.family.parent d).getD d) := by
  cases hp : m.family.parent d <;> simp_all [Family.shape]

theorem target_present (d : Fin n) (h : (m.family.shape d).kind ≠ .basic) :
    (m.family.reference d).target = some ((m.family.reference d).target.getD d) := by
  cases hr : m.family.reference d <;> simp_all [Family.shape, ReferenceTo.kind, ReferenceTo.target]

theorem target_setValued (keys : s.Keys m) (d : Fin n)
    (hk : (m.family.reference d).kind = .referenceSet) : SetValued (s.targetMap m d) := by
  rintro l k he
  have hp : l.val.1.val.1.val = k.val.1.val.1.val :=
    congrArg (fun z => z.1.val) he
  have ht : l.val.2.val.2.val = k.val.2.val.2.val :=
    congrArg (fun z => z.2.val) he
  have hl : l.val.1.val.2.val = l.val.2.val.1.val := congrArg Subtype.val l.property
  have hk' : k.val.1.val.2.val = k.val.2.val.1.val := congrArg Subtype.val k.property
  have hx := keys d hk l.val.1.val.1.val l.val.2.val.2.val
    l.val.1.val.2.val k.val.1.val.2.val l.val.1.property
    (hl.symm ▸ l.val.2.property) (hp.symm ▸ k.val.1.property)
    (hk'.symm ▸ ht.symm ▸ k.val.2.property)
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext (Prod.ext (Subtype.ext hp) (Subtype.ext hx))
  · exact Subtype.ext (Prod.ext (Subtype.ext (hl.symm.trans (hx.trans hk')))
      (Subtype.ext ht))

theorem key_local_iff (typed : s.Typed m) (parents : s.Parents m)
    (refs : s.References m) (d : Fin n)
    (hk : (m.family.shape d).kind = .referenceSet)
    (hp : (m.family.shape d).hasParent = true) :
    (interpretation U).Satisfies (s.interpret m) (LocalId.formula (.key d hk hp)) ↔
      ∀ p t x y, s.contains d p x → s.deref d x t →
        s.contains d p y → s.deref d y t → x = y := by
  let q := fun j => ((LocalId.formula (.key d hk hp)).binding.comp
    (s.interpret m)).map (Arity.OutEdge.edge j)
  have po := (s.parent_one_iff m typed d _ (parent_present m d hp)).mpr
    (parents d _ (parent_present m d hp))
  have hr : (m.family.shape d).kind ≠ .basic := by simp [hk]
  have ro := (s.deref_one_iff m typed d _ (target_present m d hr)).mpr
    (refs d _ (target_present m d hr))
  have ht : ∀ j, Total (q j) := by
    intro j; fin_cases j
    · exact ((one_iff_total_single _).mp po).1
    · exact ((one_iff_total_single _).mp ro).1
  have hs : ∀ j, SingleValued (q j) := by
    intro j; fin_cases j
    · exact ((one_iff_total_single _).mp po).2
    · exact ((one_iff_total_single _).mp ro).2
  change Key q ↔ _
  rw [two_key_iff q ht hs]
  have ptype : ∀ p x, s.contains d p x → p ∈ s.head ((m.family.parent d).getD d) := by
    intro p x h
    obtain ⟨_, c, hc, he⟩ := typed.1 d p x h
    simpa [hc] using he
  have ttype : ∀ x t, s.deref d x t →
      t ∈ s.head ((m.family.reference d).target.getD d) := by
    intro x t h
    obtain ⟨_, c, hc, he⟩ := typed.2 d x t h
    simpa [hc] using he
  constructor
  · intro h p t x y hpx hxt hpy hyt
    have hx := (typed.1 d p x hpx).1
    have hy := (typed.1 d p y hpy).1
    apply congrArg Subtype.val (h ⟨x, hx⟩ ⟨y, hy⟩
      ⟨p, ptype p x hpx⟩ ⟨t, ttype x t hxt⟩ _ _ _ _)
    · exact ⟨⟨(_, _), hpx⟩, rfl, rfl⟩
    · exact ⟨⟨(_, _), hxt⟩, rfl, rfl⟩
    · exact ⟨⟨(_, _), hpy⟩, rfl, rfl⟩
    · exact ⟨⟨(_, _), hyt⟩, rfl, rfl⟩
  · intro h x y p t hpx hxt hpy hyt
    apply Subtype.ext
    apply h p.val t.val x.val y.val
    · change (s.headMap m d).inverse.red x p at hpx
      simpa only [headMap, Span.red_ofRelation] using (Span.red_inverse _ _ _).mp hpx
    · change (s.derefMap m d).red x t at hxt
      simpa only [derefMap, Span.red_ofRelation] using hxt
    · change (s.headMap m d).inverse.red y p at hpy
      simpa only [headMap, Span.red_ofRelation] using (Span.red_inverse _ _ _).mp hpy
    · change (s.derefMap m d).red y t at hyt
      simpa only [derefMap, Span.red_ofRelation] using hyt

def LocalConditions : Prop :=
  s.Inherits m ∧ s.Parents m ∧ s.References m ∧ s.Keys m ∧ s.Multiplicities m

def GlobalConditions : Prop :=
  s.Rooted m ∧ s.Abstracts m ∧ s.Groups m ∧ s.DeclarationDisjoint m

theorem structural_split : StructuralSatisfies m s ↔
    s.Typed m ∧ s.GlobalConditions m ∧ s.LocalConditions m := by
  unfold StructuralSatisfies GlobalConditions LocalConditions
  tauto

theorem local_model (support : m.Supported) (typed : s.Typed m)
    (h : s.LocalConditions m) :
    (interpretation U).IsModel (localFormulas m.family).diagram (s.interpret m) := by
  have po (d) (hp : (m.family.shape d).hasParent = true) :
      TargetMultiplicity Clafer.one (s.headMap m d).inverse :=
    (s.parent_one_iff m typed d _ (parent_present m d hp)).mpr
      (h.2.1 d _ (parent_present m d hp))
  have ro (d) (hr : (m.family.shape d).kind ≠ .basic) :
      TargetMultiplicity Clafer.one (s.derefMap m d) :=
    (s.deref_one_iff m typed d _ (target_present m d hr)).mpr
      (h.2.2.1 d _ (target_present m d hr))
  have mo (d) (hp : (m.family.shape d).hasParent = true) :
      TargetMultiplicity (m.family.multiplicity d) (s.headMap m d) :=
    (s.head_multiplicity_iff m typed d _ (parent_present m d hp)).mpr
      (h.2.2.2.2 d _ (parent_present m d hp))
  rintro φ ⟨l, rfl⟩
  cases l with
  | setValued d r ordinary =>
    change SetValued (s.ordinaryMap m d r)
    rcases r with ⟨r, present⟩
    cases r with
    | head => exact s.headMap_setValued m d
    | parent => exact (setValued_inverse _).mpr (s.headMap_setValued m d)
    | dereference => exact s.derefMap_setValued m d
    | target =>
      apply s.target_setValued m h.2.2.2.1 d
      cases hk : (m.family.shape d).kind with
      | basic => simp [Clafer.Roles.mapPresent, hk] at present
      | referenceBag => simp [Clafer.Roles.mode, hk] at ordinary
      | referenceSet => exact hk
  | multiplicity d r =>
    change TargetMultiplicity (LocalId.range d r) (s.ordinaryMap m d r)
    rcases r with ⟨r, present⟩
    cases r with
    | head => exact mo d present
    | parent => exact po d present
    | dereference =>
      exact ro d (by simpa [Clafer.Roles.mapPresent] using present)
    | target =>
      have hp : (m.family.shape d).hasParent = true :=
        (by simpa only [Clafer.Roles.mapPresent, Bool.and_eq_true] using present :
          (m.family.shape d).hasParent = true ∧ ((m.family.shape d).kind != .basic) = true).1
      have hr : (m.family.shape d).kind ≠ .basic := by
        exact (by simpa only [Clafer.Roles.mapPresent, Bool.and_eq_true, bne_iff_ne] using present :
          (m.family.shape d).hasParent = true ∧ (m.family.shape d).kind ≠ .basic).2
      have hr' := (one_iff_total_single _).mp (ro d hr)
      exact (composite_multiplicity _ _ hr'.1 hr'.2 _).mpr (mo d hp)
  | inclusion r =>
    rcases r with ⟨d, e, ⟨⟨role, sub, sup⟩, edge⟩⟩
    have he := support.2.2.1 d e edge
    have he' := support.2.1 e he.1
    cases role with
    | head =>
      change Inclusion (Span.ofRelation (fun (a : s.head d) (b : s.head e) => a.val = b.val))
      exact (identity_inclusion_iff _ _).mpr (h.1 d e edge)
    | source => simp [Clafer.Roles.classPresent, Family.shape, he'.1] at sup
    | target => simp [Clafer.Roles.classPresent, Family.shape, he'.2.1, ReferenceTo.kind] at sup
  | inverse d hp =>
    change Inverse (s.headMap m d) (s.headMap m d).inverse
    exact s.parent_inverse m d
  | commutation d hp hr =>
    change Commutation (s.headMap m d) (s.derefMap m d) (s.targetMap m d)
    exact s.target_commutes m d
  | key d hk hp =>
    exact (s.key_local_iff m typed h.2.1 h.2.2.1 d hk hp).mpr (h.2.2.2.1 d hk)

theorem reference_has_parent (wf : m.WellFormed) (support : m.Supported)
    (d : Fin n) (hr : (m.family.shape d).kind ≠ .basic) :
    (m.family.shape d).hasParent = true := by
  cases hp : m.family.parent d with
  | some p => simp [Family.shape, hp]
  | none =>
    by_cases hd : d = m.family.root
    · subst d
      exact (hr (by simp [Family.shape, wf.1.root_shape.2.1, ReferenceTo.kind])).elim
    · have hab := wf.1.parentless_abstract d hp hd
      exact (hr (by simp [Family.shape, (support.2.1 d hab).2.1, ReferenceTo.kind])).elim

theorem local_model_iff (wf : m.WellFormed) (support : m.Supported) (typed : s.Typed m) :
    (interpretation U).IsModel (localFormulas m.family).diagram (s.interpret m) ↔
      s.LocalConditions m := by
  refine ⟨?_, s.local_model m support typed⟩
  intro model
  have holds (l : LocalId m.family) := model _ ⟨l, rfl⟩
  have parents : s.Parents m := by
    intro d p hp
    have hd : (m.family.shape d).hasParent = true := by simp [Family.shape, hp]
    exact (s.parent_one_iff m typed d p hp).mp (holds (.multiplicity d ⟨.parent, hd⟩))
  have refs : s.References m := by
    intro d t ht
    have hr : (m.family.shape d).kind ≠ .basic := by
      cases hr : m.family.reference d <;>
        simp_all [Family.shape, ReferenceTo.kind, ReferenceTo.target]
    have hd : Clafer.Roles.mapPresent (m.family.shape d).kind
        (m.family.shape d).hasParent .dereference = true := by
      simpa [Clafer.Roles.mapPresent] using hr
    exact (s.deref_one_iff m typed d t ht).mp (holds (.multiplicity d ⟨.dereference, hd⟩))
  refine ⟨?_, parents, refs, ?_, ?_⟩
  · intro d e he
    exact (identity_inclusion_iff _ _).mp
      (holds (.inclusion ⟨d, e, Shape.headInclusion _ _, he⟩))
  · intro d hd
    have hr : (m.family.shape d).kind ≠ .basic := by simp [Family.shape, hd]
    have hp := reference_has_parent m wf support d hr
    exact (s.key_local_iff m typed parents refs d hd hp).mp (holds (.key d hd hp))
  · intro d p hp
    have hd : (m.family.shape d).hasParent = true := by simp [Family.shape, hp]
    exact (s.head_multiplicity_iff m typed d p hp).mp
      (holds (.multiplicity d ⟨.head, hd⟩))

/-- Both directions, with global completeness obligations explicit. The local
bank is exactly the existing Compile bank, including every ordinary default,
effective bound, inverse, triangle, key and guarded inclusion. -/
theorem structural_model_iff (wf : m.WellFormed) (support : m.Supported) :
    StructuralSatisfies m s ↔ s.Typed m ∧ s.GlobalConditions m ∧
      (interpretation U).IsModel (localFormulas m.family).diagram (s.interpret m) := by
  rw [s.structural_split m]
  constructor
  · rintro ⟨ht, hg, hl⟩
    exact ⟨ht, hg, s.local_model m support ht hl⟩
  · rintro ⟨ht, hg, hl⟩
    exact ⟨ht, hg, (s.local_model_iff m wf support ht).mp hl⟩

end Configuration

def ConstraintFree (a : AST) : Prop :=
  ∀ d ∈ a.entries, d.declaration.constraints = []

theorem constraintId_empty {a : AST} (h : ConstraintFree a) : IsEmpty (ConstraintId a) := by
  constructor
  rintro ⟨d, q⟩
  have hq := q.isLt
  have he := h (a.at d) (List.getElem_mem d.isLt)
  simp only [he, List.length_nil, Nat.not_lt_zero] at hq

noncomputable def structuralInterpretation {a : AST} (i : Input a)
    (h : ConstraintFree a) (U : Type) :
    Interpretation (vocabulary i).signature (semanticGraph U) :=
  FormalCD.Vocabulary.extendInterpretation (interpretation U)
    ⟨fun q => (constraintId_empty h).false q |>.elim⟩

/-- Constraint-free support is checked before discarding any expression bank.
The extra signature has no symbols; no meaning is invented for expressions. -/
theorem compiled_bank_iff {a : AST} (i : Input a) (h : ConstraintFree a)
    {U : Type} (s : Configuration a.Occurrence U) :
    (structuralInterpretation i h U).IsModel (compile i).formulas.diagram
      (s.interpret (EffectiveCore.erase i)) ↔
    (interpretation U).IsModel (localFormulas (family i)).diagram
      (s.interpret (EffectiveCore.erase i)) := by
  constructor
  · intro model φ hφ
    obtain ⟨l, rfl⟩ := hφ
    exact model _ ⟨.inl l, rfl⟩
  · intro model φ hφ
    obtain ⟨l, rfl⟩ := hφ
    cases l with
    | inl l => exact model _ ⟨l, rfl⟩
    | inr q => exact (constraintId_empty h).false q |>.elim

/-- Whole-model structural interpretation of the actual compiled bank plus
the explicitly required global clauses. Compile.Input retains naming/default
and declaration-completeness assumptions; the constraint-free guard is separate. -/
def SatisfiesAST {a : AST} (i : Input a) (h : ConstraintFree a)
    {U : Type} (s : Configuration a.Occurrence U) : Prop :=
  s.Typed (EffectiveCore.erase i) ∧ s.GlobalConditions (EffectiveCore.erase i) ∧
  (structuralInterpretation i h U).IsModel (compile i).formulas.diagram
    (s.interpret (EffectiveCore.erase i))

theorem erasure_correspondence {a : AST} (i : Input a) (h : ConstraintFree a)
    (support : (EffectiveCore.erase i).Supported) {U : Type}
    (s : Configuration a.Occurrence U) :
    SatisfiesAST i h s ↔ StructuralSatisfies (EffectiveCore.erase i) s := by
  unfold SatisfiesAST
  rw [compiled_bank_iff]
  exact (s.structural_model_iff _ (EffectiveCore.erase_wellFormed i) support).symm

def Configuration.pullback {C D U : Type} (s : Configuration C U) (f : D → C) :
    Configuration D U := ⟨s.root, s.head ∘ f, s.contains ∘ f, s.deref ∘ f⟩

theorem equal_erasure_satisfaction {a b : AST} (i : Input a) (j : Input b)
    (ha : ConstraintFree a) (hb : ConstraintFree b)
    (sa : (EffectiveCore.erase i).Supported) (sb : (EffectiveCore.erase j).Supported)
    (he : (⟨a.entries.length, EffectiveCore.erase i⟩ : Σ n, EffectiveCore n) =
      ⟨b.entries.length, EffectiveCore.erase j⟩)
    {U : Type} (s : Configuration DeclId U) :
    SatisfiesAST i ha (s.pullback (EffectiveCore.erase i).id) ↔
      SatisfiesAST j hb (s.pullback (EffectiveCore.erase j).id) := by
  rw [erasure_correspondence i ha sa, erasure_correspondence j hb sb]
  exact Iff.of_eq (congrArg (fun p : Σ n, EffectiveCore n =>
    StructuralSatisfies p.2 (s.pullback p.2.id)) he)

end Clafer.Semantics
