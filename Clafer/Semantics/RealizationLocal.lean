module

public import Clafer.Semantics.Realization

-- [proof->req~clafer-compile-realization~1]

/-! # Local-bank correspondence beyond the guarded leaf-super fragment

SoSyM §6.2.4–5 and Appendix 5. Only parentless basic super targets and
parented references are required here; abstract bodies are permitted.
The original #50 theorem and checker retain their original guards.
-/

@[expose] public section
namespace Clafer.Semantics.Realization
open CategoryTheory DPGraph DPGraph.Predicates MCS Compile

variable {n : Nat} {U : Type} (m : Core n) (s : Configuration (Fin n) U)

theorem local_model (selected : m.Selected) (typed : s.Typed m.toEffectiveCore)
    (h : s.LocalConditions m.toEffectiveCore) :
    (interpretation U).IsModel (localFormulas m.family).diagram (s.interpret m.toEffectiveCore) := by
  have po (d) (hp : (m.family.shape d).hasParent = true) :
      TargetMultiplicity Clafer.one (s.headMap m.toEffectiveCore d).inverse :=
    (s.parent_one_iff m.toEffectiveCore typed d _ (Configuration.parent_present m.toEffectiveCore d hp)).mpr
      (h.2.1 d _ (Configuration.parent_present m.toEffectiveCore d hp))
  have ro (d) (hr : (m.family.shape d).kind ≠ .basic) :
      TargetMultiplicity Clafer.one (s.derefMap m.toEffectiveCore d) :=
    (s.deref_one_iff m.toEffectiveCore typed d _ (Configuration.target_present m.toEffectiveCore d hr)).mpr
      (h.2.2.1 d _ (Configuration.target_present m.toEffectiveCore d hr))
  have mo (d) (hp : (m.family.shape d).hasParent = true) :
      TargetMultiplicity (m.family.multiplicity d) (s.headMap m.toEffectiveCore d) :=
    (s.head_multiplicity_iff m.toEffectiveCore typed d _ (Configuration.parent_present m.toEffectiveCore d hp)).mpr
      (h.2.2.2.2 d _ (Configuration.parent_present m.toEffectiveCore d hp))
  rintro φ ⟨l, rfl⟩
  cases l with
  | setValued d r ordinary =>
    change SetValued (s.ordinaryMap m.toEffectiveCore d r)
    rcases r with ⟨r, present⟩
    cases r with
    | head => exact s.headMap_setValued m.toEffectiveCore d
    | parent => exact (setValued_inverse _).mpr (s.headMap_setValued m.toEffectiveCore d)
    | dereference => exact s.derefMap_setValued m.toEffectiveCore d
    | target =>
      apply s.target_setValued m.toEffectiveCore h.2.2.2.1 d
      cases hk : (m.family.shape d).kind with
      | basic => simp [Clafer.Roles.mapPresent, hk] at present
      | referenceBag => simp [Clafer.Roles.mode, hk] at ordinary
      | referenceSet => exact hk
  | multiplicity d r =>
    change TargetMultiplicity (LocalId.range d r) (s.ordinaryMap m.toEffectiveCore d r)
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
    have he := selected.2.2.1 d e edge
    have he' := selected.1 e he.1
    cases role with
    | head =>
      change Inclusion (Span.ofRelation (fun (a : s.head d) (b : s.head e) => a.val = b.val))
      exact (identity_inclusion_iff _ _).mpr (h.1 d e edge)
    | source => simp [Clafer.Roles.classPresent, Family.shape, he'.2] at sup
    | target => simp [Clafer.Roles.classPresent, Family.shape, he.2, ReferenceTo.kind] at sup
  | inverse d hp =>
    change Inverse (s.headMap m.toEffectiveCore d) (s.headMap m.toEffectiveCore d).inverse
    exact s.parent_inverse m.toEffectiveCore d
  | commutation d hp hr =>
    change Commutation (s.headMap m.toEffectiveCore d) (s.derefMap m.toEffectiveCore d) (s.targetMap m.toEffectiveCore d)
    exact s.target_commutes m.toEffectiveCore d
  | key d hk hp =>
    exact (s.key_local_iff m.toEffectiveCore typed h.2.1 h.2.2.1 d hk hp).mpr (h.2.2.2.1 d hk)

theorem local_model_iff (selected : m.Selected) (typed : s.Typed m.toEffectiveCore) :
    (interpretation U).IsModel (localFormulas m.family).diagram (s.interpret m.toEffectiveCore) ↔
      s.LocalConditions m.toEffectiveCore := by
  refine ⟨?_, local_model m s selected typed⟩
  intro model
  have holds (l : LocalId m.family) := model _ ⟨l, rfl⟩
  have parents : s.Parents m.toEffectiveCore := by
    intro d p hp
    have hd : (m.family.shape d).hasParent = true := by simp [Family.shape, hp]
    exact (s.parent_one_iff m.toEffectiveCore typed d p hp).mp (holds (.multiplicity d ⟨.parent, hd⟩))
  have refs : s.References m.toEffectiveCore := by
    intro d t ht
    have hr : (m.family.shape d).kind ≠ .basic := by
      cases hr : m.family.reference d <;>
        simp_all [Family.shape, ReferenceTo.kind, ReferenceTo.target]
    have hd : Clafer.Roles.mapPresent (m.family.shape d).kind
        (m.family.shape d).hasParent .dereference = true := by
      simpa [Clafer.Roles.mapPresent] using hr
    exact (s.deref_one_iff m.toEffectiveCore typed d t ht).mp (holds (.multiplicity d ⟨.dereference, hd⟩))
  refine ⟨?_, parents, refs, ?_, ?_⟩
  · intro d e he
    exact (identity_inclusion_iff _ _).mp
      (holds (.inclusion ⟨d, e, Shape.headInclusion _ _, he⟩))
  · intro d hd
    have hr : (m.family.shape d).kind ≠ .basic := by simp [Family.shape, hd]
    have hp : (m.family.shape d).hasParent = true :=
      selected.2.2.2.1 d _ (Configuration.target_present m.toEffectiveCore d hr)
    exact (s.key_local_iff m.toEffectiveCore typed parents refs d hd hp).mp (holds (.key d hd hp))
  · intro d p hp
    have hd : (m.family.shape d).hasParent = true := by simp [Family.shape, hp]
    exact (s.head_multiplicity_iff m.toEffectiveCore typed d p hp).mp
      (holds (.multiplicity d ⟨.head, hd⟩))


end Clafer.Semantics.Realization
