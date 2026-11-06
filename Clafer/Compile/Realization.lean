module

public import Clafer.Semantics.RealizationLocal

/-!
# Telematics.Structural realization declarations and gluing

SoSyM §5.5, §6.2.3–5, B.4–B.5, Appendices 5–6; selected D2/D4/D6.
Explicit families generate actual built-in cover/disjoint predicates. Realized
ordinary fields add the group declarations suppressed by effective abstractness.
The complete #65 bank, including authored constraints and defaults, is retained.
-/

@[expose] public section
namespace Clafer.Compile.Realization
open CategoryTheory MCS DPGraph DPGraph.Predicates Semantics

variable {n : Nat} (m : Semantics.Realization.Core n)

abbrev Member (d : Fin n) := {c : Fin n // m.family.super c = some d}
noncomputable instance (d : Fin n) : Fintype (Member m d) := Fintype.ofFinite _
noncomputable def member (d : Fin n) : Fin (Fintype.card (Member m d)) ≃ Member m d :=
  (Fintype.equivFin _).symm

noncomputable def fanBinding (d : Fin n) :
    Arity.fanIn (Fintype.card (Member m d)) ⥤q m.family.canonicalRoles.graph where
  obj | .center => d | .member j => (member m d j).val
  map
    | .edge j =>
      ⟨.inclusion ⟨(member m d j).val, d, Shape.headInclusion _ _,
      (member m d j).property⟩, rfl, rfl⟩

noncomputable def coverFormula (d : Fin n) :
    Formula DPGraph.Predicates.signature m.family.canonicalRoles.graph :=
  ⟨.cover (Fintype.card (Member m d)), fanBinding m d⟩

noncomputable def disjointFormula (d : Fin n) :
    Formula DPGraph.Predicates.signature m.family.canonicalRoles.graph :=
  ⟨.disjoint (Fintype.card (Member m d)), fanBinding m d⟩

variable {U : Type} (s : Configuration (Fin n) U)

theorem cover_iff (d : Fin n) :
    (interpretation U).Satisfies (s.interpret m.toEffectiveCore) (coverFormula m d) ↔
      ∀ x, x ∈ s.head d → ∃ c, m.family.super c = some d ∧ x ∈ s.head c := by
  change Cover (fun j => Span.ofRelation
    (fun (x : s.head (member m d j).val) (y : s.head d) => x.val = y.val)) ↔ _
  constructor
  · intro h x hx
    obtain ⟨j, l, he⟩ := h ⟨x, hx⟩
    have e : l.val.1.val = x := l.property.trans (congrArg Subtype.val he)
    exact ⟨_, (member m d j).property, e ▸ l.val.1.property⟩
  · intro h x
    obtain ⟨c, hc, hx⟩ := h x.val x.property
    let j := (member m d).symm ⟨c, hc⟩
    have hj : (member m d j).val = c := congrArg Subtype.val ((member m d).apply_symm_apply _)
    exact ⟨j, ⟨(⟨x.val, hj.symm ▸ hx⟩, x), rfl⟩, rfl⟩

theorem disjoint_iff (inh : s.Inherits m.toEffectiveCore) (d : Fin n) :
    (interpretation U).Satisfies (s.interpret m.toEffectiveCore) (disjointFormula m d) ↔
      ∀ c e, m.family.super c = some d → m.family.super e = some d → c ≠ e →
        ∀ x, ¬ (x ∈ s.head c ∧ x ∈ s.head e) := by
  change DPGraph.Predicates.Disjoint (fun j => Span.ofRelation
    (fun (x : s.head (member m d j).val) (y : s.head d) => x.val = y.val)) ↔ _
  constructor
  · intro h c e hc he hce x hx
    let j := (member m d).symm ⟨c, hc⟩
    let k := (member m d).symm ⟨e, he⟩
    have hj : (member m d j).val = c := congrArg Subtype.val ((member m d).apply_symm_apply _)
    have hk : (member m d k).val = e := congrArg Subtype.val ((member m d).apply_symm_apply _)
    have hjk : j ≠ k := fun eq => hce (hj.symm.trans ((congrArg (fun z => (member m d z).val) eq).trans hk))
    exact h j k hjk ⟨(⟨x, hj.symm ▸ hx.1⟩, ⟨x, inh c d hc x hx.1⟩), rfl⟩
      ⟨(⟨x, hk.symm ▸ hx.2⟩, ⟨x, inh e d he x hx.2⟩), rfl⟩ rfl
  · intro h j k hjk l r eq
    have hne : (member m d j).val ≠ (member m d k).val := by
      intro he
      exact hjk ((member m d).injective (Subtype.ext he))
    have he : l.val.1.val = r.val.1.val :=
      l.property.trans ((congrArg Subtype.val eq).trans r.property.symm)
    exact h _ _ (member m d j).property (member m d k).property hne _
      ⟨l.val.1.property, he.symm ▸ r.val.1.property⟩

variable {a : AST} (i : Input a)

abbrev ExplicitId := {d : a.Occurrence // (Semantics.Realization.Core.ofInput i).explicitAbstract d = true}
abbrev FieldId := {d : a.Occurrence //
  (family i).isAbstract d = true ∧ (Semantics.Realization.Core.ofInput i).explicitAbstract d = false}

noncomputable def extra : Signature :=
  ⟨(groupExtra i).Symbol ⊕ FieldId i,
    Sum.elim (groupExtra i).arity (fun p => Groups.arity (family i) p.val)⟩
noncomputable def vocabulary : FormalCD.Vocabulary := FormalCD.Vocabulary.extend (extra i)

noncomputable def promote {G : Quiv} :
    Formula (groupVocabulary i).signature G → Formula (vocabulary i).signature G
  | ⟨.inl p, b⟩ => ⟨.inl p, b⟩
  | ⟨.inr p, b⟩ => ⟨.inr (.inl p), b⟩

noncomputable def abstractFormula (p : ExplicitId i) (disjoint : Bool) :
    Formula (vocabulary i).signature (roles i).graph :=
  (vocabulary i).embed (if disjoint then
    disjointFormula (Semantics.Realization.Core.ofInput i) p.val else
    coverFormula (Semantics.Realization.Core.ofInput i) p.val)

noncomputable def fieldFormula (p : FieldId i) :
    Formula (vocabulary i).signature (roles i).graph :=
  ⟨.inr (.inr p), Groups.binding (family i) p.val⟩

noncomputable def bank : Formulas (roles i) (vocabulary i).signature where
  Id := (completeBank i).Id ⊕ (ExplicitId i × Bool) ⊕ FieldId i
  owner | .inl q => (completeBank i).owner q
        | .inr (.inl p) => p.1.val
        | .inr (.inr p) => p.val
  formula | .inl q => promote i ((completeBank i).formula q)
          | .inr (.inl p) => abstractFormula i p.1 p.2
          | .inr (.inr p) => fieldFormula i p

/-- Completeness is the actual constructed declaration image. -/
theorem declarations (φ) : φ ∈ (bank i).diagram.declarations ↔
    (∃ q, promote i ((completeBank i).formula q) = φ) ∨
    (∃ p b, abstractFormula i p b = φ) ∨ (∃ p, fieldFormula i p = φ) := by
  constructor
  · rintro ⟨q | (⟨p,b⟩ | p), rfl⟩
    · exact Or.inl ⟨q, rfl⟩
    · exact Or.inr (Or.inl ⟨p,b,rfl⟩)
    · exact Or.inr (Or.inr ⟨p,rfl⟩)
  · rintro (⟨q,rfl⟩ | ⟨p,b,rfl⟩ | ⟨p,rfl⟩)
    · exact ⟨.inl q,rfl⟩
    · exact ⟨.inr (.inl ⟨p,b⟩),rfl⟩
    · exact ⟨.inr (.inr p),rfl⟩

theorem cover_declared (p : ExplicitId i) :
    abstractFormula i p false ∈ (bank i).diagram.declarations := ⟨.inr (.inl ⟨p,false⟩),rfl⟩
theorem disjoint_declared (p : ExplicitId i) :
    abstractFormula i p true ∈ (bank i).diagram.declarations := ⟨.inr (.inl ⟨p,true⟩),rfl⟩
theorem field_declared (p : FieldId i) :
    fieldFormula i p ∈ (bank i).diagram.declarations := ⟨.inr (.inr p),rfl⟩

theorem defaults : Gluing.Defaults (roles i) (bank i) where
  inclusion m hm := by
    cases m with
    | inclusion r => exact ⟨.inl (.inl (.inl (.inclusion r))),rfl⟩
    | ordinary c r =>
      simp only [Family.MapId.mode, Clafer.Roles.mode] at hm
      split at hm <;> contradiction
  ordinary m hm := by
    cases m with
    | inclusion r => cases hm
    | ordinary c r => exact ⟨.inl (.inl (.inl (.setValued c r hm))),rfl⟩

noncomputable def glued : FormalCD.CDOver (vocabulary i) Gluing.registry :=
  Gluing.cd (groupCompatible i) (bank i)
    (Gluing.naming_of_valid (compile i).valid) (defaults i)

/-- Every source declaration survives gluing, and none is added. -/
theorem glued_declarations (φ) : φ ∈ (glued i).declarations ↔
    ∃ q, ((bank i).formula q).translate (groupLabel i) = φ := Iff.rfl

-- [impl->req~clafer-compile-realization~1]
/-- The structural MCS and the #65 augmentation remain available unchanged. -/
noncomputable def compileRealized := (compileAugmented i, bank i)
@[simp] theorem forget : (compileRealized i).1 = compileAugmented i := rfl

noncomputable def interpretation (U : Type)
    (authored : Interpretation (Constraints.signature i.constraint) (semanticGraph U)) :
    Interpretation (vocabulary i).signature (semanticGraph U) where
  meaning
    | .inl p => (DPGraph.Predicates.interpretation U).meaning p
    | .inr (.inl p) => (groupInterpretation i U authored).meaning (.inr p)
    | .inr (.inr p) => fun d => ∀ x : Subtype (d.obj (Groups.context (family i) p.val)),
        InRange ((family i).group p.val).effective.range
          {y : U // Groups.Objects (family i) d x.val y}

noncomputable def descend (s : Configuration a.Occurrence U) :
    (glued i).carrier ⥤q semanticGraph U :=
  (groupUnlabel i).comp (s.interpret (EffectiveCore.erase i))

theorem descend_reduct (s : Configuration a.Occurrence U) :
    (groupLabel i).comp (descend i s) = s.interpret (EffectiveCore.erase i) := by
  erw [descend, ← Prefunctor.comp_assoc, group_label_unlabel, Prefunctor.id_comp]

theorem glued_model_iff (I : Interpretation (vocabulary i).signature (semanticGraph U))
    (s : Configuration a.Occurrence U) :
    I.IsModel (glued i).toDPGraph (descend i s) ↔
      I.IsModel (bank i).diagram (s.interpret (EffectiveCore.erase i)) := by
  have h := I.isModel_range_translate (bank i).formula (groupLabel i) (descend i s)
  erw [descend_reduct] at h
  exact h

end Clafer.Compile.Realization

@[expose] public section
namespace Clafer.Compile.Realization
open CategoryTheory MCS DPGraph DPGraph.Predicates Semantics
variable {a : AST} (i : Input a) {U : Type}
variable (authored : Interpretation (Constraints.signature i.constraint) (semanticGraph U))

 theorem original_satisfaction (s : Configuration a.Occurrence U)
    (φ : Formula (groupVocabulary i).signature (roles i).graph) :
    (interpretation i U authored).Satisfies (s.interpret (EffectiveCore.erase i)) (promote i φ) ↔
      (groupInterpretation i U authored).Satisfies (s.interpret (EffectiveCore.erase i)) φ := by
  rcases φ with ⟨p | q,b⟩ <;> rfl

theorem field_iff (s : Configuration a.Occurrence U)
    (typed : s.Typed (EffectiveCore.erase i)) (p : FieldId i) :
    (interpretation i U authored).Satisfies (s.interpret (EffectiveCore.erase i)) (fieldFormula i p) ↔
      Groups.Holds (family i) s p.val := by
  unfold Interpretation.Satisfies fieldFormula interpretation Groups.Holds
  apply forall_congr'
  intro x
  apply inRange_iff
  exact Equiv.subtypeEquivRight (fun y => Groups.objects_interpret _ s typed p.val x.val y)

theorem abstract_iff (s : Configuration a.Occurrence U)
    (inh : s.Inherits (EffectiveCore.erase i)) :
    (∀ p b, (interpretation i U authored).Satisfies (s.interpret (EffectiveCore.erase i))
      (abstractFormula i p b)) ↔ Semantics.Realization.Abstracts (Semantics.Realization.Core.ofInput i) s := by
  constructor
  · intro h d hd
    exact ⟨(cover_iff _ s d).mp (h ⟨d,hd⟩ false),
      (disjoint_iff _ s inh d).mp (h ⟨d,hd⟩ true)⟩
  · intro h p b
    cases b
    · exact (cover_iff _ s p.val).mpr ((h p.val p.property).1)
    · exact (disjoint_iff _ s inh p.val).mpr ((h p.val p.property).2)

/-- Declaration completeness plus proved interpretation, not a caller's bridge. -/
theorem bank_model_iff (s : Configuration a.Occurrence U)
    (typed : s.Typed (EffectiveCore.erase i)) (inh : s.Inherits (EffectiveCore.erase i)) :
    (interpretation i U authored).IsModel (bank i).diagram (s.interpret (EffectiveCore.erase i)) ↔
      (groupInterpretation i U authored).IsModel (completeBank i).diagram
        (s.interpret (EffectiveCore.erase i)) ∧
      Semantics.Realization.Abstracts (Semantics.Realization.Core.ofInput i) s ∧
      (∀ p : FieldId i, Groups.Holds (family i) s p.val) := by
  constructor
  · intro h
    refine ⟨?_, (abstract_iff i authored s inh).mp ?_, ?_⟩
    · rintro φ ⟨q,rfl⟩
      exact (original_satisfaction i authored s _).mp (h _ ⟨.inl q,rfl⟩)
    · intro p b; exact h _ ⟨.inr (.inl ⟨p,b⟩),rfl⟩
    · intro p; exact (field_iff i authored s typed p).mp (h _ ⟨.inr (.inr p),rfl⟩)
  · rintro ⟨ho,ha,hf⟩ φ ⟨q | (⟨p,b⟩ | p),rfl⟩
    · exact (original_satisfaction i authored s _).mpr (ho _ ⟨q,rfl⟩)
    · exact (abstract_iff i authored s inh).mpr ha p b
    · exact (field_iff i authored s typed p).mpr (hf p)

/-- Authored body meaning stays a parameter for #68/#69, while each occurrence
and its actual Compile binding is retained. No body satisfaction is assumed. -/
def AuthoredHolds (s : Configuration a.Occurrence U) : Prop :=
  ∀ q : ConstraintId a, (groupInterpretation i U authored).Satisfies
    (s.interpret (EffectiveCore.erase i)) (Compile.promote i (formula i (.inr q)))

theorem correspondence (selected : (Semantics.Realization.Core.ofInput i).Selected)
    (s : Configuration a.Occurrence U) (typed : s.Typed (EffectiveCore.erase i)) :
    (interpretation i U authored).IsModel (glued i).toDPGraph (descend i s) ↔
      s.LocalConditions (EffectiveCore.erase i) ∧ AuthoredHolds i authored s ∧
      Semantics.Realization.Abstracts (Semantics.Realization.Core.ofInput i) s ∧
      Semantics.Realization.Groups (Semantics.Realization.Core.ofInput i) s := by
  rw [glued_model_iff]
  constructor
  · intro h
    have localModel : (DPGraph.Predicates.interpretation U).IsModel
        (localFormulas (family i)).diagram (s.interpret (EffectiveCore.erase i)) := by
      rintro φ ⟨l,rfl⟩
      exact h _ ⟨.inl (.inl (.inl l)),rfl⟩
    have hl := (Semantics.Realization.local_model_iff _ s selected typed).mp localModel
    obtain ⟨ho,ha,hf⟩ := (bank_model_iff i authored s typed hl.1).mp h
    refine ⟨hl, ?_, ha, ?_⟩
    · intro q; exact ho _ ⟨.inl (.inr q),rfl⟩
    · intro d hd
      cases he : (family i).isAbstract d with
      | false =>
          exact (generated_group_iff i authored s typed ⟨d,he⟩).mp (ho _ ⟨.inr ⟨d,he⟩,rfl⟩)
      | true => exact hf ⟨d,he,hd⟩
  · rintro ⟨hl,hc,ha,hg⟩
    apply (bank_model_iff i authored s typed hl.1).mpr
    refine ⟨?_,ha,fun p => hg p.val p.property.2⟩
    have localModel := Semantics.Realization.local_model _ s selected typed hl
    rintro φ ⟨(l | q) | p,rfl⟩
    · exact localModel _ ⟨l,rfl⟩
    · exact hc q
    · apply (generated_group_iff i authored s typed p).mpr
      apply hg
      cases he : (Semantics.Realization.Core.ofInput i).explicitAbstract p.val with
      | false => rfl
      | true =>
          have hh := (selected.1 p.val he).1
          change (family i).isAbstract p.val = true at hh
          rw [p.property] at hh
          contradiction

-- [proof->req~clafer-compile-realization~1]
/-- Root/freshness/used-object and declaration-disjointness obligations are explicit global conditions;
all local, abstract and group clauses come from the complete generated bank. -/
theorem whole_model (selected : (Semantics.Realization.Core.ofInput i).Selected)
    (s : Configuration a.Occurrence U) :
    (s.Typed (EffectiveCore.erase i) ∧ s.Rooted (EffectiveCore.erase i) ∧
      s.DeclarationDisjoint (EffectiveCore.erase i) ∧
      (interpretation i U authored).IsModel (glued i).toDPGraph (descend i s)) ↔
    (Semantics.Realization.Satisfies (Semantics.Realization.Core.ofInput i) s ∧
      AuthoredHolds i authored s) := by
  constructor
  · rintro ⟨ht,hr,hd,hm⟩
    obtain ⟨hl,hc,ha,hg⟩ := (correspondence i authored selected s ht).mp hm
    exact ⟨⟨ht,hr,hl,ha,hg,hd⟩,hc⟩
  · rintro ⟨⟨ht,hr,hl,ha,hg,hd⟩,hc⟩
    exact ⟨ht,hr,hd,(correspondence i authored selected s ht).mpr ⟨hl,hc,ha,hg⟩⟩

end Clafer.Compile.Realization
