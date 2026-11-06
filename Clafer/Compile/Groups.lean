module

public import Clafer.Compile.GroupSupport
public import Clafer.MCS.Gluing.Origins

/-!
[impl->req~clafer-compile-formulas~1]
[impl->req~clafer-compile-groups~1]
[impl->req~clafer-gluing-declarations~1]
[proof->req~clafer-compile-groups~1]
[proof->req~clafer-gluing-declarations~1]
[proof->req~clafer-gluing-formalcd~1]
-/

/-! # Augmented Compile and exact gluing (SoSyM B.4 Definitions 8–10, §6.2.5)

The original MCS bank retains its total-args/key proof. The additional component
uses full graph bindings and can have no arrows. The complete raw declaration
bank is their disjoint union; no old MCS total-args claim is made for it.
-/

@[expose] public section
namespace Clafer.Compile
open CategoryTheory MCS DPGraph

variable {a : AST} (i : Input a)

noncomputable def groupBank : Formulas (roles i) (Groups.signature (family i)) where
  Id := Groups.Id (family i)
  owner := Subtype.val
  formula := Groups.formula (family i)

noncomputable def groupExtra : Signature :=
  ⟨ConstraintId a ⊕ Groups.Id (family i),
    Sum.elim (Constraints.signature i.constraint).arity (Groups.signature (family i)).arity⟩

noncomputable def groupVocabulary : FormalCD.Vocabulary :=
  FormalCD.Vocabulary.extend (groupExtra i)

/-- Preserve full bindings of built-ins and authored constraints verbatim. -/
noncomputable def promote {G : Quiv} :
    Formula (vocabulary i).signature G → Formula (groupVocabulary i).signature G
  | ⟨.inl p, b⟩ => ⟨.inl p, b⟩
  | ⟨.inr p, b⟩ => ⟨.inr (.inl p), b⟩

noncomputable def generatedGroup (p : Groups.Id (family i)) :
    Formula (groupVocabulary i).signature (roles i).graph :=
  ⟨.inr (.inr p), Groups.binding (family i) p.val⟩

/-- B.4 declarations with owners. This raw bank is deliberately not asserted
to satisfy Figure 23's total args. -/
noncomputable def completeBank : Formulas (roles i) (groupVocabulary i).signature where
  Id := FormulaId i ⊕ Groups.Id (family i)
  owner | .inl q => (formulas i).owner q | .inr p => p.val
  formula | .inl q => promote i (formula i q) | .inr p => generatedGroup i p

/-- An explicit augmented result keeps the original structural result available. -/
structure Augmented where
  structural : Model a.Occurrence a.Occurrence (vocabulary i).signature
  additional : Formulas (roles i) (Groups.signature (family i))
  complete : Formulas (roles i) (groupVocabulary i).signature

noncomputable def compileAugmented : Augmented i :=
  ⟨compile i, groupBank i, completeBank i⟩

@[simp] theorem forget_augmented : (compileAugmented i).structural = compile i := rfl

theorem complete_declarations (φ) :
    φ ∈ (compileAugmented i).complete.diagram.declarations ↔
      (∃ q, promote i (formula i q) = φ) ∨ (∃ p, generatedGroup i p = φ) := by
  constructor
  · rintro ⟨q | p, rfl⟩
    · exact Or.inl ⟨q, rfl⟩
    · exact Or.inr ⟨p, rfl⟩
  · rintro (⟨q, rfl⟩ | ⟨p, rfl⟩)
    · exact ⟨.inl q, rfl⟩
    · exact ⟨.inr p, rfl⟩

theorem group_declared (p : Groups.Id (family i)) :
    generatedGroup i p ∈ (compileAugmented i).complete.diagram.declarations :=
  ⟨.inr p, rfl⟩

theorem group_owner (p : Groups.Id (family i)) :
    (compileAugmented i).complete.owner (.inr p) = p.val := rfl

theorem group_context (p : Groups.Id (family i)) :
    (generatedGroup i p).binding.obj (Groups.context (family i) p.val) = p.val := rfl

theorem promote_embed (φ : Formula DPGraph.Predicates.signature (roles i).graph) :
    promote i ((vocabulary i).embed φ) = (groupVocabulary i).embed φ := by
  cases φ; rfl

/-- All effective defaults are retained in the complete source bank. -/
theorem complete_defaults : Gluing.Defaults (roles i) (completeBank i) where
  inclusion m hm := by
    cases m with
    | inclusion s => exact ⟨.inl (.inl (.inclusion s)), rfl⟩
    | ordinary c m =>
      simp only [Family.MapId.mode, Clafer.Roles.mode] at hm
      split at hm <;> contradiction
  ordinary m hm := by
    cases m with
    | inclusion s => cases hm
    | ordinary c m => exact ⟨.inl (.inl (.setValued c m hm)), rfl⟩

noncomputable def groupAnnotations : a.Occurrence → Option Gluing.registry.Id :=
  Gluing.annotations (compile i).valid.cojoining

/-- Compile's referents are injective; no incidence or metadata consistency is
assumed of the output. -/
theorem groupCompatible : Gluing.Compatible (roles i) (labels i) (groupAnnotations i) where
  source m n h := by change m = n at h; cases h; rfl
  target m n h := by change m = n at h; cases h; rfl
  class_name v w h := by cases sourceId_injective i.ast h; rfl
  map_name m n h := by change m = n at h; cases h; rfl
  predefined v w h := by cases sourceId_injective i.ast h; rfl
  mode m n h := by change m = n at h; cases h; rfl

noncomputable def groupLabel :=
  Gluing.label (roles i) (labels i) (groupCompatible i).toIncidence

theorem group_representative_label (v : a.Occurrence) :
    Gluing.classRepresentative (labels i) (Gluing.classLabel (labels i) v) = v :=
  sourceId_injective i.ast (Gluing.classRepresentative_spec (labels i) (Gluing.classLabel (labels i) v))

/-- Canonical Compile labels only rename identities. This inverse is specific
to Compile; generic noninjective MCS gluing has no such inverse. -/
noncomputable def groupUnlabel :
    Gluing.graph (roles i) (labels i) ⥤q (roles i).graph where
  obj := Gluing.classRepresentative (labels i)
  map e := ⟨e.val.val, by
    constructor
    · have hs := congrArg (Gluing.classRepresentative (labels i))
        ((Gluing.source_label (groupCompatible i).toIncidence e.val.val).symm.trans e.property.1)
      simpa only [group_representative_label] using hs
    · have ht := congrArg (Gluing.classRepresentative (labels i))
        ((Gluing.target_label (groupCompatible i).toIncidence e.val.val).symm.trans e.property.2)
      simpa only [group_representative_label] using ht⟩

theorem arrow_transport_val {x y x' y' : a.Occurrence}
    (hx : x = x') (hy : y = y') (e : (roles i).Arrow x y) :
    (Eq.recOn hy (Eq.recOn hx e) : (roles i).Arrow x' y').val = e.val := by
  cases hx; cases hy; rfl

theorem group_label_unlabel :
    (groupLabel i).comp (groupUnlabel i) = Prefunctor.id (roles i).graph := by
  apply Prefunctor.ext (group_representative_label i)
  intro x y e
  apply Subtype.ext
  exact (arrow_transport_val i _ _ e).symm

noncomputable def gluedGroups : FormalCD.CDOver (groupVocabulary i) Gluing.registry :=
  Gluing.cd (groupCompatible i) (completeBank i)
    (Gluing.naming_of_valid (compile i).valid) (complete_defaults i)

/-- Exact translated union, not merely forward preservation. -/
theorem glued_declarations (φ) :
    φ ∈ (gluedGroups i).declarations ↔
      (∃ q, (promote i (formula i q)).translate (groupLabel i) = φ) ∨
      (∃ p, (generatedGroup i p).translate (groupLabel i) = φ) := by
  constructor
  · rintro ⟨q | p, rfl⟩
    · exact Or.inl ⟨q, rfl⟩
    · exact Or.inr ⟨p, rfl⟩
  · rintro (⟨q, rfl⟩ | ⟨p, rfl⟩)
    · exact ⟨.inl q, rfl⟩
    · exact ⟨.inr p, rfl⟩

theorem glued_group_declared (p : Groups.Id (family i)) :
    (generatedGroup i p).translate (groupLabel i) ∈ (gluedGroups i).declarations :=
  ⟨.inr p, rfl⟩

noncomputable def groupInterpretation (U : Type)
    (authored : Interpretation (Constraints.signature i.constraint) (DPGraph.Predicates.semanticGraph U)) :
    Interpretation (groupVocabulary i).signature (DPGraph.Predicates.semanticGraph U) where
  meaning
    | .inl p => (DPGraph.Predicates.interpretation U).meaning p
    | .inr (.inl p) => authored.meaning p
    | .inr (.inr p) => (Groups.interpretation (family i) U).meaning p

/-- Existing meanings are unchanged, including ordinary authored constraints
whose owners are abstract. Only generated groups use the concrete-owner guard. -/
theorem original_satisfaction {U : Type}
    (authored : Interpretation (Constraints.signature i.constraint) (DPGraph.Predicates.semanticGraph U))
    (m : (roles i).graph ⥤q DPGraph.Predicates.semanticGraph U)
    (φ : Formula (vocabulary i).signature (roles i).graph) :
    (groupInterpretation i U authored).Satisfies m (promote i φ) ↔
      (FormalCD.Vocabulary.extendInterpretation (DPGraph.Predicates.interpretation U) authored).Satisfies m φ := by
  rcases φ with ⟨p | q, b⟩ <;> rfl

/-- Exact image gives reflection as well as preservation for the complete
diagram; both original and generated components must be satisfied. -/
theorem glued_model_iff {Ω : Quiv} (I : Interpretation (groupVocabulary i).signature Ω)
    (m : (gluedGroups i).carrier ⥤q Ω) :
    I.IsModel (gluedGroups i).toDPGraph m ↔
      (∀ q, I.Satisfies ((groupLabel i).comp m) (promote i (formula i q))) ∧
      (∀ p, I.Satisfies ((groupLabel i).comp m) (generatedGroup i p)) := by
  exact (I.isModel_range_translate (completeBank i).formula (groupLabel i) m).trans
    ((I.isModel_range (completeBank i).formula _).trans Sum.forall)

end Clafer.Compile
