module

public import FormalCD.Examples

/-!
[impl->req~formalcd-examples~1]
[proof->req~formalcd-examples~1]
[proof->req~formalcd-structure~1]
-/

/-!
# Concrete models and their restriction

Use the delivered span interpretation, with genuine inclusion and set-valued
obligations. Syntactic well-formedness alone does not certify a candidate model.
The registry annotation is not an implementation of primitive-domain semantics.
-/

@[expose] public section

namespace FormalCD.Examples

open CategoryTheory DPGraph.Predicates

def objects : Set Unit := Set.univ

def duplicateLinks : DPGraph.Span objects objects where
  Link := Bool
  source _ := ⟨(), trivial⟩
  target _ := ⟨(), trivial⟩

theorem duplicateLinks_not_setValued : ¬ SetValued duplicateLinks := by
  intro h
  exact Bool.false_ne_true (h (show
    (duplicateLinks.source false, duplicateLinks.target false) =
    (duplicateLinks.source true, duplicateLinks.target true) from rfl))

def modelMap : graph ⥤q semanticGraph Unit where
  obj _ := objects
  map
    | .leftIn | .rightIn | .values => DPGraph.Span.identity objects
    | .bag => duplicateLinks

theorem model_condition : (interpretation Unit).IsModel diagram.toDPGraph modelMap := by
  rintro φ (rfl | rfl | rfl | rfl)
  · change Inclusion (DPGraph.Span.identity objects)
    exact ⟨Function.bijective_id, fun _ => rfl⟩
  · change Inclusion (DPGraph.Span.identity objects)
    exact ⟨Function.bijective_id, fun _ => rfl⟩
  · change SetValued (DPGraph.Span.identity objects)
    exact fun _ _ h => congrArg Prod.fst h
  · change Total (DPGraph.Span.identity objects)
    exact Function.surjective_id

def model : (interpretation Unit).Model diagram.toDPGraph := ⟨modelMap, model_condition⟩

def restrictedModel : (interpretation Unit).Model diagram.toDPGraph :=
  collapseHom.reduct (interpretation Unit) model

theorem restricted_model :
    (interpretation Unit).IsModel diagram.toDPGraph restrictedModel.val :=
  restrictedModel.property

theorem restriction_forgets : restrictedModel =
    (interpretation Unit).reduct collapseHom.toDPHom model := rfl

theorem restriction_composition :
    (collapseHom.comp swapHom).reduct (interpretation Unit) model =
      collapseHom.reduct (interpretation Unit) (swapHom.reduct (interpretation Unit) model) :=
  Hom.reduct_comp _ _ _ _

theorem restriction_identity : (Hom.id diagram).reduct (interpretation Unit) model = model :=
  Hom.reduct_id _ _

theorem satisfaction_translation :
    (interpretation Unit).Satisfies modelMap (totalFormula.translate collapse) ↔
      (interpretation Unit).Satisfies (collapse.comp modelMap) totalFormula :=
  (interpretation Unit).satisfies_translate _ _ _

/-- A valid explicit bag mode can have repeated links in an actual model. -/
theorem model_bag_not_setValued :
    ¬ (interpretation Unit).Satisfies modelMap (setValuedFormula Arrow.bag) :=
  duplicateLinks_not_setValued

theorem extra_declaration_not_satisfied :
    ¬ (interpretation Unit).IsModel explicitBag.toDPGraph modelMap :=
  fun h => model_bag_not_setValued (h _ extra_target_declaration.1)

def failingMap : graph ⥤q semanticGraph Unit where
  obj _ := objects
  map _ := duplicateLinks

theorem failing_satisfaction :
    ¬ (interpretation Unit).Satisfies failingMap (setValuedFormula Arrow.values) :=
  duplicateLinks_not_setValued

theorem wellFormed_does_not_certify_satisfaction : diagram.toRaw.WellFormed ∧
    ¬ (interpretation Unit).IsModel diagram.toDPGraph failingMap :=
  ⟨wellFormed, fun h => failing_satisfaction (h _ ordinary_default)⟩

end FormalCD.Examples
