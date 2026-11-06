module

public import FormalCD.Metamodel.Realization.Encoding

/-! # Canonical nd/ad context and their validity
SoSyM §6.1.3 and B.4 Definition 8. The context contains data, never a model proof.
-/

@[expose] public section

universe p s va ua v u z
namespace FormalCD.Metamodel.Realization
open CategoryTheory DPGraph DPGraph.Predicates

variable {V : Vocabulary.{s,va,ua}} {R : Registry.{p}}
variable (D : CDOver.{s,va,ua,p,v,u} V R)

abbrev arities : ArityContext V.signature D.carrier (Ambient D) :=
  ⟨symbol D, vertex D, arrow D⟩

noncomputable def argumentIndex (f : extent D .formula) :
    ((encode D).map Edge.args).toFamily.Index f ≃
      ArrowData (V.signature.arity ((formulas D).symm f).val.symbol) :=
  (arguments D).spanFamilyEquivalence.equiv f

theorem argumentIndex_target (f : extent D .formula)
    (l : ((encode D).map Edge.args).toFamily.Index f) :
    (((encode D).map Edge.args).target l.val).val =
      arrow D ((Candidate.ofFormula ((formulas D).symm f).val).argument (argumentIndex D f l)) :=
  congrArg Subtype.val ((arguments D).spanFamilyEquivalence.eval_eq f l).symm

noncomputable def descriptor : ArityDescriptor (σ := V.signature) (G := D.carrier) (arityBinding.comp (encode D)) where
  candidate f := some (Candidate.ofFormula ((formulas D).symm f).val)
  index f c l := by
    classical
    exact if h : c.symbol = ((formulas D).symm f).val.symbol then
      some (h.symm ▸ argumentIndex D f l) else none

-- [impl->req~formalcd-metamodel-realization~1]
noncomputable def context : Context.{p,s,va,ua,v,u,max p s va ua v u,0} R V.signature D.carrier (Ambient D) where
  names := names D
  arities := arities D
  describe d := by
    classical
    exact if h : d = arityBinding.comp (encode D) then
      h.symm ▸ descriptor D else ArityDescriptor.missing d

@[simp] theorem context_describe :
    (context D).describe (arityBinding.comp (encode D)) = descriptor D := by
  simp [context]

-- [proof->req~formalcd-metamodel-realization~1]
theorem arity_discipline :
    ArityDiscipline.{s,va,ua,v,u,max p s va ua v u,0} (arities D) (arityBinding.comp (encode D)) (descriptor D) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro e l h
    have hl : l = arrows D e := Subtype.ext h
    subst l
    change vertex D (((arrows D).symm (arrows D e)).1) = vertex D e.1
    rw [Equiv.symm_apply_apply]
  · intro e l h
    have hl : l = arrows D e := Subtype.ext h
    subst l
    change vertex D (((arrows D).symm (arrows D e)).2.1) = vertex D e.2.1
    rw [Equiv.symm_apply_apply]
  · intro f
    refine ⟨Candidate.ofFormula ((formulas D).symm f).val, rfl,
      Candidate.ofFormula_valid _, ⟨argumentIndex D f, ?_, argumentIndex_target D f⟩,
      ⟨⟨f, rfl⟩⟩, ?_⟩
    · intro l; simp [descriptor, Candidate.ofFormula]
      rfl
    · rintro ⟨l, hl⟩
      change l = f at hl
      subst l
      rfl

/-- Function spans compose with one link per source, preserving names as spans. -/
def functionComp {A B C : Type z} (f : A → B) (g : B → C) :
    Span.Iso ((Span.ofFunction f).comp (Span.ofFunction g)) (Span.ofFunction (g ∘ f)) where
  equiv :=
    { toFun := fun l => l.val.1
      invFun := fun a => ⟨(a, f a), rfl⟩
      left_inv := fun l => Subtype.ext (Prod.ext rfl l.property)
      right_inv := fun _ => rfl }
  source_eq _ := rfl
  target_eq l := congrArg g l.property

theorem name_square : Nonempty (Span.Iso
    ((((encode D).map Edge.predefIn).comp ((encode D).map Edge.classIn)).comp
      ((encode D).map Edge.name))
    (((encode D).map Edge.predefName).comp ((encode D).map Edge.predefStrIn))) := by
  refine ⟨((functionComp _ _).comp (Span.Iso.refl _)).trans
    ((functionComp _ _).trans (functionComp (predefNameMap D)
      (((encode D).map Edge.predefStrIn).target)).symm)⟩

theorem name_discipline : NameDiscipline.{p,max p s va ua v u,0} (names D) (nameBinding.comp (encode D)) := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_, fun _ => Iff.rfl, fun _ => Iff.rfl,
    fun _ => Iff.rfl, fun _ => Iff.rfl, ?_, name_square D⟩
  · rintro _ ⟨c, rfl⟩ i hi
    exact D.wellFormed.predefined_name c i hi
  · rintro _ ⟨c, rfl⟩ hi
    exact D.wellFormed.user_name c hi
  · rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩ i hi hi'
    exact congrArg (vertex D) (D.wellFormed.unique_predefined c c' i hi hi')
  · rintro _ ⟨e, he, rfl⟩
    exact D.wellFormed.inclusion_name e.2.2 he

theorem satisfies_names : (interpretation (context D)).Satisfies (encode D) nd :=
  name_discipline D

theorem satisfies_arities : (interpretation (context D)).Satisfies (encode D) ad := by
  rw [satisfies_ad, context_describe]
  exact arity_discipline D

end FormalCD.Metamodel.Realization
