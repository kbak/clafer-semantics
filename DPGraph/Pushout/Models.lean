module

public import DPGraph.Pushout.Basic

/-!
# Models on a carrier pushout

Derived results over SoSyM B.4 Definitions 9–10 and the abstract B.5 Theorem 3.
For a supplied carrier colimit, models of the declaration union correspond to
compatible component models. The semantic graph lies in the carrier universes
so that the supplied colimit applies; interpretations and reducts remain unchanged.
-/

public section

universe s va ua v u

namespace DPGraph.Pushout

open CategoryTheory CategoryTheory.Limits

variable {σ : Signature.{s, va, ua}}
variable {S T U : DPGraph.{s, va, ua, v, u} σ}
variable (F : Hom S T) (J : Hom S U) (c : CarrierCocone F J)
variable {Ω : Quiv.{v, u}} (I : Interpretation σ Ω)

-- [impl->req~dpgraph-model-amalgamation~1]
private noncomputable def amalgamate (hc : IsColimit c) (p : CompatibleModels I F J) :
    I.Model (obj F J c) := by
  let w : F.toPrefunctor.comp p.val.1.val = J.toPrefunctor.comp p.val.2.val :=
    congrArg Subtype.val p.property
  let d : c.pt ⥤q Ω :=
    PushoutCocone.IsColimit.desc (C := Quiv.{v, u}) hc p.val.1.val p.val.2.val w
  refine ⟨d, ?_⟩
  intro φ hφ
  rcases hφ with ⟨ψ, hψ, rfl⟩ | ⟨ψ, hψ, rfl⟩
  · apply (I.satisfies_translate ψ c.inl d).mpr
    rw [show c.inl.comp d = p.val.1.val from
      PushoutCocone.IsColimit.inl_desc (C := Quiv.{v, u}) hc _ _ w]
    exact p.val.1.property ψ hψ
  · apply (I.satisfies_translate ψ c.inr d).mpr
    rw [show c.inr.comp d = p.val.2.val from
      PushoutCocone.IsColimit.inr_desc (C := Quiv.{v, u}) hc _ _ w]
    exact p.val.2.property ψ hψ

private theorem amalgamate_inl (hc : IsColimit c) (p : CompatibleModels I F J) :
    I.reduct (inl F J c) (amalgamate F J c I hc p) = p.val.1 := by
  apply Subtype.ext
  exact PushoutCocone.IsColimit.inl_desc (C := Quiv.{v, u}) hc _ _ _

private theorem amalgamate_inr (hc : IsColimit c) (p : CompatibleModels I F J) :
    I.reduct (inr F J c) (amalgamate F J c I hc p) = p.val.2 := by
  apply Subtype.ext
  exact PushoutCocone.IsColimit.inr_desc (C := Quiv.{v, u}) hc _ _ _

-- [proof->req~dpgraph-model-amalgamation~1]
/-- Models on the declaration union are equivalent to compatible component models,
using the supplied carrier colimit. The forward map is the pair of reducts. -/
noncomputable def modelEquiv (hc : IsColimit c) :
    I.Model (obj F J c) ≃ CompatibleModels I F J where
  toFun m := ⟨(I.reduct (inl F J c) m, I.reduct (inr F J c) m), by
    rw [← I.reduct_comp, ← I.reduct_comp]
    have h : F.comp (inl F J c) = J.comp (inr F J c) := Hom.ext c.condition
    rw [h]⟩
  invFun := amalgamate F J c I hc
  left_inv m := by
    apply Subtype.ext
    apply PushoutCocone.IsColimit.hom_ext (C := Quiv.{v, u}) hc
    · exact congrArg Subtype.val (amalgamate_inl F J c I hc _)
    · exact congrArg Subtype.val (amalgamate_inr F J c I hc _)
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext (amalgamate_inl F J c I hc p) (amalgamate_inr F J c I hc p)

/-- The left component of the model equivalence is exactly restriction along `inl`. -/
theorem modelEquiv_fst (hc : IsColimit c) (m : I.Model (obj F J c)) :
    (modelEquiv F J c I hc m).val.1 = I.reduct (inl F J c) m := by rfl

/-- The right component of the model equivalence is exactly restriction along `inr`. -/
theorem modelEquiv_snd (hc : IsColimit c) (m : I.Model (obj F J c)) :
    (modelEquiv F J c I hc m).val.2 = I.reduct (inr F J c) m := by rfl

end DPGraph.Pushout
