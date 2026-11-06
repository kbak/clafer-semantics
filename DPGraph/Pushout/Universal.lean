module

public import DPGraph.Pushout.Basic

/-!
[impl->req~dpgraph-pushout-universal~1]
[proof->req~dpgraph-pushout-universal~1]
-/

/-!
# Universal property of declaration unions

The declaration union on a carrier pushout is a pushout of DP-graphs. This is a
derived result over SoSyM B.4 Definitions 9–10 and the abstract B.5 representation,
not a verbatim paper theorem or an assertion of global pushout existence.
-/

@[expose] public section

universe s va ua v u

namespace DPGraph.Pushout

open CategoryTheory CategoryTheory.Limits

variable {σ : Signature.{s, va, ua}}
variable {S T U : DPGraph.{s, va, ua, v, u} σ}

/-- A supplied carrier colimit lifts to the DP-graph cocone whose declarations
are exactly the translated component declarations. -/
noncomputable def isColimit (F : Hom S T) (J : Hom S U) (c : CarrierCocone F J)
    (hc : IsColimit c) : IsColimit (Pushout.cocone F J c) := by
  apply PushoutCocone.isColimitAux'
  intro d
  let e : CarrierCocone F J :=
    PushoutCocone.mk d.inl.toPrefunctor d.inr.toPrefunctor
      (congrArg Hom.toPrefunctor d.condition)
  let k : Hom (obj F J c) d.pt :=
    { toPrefunctor := hc.desc e
      preserves := by
        intro φ hφ
        rcases hφ with ⟨ψ, hψ, rfl⟩ | ⟨ψ, hψ, rfl⟩
        · change (ψ.translate c.inl).translate (hc.desc e) ∈ d.pt.declarations
          rw [Formula.translate_comp]
          change ψ.translate (c.inl ≫ hc.desc e) ∈ d.pt.declarations
          rw [hc.fac e WalkingSpan.left]
          exact d.inl.preserves hψ
        · change (ψ.translate c.inr).translate (hc.desc e) ∈ d.pt.declarations
          rw [Formula.translate_comp]
          change ψ.translate (c.inr ≫ hc.desc e) ∈ d.pt.declarations
          rw [hc.fac e WalkingSpan.right]
          exact d.inr.preserves hψ }
  refine ⟨k, ?_, ?_, ?_⟩
  · apply Hom.ext
    exact hc.fac e WalkingSpan.left
  · apply Hom.ext
    exact hc.fac e WalkingSpan.right
  · intro m hl hr
    apply Hom.ext
    apply PushoutCocone.IsColimit.hom_ext hc
    · exact (congrArg Hom.toPrefunctor hl).trans (hc.fac e WalkingSpan.left).symm
    · exact (congrArg Hom.toPrefunctor hr).trans (hc.fac e WalkingSpan.right).symm

end DPGraph.Pushout
