module

public import DPGraph.Semantics

/-!
# Injectivity and surjectivity of model reducts

Derived library consequences of the abstract model reduct and its laws, grounded
in SoSyM B.4 Definitions 9–10 and the abstract B.5 Theorem 3. These are additional
results, not verbatim theorems from the paper or concrete Clafer/span semantics.
-/

@[expose] public section

universe s va ua v₁ u₁ v₂ u₂ vm um

namespace DPGraph.Interpretation

variable {σ : Signature.{s, va, ua}} {Ω : CategoryTheory.Quiv.{vm, um}}
variable (I : Interpretation σ Ω)
variable {S : DPGraph.{s, va, ua, v₁, u₁} σ}
variable {T : DPGraph.{s, va, ua, v₂, u₂} σ}
variable {F : Hom S T} {J : Hom T S}

-- [proof->req~model-reduct-injective~1]
/-- A composite equal to the target identity makes restriction injective. -/
theorem reduct_injective_of_comp_eq_id (h : J.comp F = Hom.id T) :
    Function.Injective (I.reduct F) := by
  intro m n hmn
  have h' := congrArg (I.reduct J) hmn
  simpa only [← I.reduct_comp, h, I.reduct_id] using h'

-- [proof->req~model-reduct-surjective~1]
/-- A composite equal to the source identity supplies a preimage for every model. -/
theorem reduct_surjective_of_comp_eq_id (h : F.comp J = Hom.id S) :
    Function.Surjective (I.reduct F) := by
  intro m
  refine ⟨I.reduct J m, ?_⟩
  rw [← I.reduct_comp, h, I.reduct_id]

end DPGraph.Interpretation
