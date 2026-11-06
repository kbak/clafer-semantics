module

public import DPGraph.Signature

/-! # Formulas and translation (SoSyM B.4, Definitions 8 and 10) -/

@[expose] public section

universe s va ua v₁ u₁ v₂ u₂ v₃ u₃

namespace DPGraph

open CategoryTheory

-- [impl->req~dpgraph-core~1]
/-- A well-typed formula retains its entire arity graph, including isolated
vertices and distinct arrows that may bind to the same carrier arrow. -/
structure Formula (σ : Signature.{s, va, ua}) (G : Quiv.{v₁, u₁}) where
  symbol : σ.Symbol
  binding : σ.arity symbol ⥤q G

namespace Formula

variable {σ : Signature.{s, va, ua}}
variable {G : Quiv.{v₁, u₁}} {H : Quiv.{v₂, u₂}} {K : Quiv.{v₃, u₃}}

-- [impl->req~formula-translation~1]
/-- Translate by postcomposition, with the signature fixed (Definition 10). -/
def translate (f : Formula σ G) (F : G ⥤q H) : Formula σ H :=
  ⟨f.symbol, f.binding.comp F⟩

-- [proof->req~formula-translation~1]
@[simp] theorem translate_id (f : Formula σ G) :
    f.translate (Prefunctor.id G) = f := by
  cases f
  simp only [translate, Prefunctor.comp_id]

theorem translate_comp (f : Formula σ G) (F : G ⥤q H) (J : H ⥤q K) :
    (f.translate F).translate J = f.translate (F.comp J) := by
  exact congrArg (Formula.mk f.symbol) (Prefunctor.comp_assoc f.binding F J)

end Formula
end DPGraph
