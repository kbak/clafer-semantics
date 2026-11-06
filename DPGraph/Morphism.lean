module

public import DPGraph.Basic

/-! # Declaration-preserving morphisms (SoSyM B.4, Definition 10) -/

@[expose] public section

universe s va ua v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

namespace DPGraph

variable {σ : Signature.{s, va, ua}}

-- [impl->req~dpgraph-morphisms~1]
/-- Preservation concerns declared formulas, without adding inference closure. -/
structure Hom (G : DPGraph.{s, va, ua, v₁, u₁} σ)
    (H : DPGraph.{s, va, ua, v₂, u₂} σ) where
  toPrefunctor : G.carrier ⥤q H.carrier
  preserves : ∀ {f}, f ∈ G.declarations → f.translate toPrefunctor ∈ H.declarations

namespace Hom

variable {G : DPGraph.{s, va, ua, v₁, u₁} σ} {H : DPGraph.{s, va, ua, v₂, u₂} σ}
variable {K : DPGraph.{s, va, ua, v₃, u₃} σ} {L : DPGraph.{s, va, ua, v₄, u₄} σ}

/-- Preservation proofs do not distinguish morphisms with the same graph map. -/
@[ext] theorem ext {F J : Hom G H} (h : F.toPrefunctor = J.toPrefunctor) : F = J := by
  cases F
  cases J
  cases h
  rfl

/-- Pointwise graph-map extensionality, reusing `Prefunctor.ext`. -/
theorem ext_of_obj_map {F J : Hom G H}
    (h_obj : ∀ x, F.toPrefunctor.obj x = J.toPrefunctor.obj x)
    (h_map : ∀ (x y : G.carrier) (a : x ⟶ y),
      F.toPrefunctor.map a =
        Eq.recOn (h_obj y).symm (Eq.recOn (h_obj x).symm (J.toPrefunctor.map a))) : F = J :=
  ext (Prefunctor.ext h_obj h_map)

/-- Identity preserves every declaration by identity translation. -/
def id (G : DPGraph.{s, va, ua, v₁, u₁} σ) : Hom G G where
  toPrefunctor := Prefunctor.id G.carrier
  preserves hf := by simpa only [Formula.translate_id] using hf

/-- Composing preservation proofs uses the formula translation law. -/
def comp (F : Hom G H) (J : Hom H K) : Hom G K where
  toPrefunctor := F.toPrefunctor.comp J.toPrefunctor
  preserves hf := by
    rw [← Formula.translate_comp]
    exact J.preserves (F.preserves hf)

-- [proof->req~dpgraph-morphisms~1]
theorem comp_preserves (F : Hom G H) (J : Hom H K) {f : Formula σ G.carrier}
    (hf : f ∈ G.declarations) :
    f.translate (F.toPrefunctor.comp J.toPrefunctor) ∈ K.declarations :=
  (F.comp J).preserves hf

-- [proof->req~dpgraph-category~1]
@[simp] theorem id_comp (F : Hom G H) : (id G).comp F = F :=
  ext (Prefunctor.id_comp F.toPrefunctor)

@[simp] theorem comp_id (F : Hom G H) : F.comp (id H) = F :=
  ext (Prefunctor.comp_id F.toPrefunctor)

theorem comp_assoc (F : Hom G H) (J : Hom H K) (M : Hom K L) :
    (F.comp J).comp M = F.comp (J.comp M) :=
  ext (Prefunctor.comp_assoc F.toPrefunctor J.toPrefunctor M.toPrefunctor)

end Hom
end DPGraph
