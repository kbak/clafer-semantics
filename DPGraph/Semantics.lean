module

public import DPGraph.Category

/-!
# Abstract interpretation and contravariant model restriction

SoSyM B.5, Theorem 3, abstracted over a semantic graph and predicate meanings.
For each symbol, an interpretation selects the satisfying arity diagrams in
that graph. Formula satisfaction and the model condition are derived from this
selection. Restriction uses only declaration preservation and associativity of
graph-map composition; no closure or invariance axiom on meanings is required.

Semantic vertex/arrow universes are independent of signature and carrier
universes. No graph of all types, concrete span interpretation, or resizing
axiom is supplied here.
-/

@[expose] public section

universe s va ua v₁ u₁ v₂ u₂ v₃ u₃ vm um

namespace DPGraph

open CategoryTheory

-- [impl->req~dpgraph-interpretation~1]
/-- Meaning of each predicate on diagrams of its arity in the chosen semantic
graph. This data does not assume the model restriction theorem. -/
structure Interpretation (σ : Signature.{s, va, ua}) (Ω : Quiv.{vm, um}) where
  meaning : (p : σ.Symbol) → Set (σ.arity p ⥤q Ω)

namespace Interpretation

variable {σ : Signature.{s, va, ua}} {Ω : Quiv.{vm, um}}
variable (I : Interpretation σ Ω)
variable {G : Quiv.{v₁, u₁}} {H : Quiv.{v₂, u₂}}
variable {S : DPGraph.{s, va, ua, v₁, u₁} σ}
variable {T : DPGraph.{s, va, ua, v₂, u₂} σ}
variable {U : DPGraph.{s, va, ua, v₃, u₃} σ}

/-- Interpret a formula by composing its binding with the candidate model. -/
def Satisfies (m : G ⥤q Ω) (φ : Formula σ G) : Prop :=
  φ.binding.comp m ∈ I.meaning φ.symbol

-- [proof->req~dpgraph-interpretation~1]
/-- Satisfaction commutes with translation along any graph map. This is an
equivalence about one formula, not reflection of whole-model satisfaction. -/
theorem satisfies_translate (φ : Formula σ G) (F : G ⥤q H) (m : H ⥤q Ω) :
    I.Satisfies m (φ.translate F) ↔ I.Satisfies (F.comp m) φ := by
  unfold Satisfies Formula.translate
  rw [Prefunctor.comp_assoc]

/-- A model satisfies every declared formula (B.5). -/
def IsModel (S : DPGraph.{s, va, ua, v₁, u₁} σ) (m : S.carrier ⥤q Ω) : Prop :=
  ∀ φ ∈ S.declarations, I.Satisfies m φ

-- [proof->req~dpgraph-declaration-image~1]
/-- An exact declaration image reflects model satisfaction as well as preserving
it. This derived B.5 law requires equality of the declaration sets; an arbitrary
declaration-preserving morphism can have extra target obligations. -/
theorem isModel_iff_of_declarations_image (F : S.carrier ⥤q T.carrier)
    (h : T.declarations = (fun φ => φ.translate F) '' S.declarations)
    (m : T.carrier ⥤q Ω) : I.IsModel T m ↔ I.IsModel S (F.comp m) := by
  constructor
  · intro hm φ hφ
    apply (I.satisfies_translate φ F m).mp
    exact hm _ (h ▸ ⟨φ, hφ, rfl⟩)
  · intro hm φ hφ
    rw [h] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    exact (I.satisfies_translate ψ F m).mpr (hm ψ hψ)

/-- An indexed bank may repeat formulas; no injectivity or argument-key
hypothesis is needed to characterize its model condition. -/
theorem isModel_range {ι : Sort*} (φ : ι → Formula σ G) (m : G ⥤q Ω) :
    I.IsModel ⟨G, Set.range φ⟩ m ↔ ∀ i, I.Satisfies m (φ i) := by
  constructor
  · intro hm i; exact hm _ ⟨i, rfl⟩
  · rintro hm _ ⟨i, rfl⟩; exact hm i

/-- Exact-image specialization for formula banks, including isolated vertices,
repeated arguments and collisions between translated formulas. -/
theorem isModel_range_translate {ι : Sort*} (φ : ι → Formula σ G)
    (F : G ⥤q H) (m : H ⥤q Ω) :
    I.IsModel ⟨H, Set.range (fun i => (φ i).translate F)⟩ m ↔
      I.IsModel ⟨G, Set.range φ⟩ (F.comp m) := by
  refine I.isModel_iff_of_declarations_image
    (S := ⟨G, Set.range φ⟩) (T := ⟨H, Set.range (fun i => (φ i).translate F)⟩) F ?_ m
  ext ψ
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨φ i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩

-- [proof->req~dpgraph-model-reduct~1]
/-- B.5 Theorem 3 in its generic form: a target model restricts to a source
model along a declaration-preserving DP morphism. The only hypotheses are the
fixed interpretation, the DP morphism and the target's model proof. -/
theorem isModel_reduct (F : Hom S T) (m : T.carrier ⥤q Ω) (hm : I.IsModel T m) :
    I.IsModel S (F.toPrefunctor.comp m) := by
  intro φ hφ
  exact (I.satisfies_translate φ F.toPrefunctor m).mp (hm _ (F.preserves hφ))

/-- Models retain the interpreting graph map as well as its satisfaction proof. -/
def Model (S : DPGraph.{s, va, ua, v₁, u₁} σ) :=
  {m : S.carrier ⥤q Ω // I.IsModel S m}

-- [impl->req~dpgraph-model-reduct~1]
/-- Contravariant restriction by precomposition. -/
def reduct (F : Hom S T) (m : I.Model T) : I.Model S :=
  ⟨F.toPrefunctor.comp m.val, I.isModel_reduct F m.val m.property⟩

@[simp] theorem reduct_val (F : Hom S T) (m : I.Model T) :
    (I.reduct F m).val = F.toPrefunctor.comp m.val := rfl

@[simp] theorem reduct_id (m : I.Model S) : I.reduct (Hom.id S) m = m :=
  Subtype.ext (Prefunctor.id_comp m.val)

/-- Restricting along a composite first restricts along its second map. -/
theorem reduct_comp (F : Hom S T) (J : Hom T U) (m : I.Model U) :
    I.reduct (F.comp J) m = I.reduct F (I.reduct J m) :=
  Subtype.ext (Prefunctor.comp_assoc F.toPrefunctor J.toPrefunctor m.val)

end Interpretation
end DPGraph
