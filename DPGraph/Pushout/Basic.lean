module

public import DPGraph.Semantics
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

/-!
[impl->req~dpgraph-pushout-data~1]
[proof->req~dpgraph-pushout-data~1]
-/

/-!
# Declaration unions on carrier cocones

Derived constructions over SoSyM B.4 Definitions 9–10 and the abstract B.5
model reduct. A carrier cocone supplies its point and two commuting graph maps;
its DP-graph declares exactly the translated component declarations. This file
does not assert a universal property or a model-amalgamation theorem.
-/

@[expose] public section

universe s va ua v u vm um

namespace DPGraph.Pushout

open CategoryTheory CategoryTheory.Limits

variable {σ : Signature.{s, va, ua}}
variable {S T U : DPGraph.{s, va, ua, v, u} σ}

/-- Component models whose restrictions to the common source agree. Semantic
universes remain independent in this data type. -/
def CompatibleModels {Ω : Quiv.{vm, um}} (I : Interpretation σ Ω)
    (F : Hom S T) (J : Hom S U) :=
  {p : I.Model T × I.Model U // I.reduct F p.1 = I.reduct J p.2}

variable (F : Hom S T) (J : Hom S U)

/-- Carrier cocones live in the fixed-universe category of bundled quivers. -/
abbrev CarrierCocone :=
  PushoutCocone (C := Quiv.{v, u}) (X := S.carrier) (Y := T.carrier)
    (Z := U.carrier) F.toPrefunctor J.toPrefunctor

/-- The carrier cocone point with exactly the union of the two translated
declaration sets. No injectivity or finiteness is required. -/
def obj (c : CarrierCocone F J) :
    DPGraph.{s, va, ua, v, u} σ where
  carrier := c.pt
  declarations :=
    (fun φ : Formula σ T.carrier => φ.translate c.inl) '' T.declarations ∪
    (fun φ : Formula σ U.carrier => φ.translate c.inr) '' U.declarations

/-- Inclusion of the left component preserves declarations by the left image. -/
def inl (c : CarrierCocone F J) : Hom T (obj F J c) where
  toPrefunctor := c.inl
  preserves hφ := Or.inl ⟨_, hφ, rfl⟩

/-- Inclusion of the right component preserves declarations by the right image. -/
def inr (c : CarrierCocone F J) : Hom U (obj F J c) where
  toPrefunctor := c.inr
  preserves hφ := Or.inr ⟨_, hφ, rfl⟩

/-- The induced DP-graph cocone, using the supplied carrier commutation law. -/
def cocone (c : CarrierCocone F J) :
    PushoutCocone (C := DPGraph.{s, va, ua, v, u} σ) (X := S) (Y := T) (Z := U) F J :=
  PushoutCocone.mk (inl F J c) (inr F J c) (by
    apply Hom.ext
    exact c.condition)

end DPGraph.Pushout
