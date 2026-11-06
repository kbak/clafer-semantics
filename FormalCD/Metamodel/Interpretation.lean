module

public import FormalCD.Metamodel.Discipline
public import FormalCD.Semantics

/-! # Extended interpretation: built-in meanings plus nd/ad
The exact domain is bounded subsets/spans over U, with the explicit context
below. Arbitrary raw diagrams do not recover vertex/index/registry information.
-/

@[expose] public section

universe p s va ua v u z w

namespace FormalCD.Metamodel
open CategoryTheory DPGraph DPGraph.Predicates

structure Context (R : Registry.{p}) (σ : Signature.{s,va,ua}) (G : Quiv.{v,u}) (U : Type z) where
  names : NameContext R U
  arities : ArityContext σ G U
  describe : ∀ d : arityShape ⥤q semanticGraph.{z,w} U,
    ArityDescriptor (σ := σ) (G := G) d

-- [impl->req~formalcd-metamodel-disciplines~1]
def interpretation {R : Registry.{p}} {σ : Signature.{s,va,ua}} {G : Quiv.{v,u}}
    {U : Type z} (C : Context.{p,s,va,ua,v,u,z,w} R σ G U) :
    Interpretation vocabulary.signature (semanticGraph.{z,w} U) :=
  Vocabulary.extendInterpretation (Predicates.interpretation U)
    { meaning
        | .nd => NameDiscipline C.names
        | .ad => fun d => ArityDiscipline C.arities d (C.describe d) }

theorem builtins_unchanged {R : Registry.{p}} {σ : Signature.{s,va,ua}} {G : Quiv.{v,u}}
    {U : Type z} (C : Context.{p,s,va,ua,v,u,z,w} R σ G U) :
    vocabulary.restrict (interpretation C) = Predicates.interpretation U := rfl

-- [proof->req~formalcd-metamodel-disciplines~1]
theorem satisfies_nd {R : Registry.{p}} {σ : Signature.{s,va,ua}} {G : Quiv.{v,u}}
    {U : Type z} (C : Context.{p,s,va,ua,v,u,z,w} R σ G U)
    (m : graph ⥤q semanticGraph.{z,w} U) :
    (interpretation C).Satisfies m nd ↔ NameDiscipline C.names (nameBinding.comp m) := Iff.rfl

theorem satisfies_ad {R : Registry.{p}} {σ : Signature.{s,va,ua}} {G : Quiv.{v,u}}
    {U : Type z} (C : Context.{p,s,va,ua,v,u,z,w} R σ G U)
    (m : graph ⥤q semanticGraph.{z,w} U) :
    (interpretation C).Satisfies m ad ↔
      ArityDiscipline C.arities (arityBinding.comp m) (C.describe (arityBinding.comp m)) := Iff.rfl

-- [proof->req~formalcd-formula-identity~1]
theorem satisfies_literalKey {R : Registry.{p}} {σ : Signature.{s,va,ua}} {G : Quiv.{v,u}}
    {U : Type z} (C : Context.{p,s,va,ua,v,u,z,w} R σ G U)
    (m : graph ⥤q semanticGraph.{z,w} U) :
    (interpretation C).Satisfies m literalKey ↔
      Key (fun i => (keyBinding.comp m).map (Arity.OutEdge.edge i)) := Iff.rfl

end FormalCD.Metamodel
