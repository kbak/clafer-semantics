module

import FormalCD
public meta import Lean.Elab.Command

-- [itest->req~lean-validation~1]

/-! FormalCD is reusable without Clafer or acceptance example imports.
The existing public_imports test independently guards the DPGraph root. -/

#check FormalCD.Registry
#check FormalCD.Raw
#check FormalCD.Raw.WellFormed
#check FormalCD.Raw.WellFormed.predefined_name
#check FormalCD.Raw.WellFormed.ordinary_decl
#check FormalCD.Hom.toDPHom
#check FormalCD.CD
#check FormalCD.Hom.ext
#check FormalCD.Hom.ext_of_map
#check FormalCD.Hom.toDPHom_id
#check FormalCD.Hom.toDPHom_comp

open Lean in
run_cmd do
  let env ← getEnv
  for name in env.header.moduleNames do
    if (`Clafer).isPrefixOf name || (`FormalCD.Examples).isPrefixOf name ||
        (`FormalCD.SemanticsExamples).isPrefixOf name ||
        (`FormalCD.Metamodel.Examples).isPrefixOf name ||
        (`FormalCD.Metamodel.InterpretationExamples).isPrefixOf name ||
        (`FormalCD.Metamodel.NameExamples).isPrefixOf name ||
        (`FormalCD.Metamodel.Realization.Examples).isPrefixOf name ||
        (`FormalCD.Telematics.Examples).isPrefixOf name then
      throwError "independent FormalCD entrypoint imported {name}"

universe p v₁ u₁ v₂ u₂ v₃ u₃ vm um
open FormalCD CategoryTheory
variable {R : Registry.{p}} {S : CD.{p,v₁,u₁} R} {T : CD.{p,v₂,u₂} R}
variable {U : CD.{p,v₃,u₃} R} (F : Hom S T) (J : Hom T U)
variable {Ω : Quiv.{vm,um}} (I : DPGraph.Interpretation DPGraph.Predicates.signature Ω)

example : (Hom.id S).comp F = F := Hom.id_comp F
example : F.comp (Hom.id T) = F := Hom.comp_id F
example (m : I.Model T.toDPGraph) : I.Model S.toDPGraph := F.reduct I m
example (m : I.Model U.toDPGraph) :
    (F.comp J).reduct I m = F.reduct I (J.reduct I m) := Hom.reduct_comp I F J m

#check FormalCD.Metamodel.diagram
#check FormalCD.Metamodel.Candidate.formulaEquiv
#check FormalCD.Metamodel.satisfies_literalKey
#check FormalCD.Vocabulary.embed_injective

section Extended
universe s va ua
variable {V : Vocabulary.{s,va,ua}}
variable {A : CDOver.{s,va,ua,p,v₁,u₁} V R} {B : CDOver.{s,va,ua,p,v₂,u₂} V R}
variable {C : CDOver.{s,va,ua,p,v₃,u₃} V R}
variable (f : HomOver A B) (g : HomOver B C)
variable (J : DPGraph.Interpretation V.signature Ω)
example : (HomOver.id A).comp f = f := HomOver.id_comp f
example : f.comp (HomOver.id B) = f := HomOver.comp_id f
example : (f.comp g).toDPHom = f.toDPHom.comp g.toDPHom := rfl
example (m : J.Model C.toDPGraph) :
    (f.comp g).reduct J m = f.reduct J (g.reduct J m) := HomOver.reduct_comp J f g m
open FormalCD.Metamodel Realization in
example : (interpretation (context A)).IsModel diagram.toDPGraph (encode A) ↔
    Supported A ∧ Separated A := model_iff A

open FormalCD.Metamodel.Realization in
example : decodeRaw (encode A) (context A) (modes A) = A.toRawOver := decode_encode A
end Extended

#check FormalCD.bounded_self_description
#check FormalCD.metamodelFormulaRepresentation
#check FormalCD.Telematics.diagram
#check FormalCD.Telematics.declaration_injective
#check FormalCD.Telematics.satisfies_vc_iff_guarded
#check FormalCD.Telematics.builtins_unchanged
#check FormalCD.Telematics.twelve_effective_formulas
#check FormalCD.Telematics.declared_vc_iff_guarded

#check FormalCD.Metamodel.Realization.Self.self_instantiation
#check FormalCD.Metamodel.Realization.Self.self_reconstruction
#check FormalCD.Metamodel.Realization.Self.thirty_formula_objects
#check FormalCD.Metamodel.Realization.Self.forty_six_argument_links

#check FormalCD.IntegerRealization.extract_eq_some_iff
#check FormalCD.IntegerRealization.extract_none_iff
#check FormalCD.IntegerRealization.objectEquiv
#check FormalCD.Gluing.Compatible
#check FormalCD.Gluing.Defaults
#check FormalCD.Gluing.raw_wellFormed
