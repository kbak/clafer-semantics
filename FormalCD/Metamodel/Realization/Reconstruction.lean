module

public import FormalCD.Metamodel.Realization.Context

/-! # Reconstruction from the explicit semantic representation
SoSyM B.4 Definition 8. Decode the effective declaration set, names, identifiers
and the separately retained mode data. The bare drawing cannot recover modes
or full bindings. The decoder takes no original source CD and no IsModel proof.
-/

@[expose] public section

universe p s va ua v u z w
namespace FormalCD.Metamodel.Realization
open CategoryTheory DPGraph

/-- Explicit side data: Incl membership alone loses ordinary-versus-bag mode. -/
structure ModeData (G : Quiv.{v,u}) where
  mode : ArrowData G → MapMode

-- [impl->req~formalcd-metamodel-realization~1]
/-- Decode on the represented carrier using context embeddings, full candidates
and mode side data. This operation also makes sense for malformed representations. -/
def decodeRaw {V : Vocabulary.{s,va,ua}} {R : Registry.{p}} {G : Quiv.{v,u}} {U : Type z}
    (m : graph ⥤q Predicates.semanticGraph.{z,w} U)
    (C : Context.{p,s,va,ua,v,u,z,w} R V.signature G U) (M : ModeData G) :
    RawOver V R where
  carrier := G
  declarations := {φ | ∃ f : objects (arityBinding.comp m) .formula,
    (C.describe (arityBinding.comp m)).candidate f = some (Candidate.ofFormula φ)}
  className c := C.names.name (C.arities.vertex c)
  mapName e := C.names.name (C.arities.arrow ⟨_, _, e⟩)
  predefined c := C.names.identifier (C.arities.vertex c)
  mode e := M.mode ⟨_, _, e⟩

variable {V : Vocabulary.{s,va,ua}} {R : Registry.{p}}
variable (D : CDOver.{s,va,ua,p,v,u} V R)

def modes : ModeData D.carrier := ⟨fun e => D.mode e.2.2⟩

/-- Every formula and every binding vertex is retained, even without support
or separation. This includes isolated vertices and repeated argument images. -/
theorem candidate_roundtrip (f : Declared D) :
    (descriptor D).candidate (formulas D f) = some (Candidate.ofFormula f.val) := by
  change some (Candidate.ofFormula ((formulas D).symm (formulas D f)).val) = _
  rw [Equiv.symm_apply_apply]

theorem decoded_declarations :
    (decodeRaw (encode D) (context D) (modes D)).declarations = D.declarations := by
  ext φ
  change (∃ f, ((context D).describe (arityBinding.comp (encode D))).candidate f =
    some (Candidate.ofFormula φ)) ↔ _
  rw [context_describe]
  constructor
  · rintro ⟨f, hf⟩
    have he : Candidate.ofFormula ((formulas D).symm f).val = Candidate.ofFormula φ :=
      Option.some.inj hf
    rw [← (full_binding_identity _ _).mp he]
    exact ((formulas D).symm f).property
  · intro h
    exact ⟨formulas D ⟨φ, h⟩, candidate_roundtrip D ⟨φ, h⟩⟩

-- [proof->req~formalcd-metamodel-realization~1]
/-- Exact reconstruction of the whole raw syntax on its original carrier;
the source itself is not an argument of decodeRaw. -/
theorem decode_encode : decodeRaw (encode D) (context D) (modes D) = D.toRawOver := by
  have hd := decoded_declarations D
  change RawOver.mk ⟨D.carrier,
    (decodeRaw (encode D) (context D) (modes D)).declarations⟩
    D.className (fun e => D.mapName e) D.predefined (fun e => D.mode e) = _
  rw [hd]

end FormalCD.Metamodel.Realization
