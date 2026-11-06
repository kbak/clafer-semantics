module

public import FormalCD.Metamodel.Realization.Correctness
public import FormalCD.Metamodel.Realization.Reconstruction
public import Mathlib.Data.Fintype.BigOperators

/-!
[impl->req~formalcd-metamodel-self-instance~1]
[proof->req~formalcd-metamodel-self-instance~1]
-/

/-! # A model of the metamodel obtained by reifying its own syntax
SoSyM §6.1.3 Figure 21c. This is bounded, context-dependent self-instantiation
in the existing DP semantics, not a universe fixed point.
-/

@[expose] public section

namespace FormalCD.Metamodel.Realization.Self
open CategoryTheory DPGraph DPGraph.Predicates

instance : Fintype Declaration where
  elems := {.predefStrIn, .classIn, .mapIn, .predefIn, .singIn, .domIn, .inclIn,
    .nameSet, .predefNameSet, .soSet, .taSet, .predSet, .nameTotal, .nameSingle,
    .predefNameTotal, .predefNameSingle, .soTotal, .soSingle, .taTotal, .taSingle,
    .argsTotal, .predTotal, .predSingle, .classifiersCover, .classifiersDisjoint,
    .predefinedCover, .predefinedDisjoint, .key, .nd, .ad}
  complete d := by cases d <;> simp

/-- Complete indexed arities of the thirty declarations. -/
def arityEdges (d : Declaration) : List (ArrowData (vocabulary.signature.arity (declaration d).symbol)) := by
  cases d
  all_goals first
    | exact [⟨_, _, Arity.UnaryEdge.arrow⟩]
    | exact [⟨_, _, Arity.InEdge.edge 0⟩, ⟨_, _, Arity.InEdge.edge 1⟩]
    | exact [⟨_, _, Arity.OutEdge.edge 0⟩, ⟨_, _, Arity.OutEdge.edge 1⟩]
    | exact [⟨_, _, NameEdge.predefStrIn⟩, ⟨_, _, NameEdge.classIn⟩,
        ⟨_, _, NameEdge.mapIn⟩, ⟨_, _, NameEdge.predefIn⟩, ⟨_, _, NameEdge.singIn⟩,
        ⟨_, _, NameEdge.domIn⟩, ⟨_, _, NameEdge.inclIn⟩, ⟨_, _, NameEdge.name⟩,
        ⟨_, _, NameEdge.predefName⟩]
    | exact [⟨_, _, ArityEdge.so⟩, ⟨_, _, ArityEdge.ta⟩,
        ⟨_, _, ArityEdge.args⟩, ⟨_, _, ArityEdge.pred⟩]

theorem arityEdges_complete (d : Declaration)
    (a : ArrowData (vocabulary.signature.arity (declaration d).symbol)) : a ∈ arityEdges d := by
  cases d <;> rcases a with ⟨x, y, a⟩ <;> cases a
  all_goals try (rename_i i; fin_cases i)
  all_goals simp [arityEdges]

theorem arityEdges_nodup (d : Declaration) : (arityEdges d).Nodup := by
  apply List.Nodup.of_map (f := fun a => edgeCode ((Candidate.ofFormula (declaration d)).argument a))
  cases d <;> decide

instance arityFinite (d : Declaration) :
    Fintype (ArrowData (vocabulary.signature.arity (declaration d).symbol)) where
  elems := ⟨arityEdges d, arityEdges_nodup d⟩
  complete := arityEdges_complete d

def symbolCode : vocabulary.signature.Symbol → Nat
  | .inl .inclusion => 0
  | .inl .setValued => 1
  | .inl .total => 2
  | .inl .singleValued => 3
  | .inl (.cover _) => 4
  | .inl (.disjoint _) => 5
  | .inl (.key _) => 6
  | .inr .nd => 7
  | .inr .ad => 8
  | _ => 9

/-- For this inventory, even the coarser support set separates each symbol's
bindings. This computation does not redefine the general bag key. -/
def fingerprint (d : Declaration) : Nat × Finset Nat :=
  (symbolCode (declaration d).symbol,
    ((arityEdges d).map (fun a => edgeCode ((Candidate.ofFormula (declaration d)).argument a))).toFinset)

theorem fingerprint_injective : Function.Injective fingerprint := by decide

theorem fingerprint_eq (d e : Declaration)
    (hs : (declaration d).symbol = (declaration e).symbol)
    (h : SameArguments diagram ⟨declaration d, declared d⟩ ⟨declaration e, declared e⟩) :
    fingerprint d = fingerprint e := by
  obtain ⟨f, hf⟩ := h
  apply Prod.ext (congrArg symbolCode hs)
  ext k
  constructor
  · intro hk
    obtain ⟨a, _, ha⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨f a, arityEdges_complete _ _, (congrArg edgeCode (hf a)).symm.trans ha⟩)
  · intro hk
    obtain ⟨a, _, ha⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨f.symm a, arityEdges_complete _ _, ?_⟩
    exact (congrArg edgeCode (hf (f.symm a))).trans
      ((congrArg (fun b => edgeCode ((Candidate.ofFormula (declaration e)).argument b))
        (f.apply_symm_apply a)).trans ha)

theorem metamodel_supported : Supported diagram := by
  rintro ⟨_, d, rfl⟩
  cases d
  all_goals first
    | exact ⟨⟨_, _, Arity.UnaryEdge.arrow⟩⟩
    | exact ⟨⟨_, _, Arity.InEdge.edge 0⟩⟩
    | exact ⟨⟨_, _, Arity.OutEdge.edge 0⟩⟩
    | exact ⟨⟨_, _, NameEdge.name⟩⟩
    | exact ⟨⟨_, _, ArityEdge.args⟩⟩

theorem metamodel_separated : Separated diagram := by
  rintro ⟨_, d, rfl⟩ ⟨_, e, rfl⟩ hs hb
  have h := fingerprint_injective (fingerprint_eq d e hs hb)
  subst e
  rfl

theorem declaration_injective : Function.Injective declaration := by
  intro d e h
  apply fingerprint_injective
  apply fingerprint_eq d e (congrArg Formula.symbol h)
  have hd : (⟨declaration d, declared d⟩ : Declared diagram) = ⟨declaration e, declared e⟩ :=
    Subtype.ext h
  rw [hd]
  exact ⟨Equiv.refl _, fun _ => rfl⟩

noncomputable def effectiveFormulasEquiv : Declaration ≃ Declared diagram :=
  Equiv.ofBijective (fun d => ⟨declaration d, declared d⟩)
    ⟨fun _ _ h => declaration_injective (congrArg Subtype.val h), by
      rintro ⟨_, d, rfl⟩; exact ⟨d, rfl⟩⟩

noncomputable def formulaObjectsEquiv : Declaration ≃ extent diagram .formula :=
  effectiveFormulasEquiv.trans (formulas diagram)

noncomputable instance : Fintype (extent diagram .formula) :=
  Fintype.ofEquiv Declaration formulaObjectsEquiv

theorem thirty_formula_objects : Fintype.card (extent diagram .formula) = 30 :=
  (Fintype.card_congr formulaObjectsEquiv).symm.trans (by decide)

noncomputable def argumentLinksEquiv :
    (Σ d : Declaration, ArrowData (vocabulary.signature.arity (declaration d).symbol)) ≃
      ((encode diagram).map Edge.args).Link :=
  (Equiv.sigmaCongrLeft (β := fun f : Declared diagram =>
    ArrowData (vocabulary.signature.arity f.val.symbol)) effectiveFormulasEquiv).trans
    (Equiv.sigmaCongrLeft' (formulas diagram))

noncomputable instance : Fintype (((encode diagram).map Edge.args).Link) :=
  Fintype.ofEquiv _ argumentLinksEquiv

theorem forty_six_argument_links : Fintype.card (((encode diagram).map Edge.args).Link) = 46 := by
  rw [← Fintype.card_congr argumentLinksEquiv, Fintype.card_sigma]
  decide

/-- All thirty formulas, including nd/ad, key and total args, are satisfied. -/
theorem self_instantiation :
    (interpretation (context diagram)).IsModel diagram.toDPGraph (encode diagram) :=
  (model_iff diagram).mpr ⟨metamodel_supported, metamodel_separated⟩

noncomputable def selfModel : (interpretation (context diagram)).Model diagram.toDPGraph :=
  model diagram metamodel_supported metamodel_separated

theorem self_reconstruction :
    decodeRaw (encode diagram) (context diagram) (modes diagram) = diagram.toRawOver :=
  decode_encode diagram

end FormalCD.Metamodel.Realization.Self
