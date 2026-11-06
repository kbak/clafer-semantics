module

public import FormalCD.Metamodel.Basic
public import FormalCD.Metamodel.Binding

/-!
# Bounded syntactic self-description

SoSyM §6.1.3 / Figure 21c says MCD is itself a formal CD. The checked statement
here means representation in the same `CDOver` family as ordinary formal CDs
and Figure 21b. It does not mean that MCD satisfies itself as a semantic instance.
All six syntax/registry universes below are zero; the signature is the built-in
vocabulary extended by nd/ad and the registry is the existing SING registry.
Class, Map and Signature are ordinary `Metamodel.Node` constructors. Full graph
bindings use the existing equivalence, including isolated vertices and zero-arrow
arities. No claim about literal-key or total-args satisfaction follows.
-/

@[expose] public section

namespace FormalCD

-- [proof->req~formalcd-bounded-self-description~1]
/-- Exact representation of the delivered metamodel, without rebuilding it. -/
theorem bounded_self_description :
    ∃ D : CDOver.{0,0,0,0,0,0} Metamodel.vocabulary Metamodel.registry,
      D = Metamodel.diagram ∧ D.toRawOver = Metamodel.raw ∧
      D.toRawOver.WellFormed ∧
      Fintype.card Metamodel.Node = 11 ∧ Metamodel.edges.length = 13 :=
  ⟨Metamodel.diagram, rfl, rfl, Metamodel.wellFormed,
    Metamodel.eleven_nodes, Metamodel.thirteen_arrows⟩

-- [impl->req~formalcd-bounded-self-description~1]
/-- The representation keeps the existing full formula identity, not its bag projection. -/
def metamodelFormulaRepresentation :
    {c : Metamodel.Candidate Metamodel.vocabulary.signature Metamodel.graph // c.Valid} ≃
      DPGraph.Formula Metamodel.vocabulary.signature Metamodel.graph :=
  Metamodel.Candidate.formulaEquiv

theorem metamodel_formula_roundtrip
    (f : DPGraph.Formula Metamodel.vocabulary.signature Metamodel.graph) :
    metamodelFormulaRepresentation (metamodelFormulaRepresentation.symm f) = f :=
  metamodelFormulaRepresentation.apply_symm_apply f

end FormalCD
