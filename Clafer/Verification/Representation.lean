module

public import Clafer.Verification.Finite
public import Clafer.Semantics.Renaming
public import Clafer.Semantics.Normalization

-- [proof->req~clafer-structural-satisfaction~1]

/-!
# Completeness of the finite relational candidate domain

Every finite shared-object relational presentation has an encoding, independently
of whether it satisfies the constraints. Together with `ordinary_representation`,
ordinary set-valued span models have tuple presentations up to link isomorphism;
derived reference spans retain their pullback links.
-/

@[expose] public section
namespace Clafer.Verification
open Semantics CategoryTheory

variable {n : Nat} {U : Type}

/-- An existence/representation construction, not a production generator. -/
noncomputable def encode [Fintype U] (s : Configuration (Fin n) U) : Candidate n := by
  classical
  let e := Fintype.equivFin U
  exact {
    size := Fintype.card U
    root := e s.root
    head := fun d x => decide (e.symm x ∈ s.head d)
    contains := fun d p x => decide (s.contains d (e.symm p) (e.symm x))
    deref := fun d x t => decide (s.deref d (e.symm x) (e.symm t)) }

theorem realize_encode [Fintype U] (s : Configuration (Fin n) U) :
    realize (encode s) = s.rename (Fintype.equivFin U) := by
  classical
  simp [encode, realize, Configuration.rename]

theorem representable [Fintype U] (m : EffectiveCore n) (s : Configuration (Fin n) U) :
    StructuralSatisfies m (realize (encode s)) ↔ StructuralSatisfies m s := by
  rw [realize_encode]
  exact structural_rename m s _

/-- Every finite interpreted whole-model configuration has a candidate with
exactly its shared objects and tuple relations, up to the displayed bijection.
The normalizer derives ordinary/parent/target/inclusion link isomorphisms from
the actual local bank. Global clauses are the additional whole-model contract. -/
theorem finite_model_representable [Fintype U] (m : EffectiveCore n)
    (g : m.family.canonicalRoles.graph ⥤q DPGraph.Predicates.semanticGraph.{0,0} U)
    (root : U) (wf : m.WellFormed) (support : m.Supported)
    (model : (DPGraph.Predicates.interpretation U).IsModel
      (Compile.localFormulas m.family).diagram g)
    (global : (SpanModel.normalize m g root).GlobalConditions m) :
    ∃ c : Candidate n, ∃ e : U ≃ Fin c.size,
      realize c = (SpanModel.normalize m g root).rename e ∧ check m c = true := by
  let s := SpanModel.normalize m g root
  refine ⟨encode s, Fintype.equivFin U, realize_encode s, ?_⟩
  apply (check_correct m (encode s) wf support).mpr
  apply (representable m s).mpr
  exact SpanModel.normalize_satisfies m g root model wf support global

end Clafer.Verification
