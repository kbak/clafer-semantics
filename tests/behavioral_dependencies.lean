module

import Clafer.Behavioral
public meta import Lean.Elab.Command

/-! The optional source meaning stays independent of compilation and execution. -/
open Lean in
-- [utest->req~behavioral-snapshot-bridge~1]
run_cmd do
  for name in (← getEnv).header.moduleNames do
    if [ `Clafer.Compile, `Clafer.Verification,
         `Clafer.Behavioral.Lasso, `Clafer.Behavioral.Orbit,
         `Clafer.Behavioral.FiniteEvaluation, `Clafer.Behavioral.LassoValidation,
         `Clafer.Behavioral.FiniteSets, `Clafer.Behavioral.Verification,
         `Clafer.Behavioral.FinitePartial, `Clafer.Behavioral.FiniteComposition ].any
         (fun executionModule => executionModule.isPrefixOf name) then
      throwError "behavioral source semantics imported {name}"

#check Clafer.Behavioral.Trace.admissible_projection
#check Clafer.Behavioral.StaticCorrespondence.constant_admissible
#check Clafer.Behavioral.Formula.normalize_lower_agrees
#check Clafer.Behavioral.Formula.persistent_eventually_consistent
#check Clafer.Semantics.Groups.ChildObjects
#check Clafer.Semantics.Groups.Holds
#check Clafer.Behavioral.GroupObservation.holds_iff
#check Clafer.Behavioral.ReferenceObservation.snapshot_assignments
#check Clafer.Behavioral.ReferenceObservation.valid_finite_targets
#check Clafer.Behavioral.InheritedReference.Owner.unique
#check Clafer.Behavioral.InheritedReference.shared_head
#check Clafer.Behavioral.IntegerObservation.coerce_defined_iff
#check Clafer.Behavioral.IntegerObservation.agrees_with_extract
#check Clafer.Behavioral.Arithmetic.defined_iff
#check Clafer.Behavioral.Aggregate.fold_defined_iff
#check Clafer.Behavioral.Aggregate.select_singleton
#check Clafer.Behavioral.Structural.valid_iff_common
#check Clafer.Behavioral.Structural.Valid.refined_reference_agrees
#check Clafer.Behavioral.StructuralBinding.Resolution.ofRoles
#check Clafer.Behavioral.StructuralBinding.Resolution.coherent
#check Clafer.Behavioral.CapturedStatic.agrees
#check Clafer.Behavioral.PrimitiveExpression.finite_reference_operand
#check Clafer.Behavioral.Formula.extension_agrees
#check Clafer.Behavioral.Formula.total_agrees
#check Clafer.Behavioral.Formula.letSet_next_of_stable
#check Clafer.Behavioral.Formula.letSet_undefined_neither
#check Clafer.Behavioral.Formula.satisfies_iff_lowered
#check Clafer.Behavioral.StaticObservation.signed_atom_agrees
#check Clafer.Behavioral.Initializers.Legacy.default_rejected
#check Clafer.Behavioral.AbsentReference.raw_empty
#check Clafer.Behavioral.AbsentReference.next_equalValue_live
#check Clafer.Behavioral.AbsentReference.counter_alive
#check Clafer.Behavioral.AbsentReference.forced_disappearance_unsat
#check Clafer.Behavioral.Formula.checkedCore_agrees
#check Clafer.Behavioral.Properties.Model.behavioral_core_iff
#check Clafer.Behavioral.Properties.Model.constant_iff

#check Clafer.Behavioral.Initializers.expansion_agrees
#check Clafer.Behavioral.Initializers.Transport.observation_preserved
#check Clafer.Behavioral.Initializers.Structure.single_fibers
#check Clafer.Behavioral.Initializers.Static.production_constant_agreement
#check Clafer.Behavioral.Initializers.Finality.production_equivalence
