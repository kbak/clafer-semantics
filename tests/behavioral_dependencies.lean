module

import Clafer.Behavioral
public meta import Lean.Elab.Command

/-! The optional source meaning stays independent of compilation and execution. -/
open Lean in
-- [utest->req~behavioral-snapshot-bridge~1]
run_cmd do
  for name in (← getEnv).header.moduleNames do
    if (`Clafer.Compile).isPrefixOf name || (`Clafer.Verification).isPrefixOf name then
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
#check Clafer.Behavioral.Formula.satisfies_iff_lowered
#check Clafer.Behavioral.StaticObservation.signed_atom_agrees
#check Clafer.Behavioral.Initializers.default_rejected
