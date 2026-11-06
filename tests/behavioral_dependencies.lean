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
