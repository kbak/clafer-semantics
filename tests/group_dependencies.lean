module

import Clafer.Compile.GroupSemantics
public meta import Lean.Elab.Command

/-!
[itest->req~clafer-compile-groups~1]
[itest->req~clafer-effective-core~1]
[itest->req~clafer-integer-extraction~1]
-/

/-! Group mathematics uses the generic finite-range specialization, with no
reverse dependency on candidate tables, checker algorithms or protocols. -/
open Lean in
run_cmd do
  for name in (← getEnv).header.moduleNames do
    if (`Clafer.Verification).isPrefixOf name then
      throwError "group semantics imported checker module {name}"

#check Clafer.Compile.Groups.finite_bounds
#check Clafer.Compile.Groups.empty_holds_iff
#check Clafer.Semantics.EffectiveCore.erase
#check Clafer.Semantics.EffectiveCore.erase_wellFormed
