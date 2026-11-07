module

import Clafer
public meta import Lean.Elab.Command

/-! The existing public entry point remains usable without the optional extension. -/
open Lean in
-- [utest->req~behavioral-snapshot-bridge~1]
run_cmd do
  for name in (← getEnv).header.moduleNames do
    if (`Clafer.Behavioral).isPrefixOf name then
      throwError "structural entry point imported optional behavioral module {name}"
