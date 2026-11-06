module

import Clafer.Semantics.Structural
import Clafer.Constraints.Denotation
public meta import Lean.Elab.Command

/-!
[itest->req~clafer-compile-groups~1]
[itest->req~clafer-effective-core~1]
[itest->req~clafer-integer-extraction~1]
[proof->req~formalcd-integer-realization~1]
-/

/-! Independent structural and expression meanings must not pull in Compile,
the finite checker, or the Figure 21 example to obtain integer infrastructure. -/
open Lean in
run_cmd do
  for name in (← getEnv).header.moduleNames do
    if (`Clafer.Compile).isPrefixOf name || (`Clafer.Verification).isPrefixOf name ||
        (`FormalCD.Telematics).isPrefixOf name then
      throwError "independent semantic module imported {name}"

#check Clafer.Semantics.EffectiveCore
#check Clafer.Semantics.StructuralSatisfies
#check Clafer.Constraints.Expr.denote

universe u
example {U : Type u} (R : FormalCD.IntegerRealization U) (n : Int) :
    R.extract {R.encode n} = some n := R.extract_encoded n

example {U : Type u} (R : FormalCD.IntegerRealization U) :
    R.extract ∅ = none := R.extract_empty

example {U : Type u} (R : FormalCD.IntegerRealization U) {x : U} (h : x ∉ R.domain) :
    R.extract {x} = none := R.extract_wrong_domain h
