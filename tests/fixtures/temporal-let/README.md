# Temporal let comparison inputs

These original Clafer inputs distinguish the accepted D1/D3 captured-value
contract from the syntactic substitution in `gsdlab/clafer` at
`fca0deb9c766261f5c0d2ae57af4ba9b07e1279a`. They are supplementary investigation
inputs, not additions to the supported 0.5.7 importer or its default comparison
suite. The [source disposition](../../../docs/sources.md#temporal-let-substitution)
and [formula contract](../../../docs/behavioral-formulas.md#let-capture-and-substitution)
own the meaning and limits. Executed comparison evidence belongs to
[issue #174](https://github.com/kbak/clafer-semantics/issues/174) and its PR.

For replay, compile the inputs with the exact candidate to explicit Clafer,
JSON and Alloy. Inspect the resolved explicit bodies before solving. Use Alloy
6.2.0/SAT4J with four-bit integers and an upper bound of one identity per user
signature; temporal cases use exactly four states with a final-to-earlier loop.
The declaration cardinalities force the reference heads present in every state;
`a ?` permits absence and rebirth. All top-level constraints attach to the
persistent synthetic root. There is no parent-cancellation escape. No arithmetic
operation remains in the emitted unused-binding case, so its result is independent
of Alloy's division-by-zero convention. Overflow exclusion is disabled.

| Input | Expected candidate behavior | Purpose |
| --- | --- | --- |
| `baseline.cfr` | SAT | The changing reference alone is consistent. |
| `target.cfr` | UNSAT | Substitution requires both 1 and 2 in the next state. Captured-value meaning retains `{1}`. |
| `same-state.cfr` | SAT | A defined same-state use agrees. |
| `head.cfr` | SAT | Current dereference of the stable captured head sees 2. The identity bound ensures the single head cannot be replaced. |
| `changing-set.cfr` | UNSAT | Substitution sees an empty extent after disappearance; a captured set retains its identity. |
| `rebirth.cfr` | UNSAT | Later rebirth cannot repair the substituted next-state nonemptiness failure. |
| `shadow.cfr` | SAT | The inner `let` hides the outer name. |
| `rename.cfr`, `rename-control.cfr` | SAT | Renaming the inner binder preserves the outer reference target 1 independently of the inner target 2. |
| `unused.cfr` | SAT | Substitution erases an unused undefined RHS; strict D3 capture rejects it. |

Independent capture controls replace only the candidate's substituted `let`
constraint, retaining the baseline structure and trace conditions. At time zero,
existentially bind `old : Int` equal to the reference target, then require
`after (old = 1)`. For the optional head, bind `old : a` equal to the initial
head set and require `after (some old)`; the rebirth control additionally requires
`after after (old = alive_a)`. These controls are SAT in the stated bounds.
They use singleton quantification because these particular initial values are
singletons; this is not an encoding of general set-valued `let`. Alloy `let`
also substitutes an expression and cannot serve as a value-freezing control.

The controls are independently written comparison models, not emitted Haskell
output or a compiler-correctness proof. The checked source counterexample and
stable-domain law live in `LetCaptureExamples.lean` and `LetCapture.lean` under
`Clafer/Behavioral`. Lexical names have already been resolved in those APIs;
parsing and alpha-renaming remain frontend obligations.
