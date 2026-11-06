# Finite behavioral verification

Import `Clafer.Behavioral.Verification` for an executable exact-candidate checker.
The source entry point `Clafer.Behavioral` continues to import only independent
meaning and its proofs. The [formula contract](behavioral-formulas.md) defines
truth over infinite traces; finite evaluation is related to that meaning by
kernel-checked theorems. The existing [structural checker](structural-checker.md),
static comparison protocol and oracle pins are unchanged.

## Inventory, states and unfolding

`Lasso C size last` stores `last + 1` states, a loop index in `Fin (last + 1)`,
and a shared `Identities C (Fin size)` inventory. State indices before the loop
form a possibly empty prefix; the loop is nonempty. Inventory identities include
absent and unused objects. Direct types and actual parents never change, including
across a gap or the loop edge. Reference occurrences are inventory objects, so
different bag heads may retain the same target. Presence and dereferences are
Boolean tables that may change on every edge.

`next` increments a nonfinal position and sends the final position to the loop
index. `clock` iterates this deterministic step from state zero. `unfold` constructs
an actual `Trace`, with the same identities and the observed live/reference tables
at every natural-number time. `clock_first` proves every stored state is visited.
The finite `Valid` predicate checks the static identity contract, root/parent
presence and every `Trace.StateValid` clause on all stored states.
`valid_iff_unfold` proves equivalence with validity of the infinite unfolding.
Multiplicity and group checks use the existing finite cardinality bridge; absent
pool identities are not required to be live members of a structural snapshot.

`RawLasso` additionally admits repeated type/parent metadata from decoded frames.
`admit` rejects an out-of-range loop or any disagreement with the shared inventory,
including on an absent identity. It cannot repair a parent switch by renaming an
object. Fin indices make out-of-range object/declaration references unrepresentable
in the typed API; a decoder must reject them before construction. An empty decoded
trace is `none` at `checkRaw`, hence malformed. `loopIndex` separately checks
arbitrary state-count/index pairs, including zero states.

## Initial history and exact temporal evaluation

The finite clock contains `(current position, optional previous position)`.
Its initial previous position is `none`; every transition records the state just
left. `Starts` therefore tests time zero on the initial visit and the actual
predecessor on subsequent visits. For loop entry 3 with a birth there, the first
arrival can start a lifetime while later self-loop visits do not. A root present
throughout starts once even when the lasso loops to state zero. `Ends` uses the
actual successor, including the final-to-loop edge.

`starts_agrees`, `ends_agrees` and `parentPresent_agrees` relate these finite
observations to the independent trace definitions at every absolute time. No
general past-time operator is introduced; the history component is sufficient
for the accepted core's lifetime anchors. Arbitrary history-dependent source
atoms need their own finite representation and agreement evidence.

For a finite deterministic state space S, `Orbit.representative` proves that each
future state has a representative at an offset less than `card S` and no later
than the original visit. The proof removes a repeated segment from a shortest
visit. `some_iff`, `every_iff` and `until_iff` use that result for eventuality,
always and strong until. Shortening an until endpoint retains all preceding
left-operand requirements. Weak until is always-or-strong-until.

`Core.finite` recursively evaluates every accepted core constructor, using these
finite searches. Its well-founded syntax recursion carries kernel-checked
decreasing proofs; syntax size is not a runtime cutoff. Constructor equations
support kernel reduction of concrete examples. With N stored positions the clock
has N(N+1) states. That bound
comes from the finite-state proof; it is not a configurable prefix cutoff. This
implementation favors a simple checked algorithm, without a performance claim
for large nested formulas. It does not enumerate possible traces.

## Observations, capture and agreement

`FiniteEnvironment` stores the fixed attachment and finite captured sets.
`push` preserves the attachment; temporal steps preserve all captures. Quantifiers
range over distinct identities in a `Finset`, including identities now absent.
All/some/no/one/lone implement the accepted counting equations, and `letSet`
captures the complete set at its evaluation time.

`FiniteObservation` supplies total Boolean atoms and finite domains as functions
of the environment and clock. `Agrees` requires atom equivalence and domain
set equality with an independently supplied `Observation`, for every captured
environment and absolute time. It is a proof obligation, not an assertion that
matching a sampled table establishes source agreement. `FiniteAdapter` packages
that proof with the executable observation functions.

`FiniteAdapter.sets` supplies a concrete proved adapter for the complete accepted
`SetExpr`/`SetAtom` grammar: empty/current-this/root/variables/extents, set operations,
current parent/child/dereference navigation, nonemptiness, equality and inclusion.
It retains D1's distinction between standalone `this` and direct `this` navigation.
A captured head observes a later changed reference target; a captured target set
retains its original identities. Source absence does not prevent reaching a live
fixed parent. Invalid reference tables still fail structural checks.

The generic boundary accommodates later normalized surface reductions and exact
trace comparisons. A structural/primitive adapter must prove its own source
agreement and actual finite-domain/range conditions. The reviewed
[D3 partial-arithmetic interfaces](behavioral-structure.md#mathematical-arithmetic)
are not yet integrated into this checker. A missing adapter is unsupported. This
total-atom contract has no admitted undefined value; it does not collapse
undefinedness into violation or supply partial temporal-atom integration.

The main results are:

- `Core.finite_agrees`: finite evaluation equals `Core.eval` on the infinite
  unfolding, for every formula, finite environment and absolute time, under
  `FiniteObservation.Agrees`. The temporal theorem applies even to raw signals;
  structural validity is checked separately.
- `Core.normalized_finite_agrees`: composition with signed normalization and
  lifetime lowering gives independent `Formula.denote`, for either source sign.
  The existing mathematical normalizer/lowering remain noncomputable definitions;
  the executable API consumes a supplied `Core`.
- `attachedFinite_agrees` and `normalized_attached_agrees`: implicit always over
  every live applicable context, preserving each original attachment through
  quantification. The context inventory is explicitly supplied; a surface adapter
  must relate it to its own applicability rule.

The existing lowering stops obligations at the first parent gap. The agreement
proof therefore preserves cancellation without resumption on reappearance.
It does not replace source negation by classical negation of a checker result.

## Outcomes and limits

`Verification.checkAt` uses the existing checked core certificate and returns:

| Result | Meaning |
| --- | --- |
| `malformed` | Invalid core certificate or static identity inventory |
| `unsupported` | Core outside the admitted structural fragment, or missing certified finite observations |
| `violated` | Structural trace validity or the supplied core formula fails |
| `satisfied` | Both structural validity and the formula hold on this supplied unfolding |

`checkRaw` first rejects empty inputs, invalid loop indices and changed frame
metadata as malformed. `checkAt_correct` proves satisfied iff infinite trace
validity and independent core satisfaction, assuming the checked core/support
conditions and a certified adapter. Raw input and adapter failures stay separate
from that equivalence. An invalid certificate is not evidence that the model
itself is unsatisfiable.

These results concern only the supplied finite inventory and lasso. They do not
prove that every infinite trace is ultimately periodic, that inferred identity
scopes suffice, that a solver enumerated every candidate, or that bounded UNSAT
excludes every infinite trace. There is no new Alloy protocol or compiler theorem.

## Sources and verification

Behavioral paper §5 Definitions 2–5 and §6.2 (pp. 2:25–28, 2:32), amended by
pinned temporal errata T1/T2/T7/T13, supply the source obligations. The
[source ledger](sources.md#behavioral-profile-sources) preserves exact hashes,
licenses and the deliberate D1 departure. The [Alloy 6 reference](https://alloytools.org/alloy6.html)
sections “Instances are traces”, “Time horizon” and “Meaning of temporal
connectives” supply the lasso/ordinary-LTL comparison. The finite-orbit and
history construction is independently authored.

[LassoExamples](../Clafer/Behavioral/LassoExamples.lean) kernel-checks valid
structural cycles, nonzero prefixes, first-entry/self-loop anchors, loop-edge
birth/death, persistent/cancelled obligations, no resumption, retained sets,
changing references and quantifier boundaries. Mutations reject bad loop indices,
parent/type switches and multiple targets for one reference occurrence; distinct
bag heads sharing a target remain valid. All four public outcomes are exercised.
The [exhaustive test](../tests/behavioral_lasso.lean) compares actual evaluation
with an independent arithmetic-index oracle for every one-, two- and three-state
lasso and pair of Boolean signals, including nested future operators and anchors.
These executable comparisons supplement the universal correspondence proofs.
