# Behavioral profile and integration contract

`impl~behavioral-profile-contract~1`

This is the contract accepted through [profile adoption (S1)](https://github.com/kbak/clafer-semantics/issues/123).
The unresolved decisions below still require explicit review before dependent definitions.
The [accepted research direction](https://github.com/kbak/clafer-semantics/issues/112#issuecomment-6673473063)
selects independent source semantics and integration branches; it does not accept
new definitions. This document specifies the complete intended behavioral surface,
its owners and verification obligations.
The [trace foundation](behavioral-traces.md) records the delivered identity,
lifetime and structural bridge APIs and witnesses. The
[formula contract](behavioral-formulas.md) supplies signed evaluation,
normalization/lowering and the adopted D1 environments over total observations;
later feature obligations remain separate. The [structural and atom contract](behavioral-structure.md)
adds richer admission, inherited-reference bindings, captured static agreement and
strict partial temporal composition, with explicit downstream obligations.

Profile identifier: **behavioral-0.5.7-candidate/v1**, source commit
`gsdlab/clafer@af858ec0fe3ce2ceacb7fd120947c058233086d6`.
The [source ledger](sources.md#behavioral-profile-sources) identifies the paper,
hashes, licenses and decision comments. A later release commit requires an
explicit delta review; a version number or moving branch is insufficient.

Covers:
- `req~behavioral-profile~1`
- `req~behavioral-structural-boundary~1`

## Ownership and proposed module boundaries

The existing `clafer` Lake package retains `DPGraph`, `FormalCD` and `Clafer`.
Add behavioral modules under `Clafer/Behavioral`, exposed through an optional
`Clafer.Behavioral` entry point. Preserve existing structural entry points:
`import Clafer` need not import behavioral machinery, and `import DPGraph`
remains independent. The module inventory still builds and audits every owned
module, including modules outside public entrypoint closures.

These are responsibility boundaries. Trace/Snapshot APIs are documented in the
[trace foundation](behavioral-traces.md); formula/environment APIs in the
[formula contract](behavioral-formulas.md). Other names remain proposed.
Implementing tickets must publish actual declaration names and assumptions before
accepted downstream use. Splitting a file within its responsibility is allowed;
moving meaning across a repository or layer requires contract review.

| Owner | Proposed modules / interface | Required boundary |
| --- | --- | --- |
| [Trace and snapshot semantics (S2)][S2] | `Clafer/Behavioral/Trace.lean`, `Snapshot.lean` | Shared identity/type/parent data, live states, lifetimes, structural projection and constant embedding |
| [Signed temporal semantics (S3)][S3] | `Formula.lean`, `Environment.lean`, `Denotation.lean`, `Lifetime.lean`, `Normalization.lean`, `Lowering.lean` | Independent signed source satisfaction, interval meaning, normalization and ordinary temporal core; no compiler IR or target imports |
| [Structural atom compatibility (S4)][S4] | `Structural.lean`, `StructuralCompatibility`, `StructuralObservation`, `StructuralSnapshot`, `StructuralBinding`, `CapturedStatic`, `PrimitiveExpression`, `StaticObservation`, `PartialObservation`, `PartialCompatibility`, `Initializers` | Independent richer admission, full current bindings, captured static agreement and strict partial temporal composition; reviewed initializer profile |
| [Surface meaning (S5)][S5] | `Surface.lean`, `Patterns.lean`, `Properties.lean` | Independent modifier/transition/pattern meaning and reduction proofs; assertions and scenarios |
| [Lasso checking (S6)][S6] | `Lasso.lean`, `Orbit.lean`, `FiniteEvaluation.lean`, `LassoValidation.lean`, `FiniteSets.lean`, `Verification.lean` | [Finite representation, unfolding and exact-candidate evaluation](behavioral-verification.md) over the normalized core |
| [Compiler contract (C1)][C1], [IR (C4)][C4] | Downstream executable behavioral IR and interpretation | Pins an accepted upstream SHA; representation correctness is proved, not an assumed preservation predicate |
| [Target semantics (C3)][C3], [encoding (C5)][C5]/[full encoding (C8)][C8] | Downstream independent Alloy temporal meaning, encoder, serializer | Source meaning must not be defined by the generator or target evaluator |
| [Structural frontend (C6)][C6], [behavioral frontend (C7)][C7] | Downstream parsing, resolution and elaboration | Names become resolved IDs and explicit head/target views; source positions and attachment survive |
| [Exact comparison (C9)][C9], [source CLI qualification (C10)][C10] | Downstream decoding, receipts, CLI and integration | Same trace/identity correspondence, explicit scopes, target capacity and arithmetic assumptions |

Dependencies remain `Clafer -> FormalCD -> DPGraph -> Mathlib`. No generic
temporal DPGraph/FormalCD framework or third package is required. Behavioral
core meaning must not import its executable checker, source frontend, Haskell
exporter or Alloy tooling. Shared static prerequisites remain in their owning
Clafer modules; any extension there must retain existing contracts.

## Infinite meaning and structural agreement

The semantic domain is an infinite sequence indexed by natural-number time,
with a shared carrier of identities, time-independent typing and parent assignment,
and time-dependent live sets and references. A child can be live only with its
parent. Its parent is fixed across **all** its lifetimes, not just adjacent live
states. An identity may disappear and reappear; a different identity is replacement.
The synthetic root exists throughout. Abstract declaration roles and actual parents
of concrete instances remain distinct, including mixed top-level/nested subtypes.

A state is projected onto its **live carrier**, with an embedding into the shared
identity carrier. This is necessary because
[`Configuration.Rooted`](../Clafer/Semantics/Structural.lean) covers every member
of its ambient carrier. Absent pool objects must not be forced into live classes.
Reference heads retain identity; two bag heads with the same parent and target
remain two occurrences. Changing target relations do not rename heads.

The first bridge domain is a resolved `EffectiveCore` satisfying its existing
`WellFormed` and `Supported` predicates, with no additional temporal constraints
or modifiers. State data must satisfy the corresponding typing, root, parent,
reference, inheritance, declaration-disjointness, multiplicity and group clauses.
The [trace bridge](behavioral-traces.md#projection-and-constant-embedding) proves
projection into `StructuralSatisfies`, and conversely embeds a
satisfying structural configuration as a constant trace under the stated stable
identity/type/parent correspondence. Where the current overlapping super extents
need a direct-type witness, that witness and its existence obligation must be
explicit. Neither arbitrary sequences of valid snapshots nor arbitrary temporal
constraints follow from this bridge.

This initial domain excludes richer inherited/reference/primitive cases.
The [S4 contract](behavioral-structure.md) supplies their independent richer model,
current bindings and partial-atom adapters, with exact agreement on the old domain.
Static atom agreement states its captured-environment, live-this and definedness
hypotheses explicitly. The present `Expr.not` remains ordinary static negation; reusing it
for lifetime-bounded source negation would change the profile.

Finite lassos are a separate analysis representation: a nonempty finite state
sequence, valid loop index, fixed identity/type/parent data and well-formed loop
edge. The [finite verification contract](behavioral-verification.md) relates
evaluation to the infinite unfolding, including time zero,
birth/death at the loop edge and repeated lifetimes. A cancelled obligation does
not restart when its parent identity reappears. Internal past operators require
an initial-history argument, not assumed first-loop periodicity. Finite observation
and integer range evidence remain explicit. No finite identity/step bound implies
completeness over all infinite traces; scopes bound identities across the whole
trace, not maximum simultaneous population.

## Parent lifetime and source polarity

For a constraint attached to identity `c`, let `P(t)` mean that **its fixed parent**
is live at time `t`. The root case uses `P = true`. Each live context at each time
starts its constraint obligation. Context disappearance alone does not cancel it;
the parent's first disappearance does. The corrected T2 rule can be stated without
an Alloy representation, using ordinary infinite-trace LTL on the right:

| Source operator after signed normalization | Parent-bounded meaning |
| --- | --- |
| `X a` | `X (¬P ∨ a)` |
| `F a` | `F (¬P ∨ a)` |
| `G a` | `a` at every time before the first `¬P`, forever if none occurs |
| `a U b` | `(P ∧ a) U (¬P ∨ b)` |
| `a W b` | the disjunction of parent-bounded `G a` and parent-bounded `a U b` |

Operands are interpreted recursively in the same attachment environment. Source
negation is normalized **before** these bounds: `!X a` becomes `X !a`, `!F a`
becomes `G !a`, `!G a` becomes `F !a`, and negated U/W exchange U/W with the
standard signed operands. Negated `initially`/`finally` push the sign into the
anchored body. Temporal implication, equivalence, xor and conditionals expand;
`all`, `some`, `no` propagate polarity, while `one` and `lone` retain classical
negation of their interpreted counting result. Temporal-free atoms remain classical
on their defined domain. S3 must state the precise normalization judgment, including
these barriers, and prove agreement with independent source meaning.

Consequently `F error` and its **source** negation can both hold if the parent
ends before an error. Under a persistent parent and defined atoms the corresponding
contradiction must be impossible. Lean's meta-level logic stays classical.
An assertion counterexample is classical failure of the interpreted assertion,
not satisfaction of its source-negated syntax.

## Feature disposition matrix

`P` below means the [behavioral paper][paper], with its printed article pages
`2:n`. `Tn` and `Sn` refer to the pinned [temporal][temporal] and [static][static]
errata. `CS` refers to the pinned [CheatSheet][cheat]. Each row is required in the
final profile unless explicitly marked **review decision**. A fixture pair is a
required future positive witness and negative mutation/countermodel, not a claim
that executable fixtures already exist. S7 must replace each obligation with
actual declarations, proof hypotheses and fixture links. Backend witnesses alone
do not discharge source proofs.

| ID / semantic rule | Source locator | Owner | Proof obligation | Positive / negative fixture |
| --- | --- | --- | --- | --- |
| B01: resolved declarations, containment, abstractness, single inheritance and type consistency | P §5 Def. 1, pp. 2:23–24; Def. 3.1–3 | [S2], [S4], [C6] | Well-formed model and state clauses; effective realization agreement | Nested concrete refinement / wrong-parent or direct abstract instance |
| B02: shared identities, live root, fixed types and fixed parents | P §5 Def. 2, p. 2:25; Def. 5.1,3; T1 | [S2], [C4] | Snapshot projection; same parent at any two live times | Same object under one parent / move it after absence |
| B03: disappear, reappear, replace | P Def. 5.2 replaced by T1; T13 | [S2], [S6], [C9] | Lifetime start/end and trace-wide identity transport | Reuse one identity after a gap / hide replacement by per-state renaming |
| B04: set/bag reference occurrence identity and live, typed targets | P Def. 2; Def. 3.3–4; T11; S4 | [S4], [C6] | Set key only for distinct set heads; preserve bag heads and current target validity | Two bag heads to one target / same pair in a set or absent target |
| B05: effective groups count own and inherited child objects | P Def. 3.5–6 corrected by T11; S1–S5 | [S4], [C6] | Agreement with existing group/default/realization contracts | Inherited xor satisfied by an added child; two bag heads counted twice / count names or distinct targets |
| B06: root/parent, explicit and implicit dereference | P §5 expression equations pp. 2:26–27; S7–S9; CS Identifiers | [S4], [C6] | Explicit head/target views; actual parent for abstract instances | Top-level parent is root; explicit dref chooses target child / double dereference or missing root |
| B07: `this`, variables, `let`, navigation across time | P §5 pp. 2:26–28, Def. 4; CS Temporal logic | [S3], [S4], [C4] | Environment admissibility and static atom agreement; resolve D1 below | Freeze a chosen identity / accidentally rebind it to its replacement |
| B08: true, Boolean connectives, set inclusion/equality/union/intersection/difference, joins, quantifiers and conditionals | P Def. 4 and §6.1 p. 2:30; CS Expressions | [S3], [S4], [C6] | Static atom agreement, typed navigation and explicit definedness; temporal signs compose | Equal targets with distinct heads / conflate those views or erase binder identity |
| B09: `X` / `next` | P Def. 4, §6.1; T2 | [S3], [C5] | One-step equation including parent cancellation | Parent survives and next body holds / next body false under surviving parent |
| B10: `F` / `eventually` | P §6.1 p. 2:31; T2 | [S3], [S6], [C5] | Eventual body or parent end | Event after several states, or parent end / persistent parent and no event |
| B11: `G` / `globally` | P §6.1 p. 2:31; T2 | [S3], [S6], [C5] | All states of the remaining parent lifetime | Body until parent end / false body before that end |
| B12: `U` / `until` | P Def. 4, p. 2:28; T2 | [S3], [S6], [C5] | Strong until or cancellation, including immediate right operand | Left holds until right / left breaks early with parent live |
| B13: `W` / `weakuntil` | P §6.1 p. 2:31; T2 | [S3], [S6], [C5] | Weak-until equation and signed duality | Left forever without right / neither left nor right before cancellation |
| B14: source `!`, temporal Boolean expansions, quantifier polarity | P Def. 4 deliberately changed by T2; decision #110 | [S3], [C4], [C8] | Signed normalization, all/some/no duality and one/lone barrier | Both polarities cancelled / incorrectly allow both with persistent parent |
| B15: implicit always and per-instance attachment | P §6.1 p. 2:30; T2, T9 | [S3], [S5], [C7] | Constraints start at every applicable state/context | Recurring `sometime` / only one occurrence on a permanent root trace |
| B16: `initial` including inheritance | P §6.1 p. 2:32; T7–T8 | [S5], [C7] | Child presence at every parent birth, including time zero | Present at two births / absent only at reappearance |
| B17: `final` including inheritance | P §6.1 p. 2:32; T8 | [S5], [C7], [C8] | Shallow stability of heads and references per parent lifetime | Stable parent interval with changing grandchildren / replace a final child within that interval |
| B18: `finalref`, `finaltarget`, direct/inherited references and combined modifiers | T8; CS Temporal modifiers; decision #109 | [S4], [S5], [C6] | Distinguish reference stability from target-set stability; inherited modifier agreement | Inherited fixed reference / change its target while the relevant lifetime continues |
| B19: dynamic enum literals are final | T8; CS Enum | [S5], [C7] | Enum expansion without turning static models dynamic | Same literal identity through a trace / replace a literal |
| B20: `initially` | P §6.1 p. 2:31 corrected by T7 | [S3], [S5], [S6], [C7] | At time zero and each context birth; negative polarity anchors body | Body at first and second births / satisfy only the first |
| B21: `finally` | P §6.1 p. 2:31; T7; T2 polarity | [S3], [S5], [S6], [C7] | Last live state, every lifetime; vacuous for no death | Body before death / body only after death |
| B22: immediate `-->` and guarded `-[g]->` | P §6.1 pp. 2:31–32; T2–T3 | [S5], [C7], [C8] | Source (and guard) implies bounded next target | Guard fires to target / surviving parent but wrong next state |
| B23: eventual `-->>` and guarded `-[g]->>` | P §6.1 pp. 2:31–32; T2–T3 | [S5], [C7], [C8] | Source/context persist until target or parent cancellation; guard tests entry | Guard need not persist / source dies before target with parent live |
| B24: declaration transition and additional outgoing constraints | T3; CS Transitions; decision #107 | [S5], [C7] | Attach to the source clafer, not its parent | Nested source switch / accidentally cancel on source death or wait for grandparent death |
| B25: mixed guarded transition chains | P §6.1 amended by T4 | [S5], [C7], [C8] | First condition, then required sequential states/guards | `a,b,c` / `a,not b,c` satisfying a nested-implication misreading |
| B26: six patterns in all five scopes | P §§4.2, 6.1; T2, T9; CS Dwyer's patterns | [S5], [C7], [C8] | Every cell in the pattern matrix below; resolve D2 | Required scope fixtures / missing event or boundary mutation |
| B27: universal top-level/nested assertions | P §§4.5, 6.1 corrected by T5–T6 | [S5], [C8], [C10] | All model traces and all applicable instances; classical counterexample | Property on all traces / one counterexample despite another good trace |
| B28: possible and negative scenarios | P §4.5 corrected by T4–T6; T12 | [S5], [C7], [C10] | Existential model-plus-scenario feasibility; required start anchor | Anchored reachable sequence / impossible sequence or vacuous first condition |
| B29: syntax/precedence and aliases | P §6.1; T12; CS Temporal logic/Transitions | [C7] with [S5] normalization | Parser/elaboration agreement; transitions bind weakest; `not` quantifier differs from `!` | `initially (a --> b)` / parse it as `(initially a) --> b`; following `xor` ambiguity |
| B30: lassos and bounded reporting | P §6.2; T13 | [S6], [C2], [C3], [C9] | Infinite unfolding/evaluation agreement; identity capacity assumptions | Nonzero prefix and loop-edge birth / invalid loop index or undersized identity pool |
| B31: integer observations and operations | P §6.1 structural reuse; S11; current denotation; reviewed D3 conversion | [S4], [C6], [C8] | Explicit strict-singleton versus finite-set-sum conversion and arithmetic-domain/range conditions; complete D3 | Empty arithmetic operand contributes zero while presence stays false; defined arithmetic in range / wrong-domain or infinite observation, zero divisor; backend range overflow |
| B32: declaration `=` / `:=`, numeric/group defaults | P §6.1 p. 2:29; T10; S1–S2 | [S4], [S5], [C6], [C7] | Constant equation at every live attachment state; explicit rejection of `:=`; effective defaults remain separate from temporal birth | Inherited opt and persistent `=` / accept `:=` silently or confuse `=` with `initially` |

The current static prerequisite rules are described by
[group compilation](group-compilation.md), [inherited realization](inherited-realization.md),
[constraint denotation](constraint-denotation.md) and [integer extraction](integer-extraction.md).
They are evidence for reuse only on their stated domains. In particular, unreachable
group lower bounds retain the source meaning of an empty context; the compiler's
rejection is a separate frontend check (S5). Existing bounded structural importer
and oracle contracts are not upgraded to temporal or 0.5.7 contracts by this document.

## Complete pattern and scope inventory

All **30** cells below are required. IDs identify future fixture pairs and expansion
proofs owned by [S5], frontend preservation by [C7], and encoding by [C8]. The
source locator for each row is the matching `TmpPat*` branch of pinned
[`translateTmpPatterns`][desugarer], with each column selecting `PatScopeEmpty`,
`PatScopeBefore`, `PatScopeAfter`, `PatScopeBetweenAnd`, or `PatScopeAfterUntil`.
The paper supplies the pattern approach, not a complete expansion catalogue.
The compiler is supplementary: D2 requires independent interval meanings and
review of any mismatch before adopting its equations.

| Pattern / local positive and negative witness | Whole suffix | Before r | After q | Between q and r | After q until r |
| --- | --- | --- | --- | --- | --- |
| `never p`: no p / insert p | N0 | N1 | N2 | N3 | N4 |
| `sometime p`: p occurs / omit p in a completed required interval | E0 | E1 | E2 | E3 | E4 |
| `lonce p`: one contiguous p episode / two separated episodes | L0 | L1 | L2 | L3 | L4 |
| `always p`: p throughout / insert a non-p state | A0 | A1 | A2 | A3 | A4 |
| `s must precede p`: s no later than first p / p strictly before any s | P0 | P1 | P2 | P3 | P4 |
| `s must follow p`: each required p gets s / leave a p unanswered | R0 | R1 | R2 | R3 | R4 |

For each cell apply its row's positive/negative pair in its column's active
interval. Whole suffix starts now; before excludes the closing r; after includes
its triggering q; between and after-until start at q when not already r and end
before r. Distinguish a scope that requires a closing r from an unfinished scope.
Repeat q/r, simultaneous q/r, a missing q, a missing r, an event exactly at either
boundary, context death, parent death and reappearance are mandatory boundary
fixtures. Evaluate both polarities, including temporal scope premises. T2's
normalization means a negated `F r` premise cannot be naively replaced by a
positive bounded eventuality that becomes true solely on cancellation.

These witness recipes are acceptance obligations. They do not declare every
pinned expansion correct. In particular, the pinned `TmpPatFollow` / between
branch must be checked for responses to p **after** the opening q (D2).
Implicit always still applies to a pattern's attachment: unanchored top-level
`sometime p` requires recurrence; `initially (sometime p)` requires one future
occurrence. `lonce` counts episodes, not individual adjacent p states.

## Errata coverage and deliberate departures

| Item | Disposition / matrix rows | Required departure from the printed paper or boundary |
| --- | --- | --- |
| T1 | B02–B03, B30; adopt | Remove no-reappearance; fix parent across all lifetimes; separate population from identity bounds |
| T2 | B07, B09–B15, B20–B28; adopt documented signed rule | Parent-bound obligations, including negated ones; do not reuse classical static `.not` |
| T3 | B22–B24; adopt extension | Declaration transition belongs to the source context; additional transitions in the same state share that attachment |
| T4 | B25, B28; adopt change | Chains require their intermediate states, with only the first source conditional |
| T5 | B27–B28; adopt correction | Universal assertions and existential scenarios are distinct |
| T6 | B27–B29; adopt correction | Negative scenarios require the intended conjunction/next condition, not a vacuous implication |
| T7 | B16, B20–B21; adopt correction | Time-zero birth and every reappearance; finally at each actual last live state |
| T8 | B17–B19; adopt with reference-view review | Finality is shallow and lifetime-scoped; inherit modifiers and references; enum literals final dynamically |
| T9 | B15, B26; adopt clarification | Implicit always applies to patterns too; recurrence differs from one anchored occurrence |
| T10 | B05, B32; reuse adopted static policy | `opt` children optional; numeric defaults retain the separately adopted S1 language evolution |
| T11 | B01, B04–B06; adopt corrections/change | Distinct heads and set-only injectivity; effective group over own/inherited children; restore missing bound variable; discard obsolete Def. 5.2 |
| T12 | B28–B29; frontend obligation | Explicit precedence, transition/declaration ambiguity and quantifier `not` |
| T13 | B03, B30; analysis boundary | Native Alloy lasso bounds do not characterize all infinite traces or guarantee inferred scopes suffice |

Paper §§5–6 are covered by B01–B32: Definitions 1–3 by B01–B06, expression and
constraint meaning/Definition 4 by B07–B14, Definition 5 by B02–B03/B15,
§6.1 by B05–B29/B31–B32, and §6.2 by B30. Sections 8–9 motivate scope and
alternatives; they do not add a timed, probabilistic, branching-time or concurrency
scheduler semantics. The historical Alloy 4.2 encoding is context, not the target
semantics for the new Alloy 6.2.0 backend.

## Decisions requiring contract review

The [public contract questions](https://github.com/kbak/clafer-semantics/issues/123#issuecomment-6673807549)
record the concrete source conflicts below. No unresolved row authorizes a dependent
interpretation. Record its disposition
publicly on [profile adoption][S1] and the owning ticket before adding a definition;
update this contract and any affected dependency/readiness record. Contract
acceptance must explicitly settle these points or explicitly approve a bounded
interface with the remaining obligation owned and blocked. Required behavioral
features cannot disappear through an unsupported-input guard.

| Decision | Evidence / conflict | Required resolution and owners |
| --- | --- | --- |
| D1: observations of stored identities — adopted | P §5 pp. 2:26–28 attaches snapshots to environment values; pinned `AlloyLtl.genPExp'` emits bound variables as stable identities and current-state navigation. `thisAlive` filters standalone `this`, whereas direct `this` navigation starts at the identity even after its disappearance. | [Approved disposition](https://github.com/kbak/clafer-semantics/issues/123#issuecomment-6684849831): capture identities/sets and use current relations, retaining standalone-this versus direct-navigation distinction. The [formula contract](behavioral-formulas.md#captured-values-and-current-navigation) and its witnesses give exact rules. [S4]/[C4] must preserve them in adapters; no full agreement with the paper's snapshot-pair evaluator is claimed. |
| D2: independent scoped patterns | The paper lacks all 30 equations; pinned `TmpPatFollow` between q/r puts the p implication at the opener, unlike the after-until branch. | [S5]/[C7]/[C8]: evaluate a trace with q at 0, p later, r later still, and no response; record whether to correct the expansion or select that candidate behavior. Preserve the complete pattern scope while resolving the mismatch. |
| D3: arithmetic and partial temporal domain — adopted | The [accepted behavioral conversion](https://github.com/kbak/clafer-semantics/issues/126#issuecomment-6685233729) sums finite integer sets, including empty-to-zero, while preserving relational presence/equality and strict extraction. The [accepted scalar rule](https://github.com/kbak/clafer-semantics/issues/126#issuecomment-6685442865) uses mathematical Int, truncation toward zero, matching remainder and undefined division/remainder at zero. The [extrema disposition](https://github.com/kbak/clafer-semantics/issues/126#issuecomment-6685652746) keeps empty selectors empty; explicit folds retain occurrences, with empty sum 0/product 1. Backend overflow does not change source meaning. The [strict temporal-domain disposition](https://github.com/kbak/clafer-semantics/issues/126#issuecomment-6687520296) requires every operand/member and every active temporal observation defined. | [S4] supplies the [resolved expression and partial-domain interfaces](behavioral-structure.md#captured-static-atoms-and-partial-temporal-composition), finite-observation and agreement proofs. [C6]/[C8] preserve those rules during elaboration/encoding and establish sufficient intermediate ranges. Undefined expressions and wrong-domain/infinite observations must not silently become zero, false or true. |
| D4: defaults and structural prerequisites — adopted | The [reviewed disposition](https://github.com/kbak/clafer-semantics/issues/126#issuecomment-6687520296) supports `=` as a presence-guarded equation at every live attachment state and explicitly rejects `:=` in this profile. S6 nested abstracts/refined parents and S9 inherited references use the richer independent structural core. S10 concrete supers remain source-permitted. | [S4] supplies admission, common-fragment equivalence, full bindings and initializer disposition. [C6]/[C7] preserve effective defaults and instance identities, resolve views and diagnose unsupported `:=`; [S5] owns remaining surface modifiers. Neither initializer denotes temporal birth. |

The following broader nonbehavioral features are **proposed exclusions requiring
S1/C1 review**, not silent omissions: decimal/double/real and string computation,
optimization goals, backend escapes, alternative solvers, inferred-scope correctness,
and production parser/tooling in this repository. Inheritance from concrete types
is unimplemented by the pinned compiler (S10); unrestricted name resolution order
remains the separate [resolution decision](https://github.com/kbak/clafer-semantics/issues/121).
Resolved inputs and explicit paths permit independent semantics work without
settling that frontend dispute. No listed exclusion covers an integer/reference/
structural prerequisite necessary for the required behavioral rows. Source `let`
and the paper's static initializer syntax remain accounted for by B07/B32 and D1/D4.

## Integration and acceptance

Feature branches use `codex/behavioral-...` and PRs target `behavioral`, with
`Closes #N`. Selection and accepted hard dependencies precede implementation.
Follow [Todo → Ready → In Progress → Done](../CONTRIBUTING.md#ticket-readiness).
Parent/child roadmap links group work; they are not hard dependencies.

A feature handoff includes an accepted immutable commit, actual APIs/theorems,
all assumptions, positive/negative fixtures, source locators, retained validation
and independent semantic review. Downstream pins that SHA, never `behavioral`
or an unaccepted PR head. New gaps go to public issues before choosing a meaning.
For non-default-branch PRs, explicitly close the issue and mark Done **after** the
accepted merge; `Closes` alone may not close it. A maintainer's merge
communicates approval and acceptance under the [acceptance policy](maintenance.md#maintainer-acceptance);
do not wait for a second confirmation or a separate review submission. Refresh
affected unstarted statuses in both repositories manually.

PR and push CI on `behavioral` run full validation, even for a contract-only diff:
module discovery, build, all tests, independent imports, axiom/layer audits, kernel
replay and IntentBond trace/source checks. Main retains its existing validation
selection policy. Hosted CI and branch protection are separate controls; follow
[maintenance policy](maintenance.md#behavioral-integration-controls), inspect actual
settings, and retain the readback outside source. Exit 4 is automation success
with review pending, not permission to accept a semantic choice.

The final gates are ordered to avoid a cross-repository cycle:

1. [Semantic qualification (S7)][S7] accepts all required rows, structural bridges,
   surface/core composition, lasso obligations and exact source-profile disposition.
2. [Compiler qualification (C10)][C10] accepts the complete frontend, target/encoding
   proofs, CLI and exact comparisons against S7's immutable upstream commit.
3. [Semantics main integration (S8)][S8] requires S7 **and C10**, reconciles any main
   changes, revalidates, and obtains authorization for the concrete integration PR.
4. [Compiler main integration (C11)][C11] pins the actual merged semantics main SHA,
   repeats full qualification and obtains its own merge authorization.

Keep static tests, the historical SoSyM checkpoint, structural comparison receipts
and oracle pins reproducible throughout. A first successful slice is progress,
not completion. Tags, releases and final main merges require their own concrete
review/authorization; this contract change supplies none of them.

[paper]: https://arxiv.org/abs/1807.08576v1
[temporal]: https://github.com/gsdlab/clafer/blob/af858ec0fe3ce2ceacb7fd120947c058233086d6/doc/temporal-semantics-errata.md
[static]: https://github.com/gsdlab/clafer/blob/af858ec0fe3ce2ceacb7fd120947c058233086d6/doc/static-semantics-errata.md
[cheat]: https://github.com/gsdlab/clafer/blob/af858ec0fe3ce2ceacb7fd120947c058233086d6/doc/CheatSheet.md
[desugarer]: https://github.com/gsdlab/clafer/blob/af858ec0fe3ce2ceacb7fd120947c058233086d6/src/Language/Clafer/Intermediate/Desugarer.hs
[S1]: https://github.com/kbak/clafer-semantics/issues/123
[S2]: https://github.com/kbak/clafer-semantics/issues/124
[S3]: https://github.com/kbak/clafer-semantics/issues/125
[S4]: https://github.com/kbak/clafer-semantics/issues/126
[S5]: https://github.com/kbak/clafer-semantics/issues/127
[S6]: https://github.com/kbak/clafer-semantics/issues/128
[S7]: https://github.com/kbak/clafer-semantics/issues/129
[S8]: https://github.com/kbak/clafer-semantics/issues/130
[C1]: https://github.com/kbak/clafer-compiler-lean/issues/70
[C2]: https://github.com/kbak/clafer-compiler-lean/issues/71
[C3]: https://github.com/kbak/clafer-compiler-lean/issues/72
[C4]: https://github.com/kbak/clafer-compiler-lean/issues/73
[C5]: https://github.com/kbak/clafer-compiler-lean/issues/74
[C6]: https://github.com/kbak/clafer-compiler-lean/issues/75
[C7]: https://github.com/kbak/clafer-compiler-lean/issues/76
[C8]: https://github.com/kbak/clafer-compiler-lean/issues/77
[C9]: https://github.com/kbak/clafer-compiler-lean/issues/78
[C10]: https://github.com/kbak/clafer-compiler-lean/issues/79
[C11]: https://github.com/kbak/clafer-compiler-lean/issues/80
