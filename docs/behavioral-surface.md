# Behavioral surface meaning

`impl~behavioral-surface-contract~1`

The [profile](behavioral-profile.md) exposes resolved modifiers, transitions,
patterns, constraints, assertions and scenarios through `Clafer.Behavioral`.
This is independent source meaning. There is no production parser here and no
assumption that the Haskell compiler preserves it. The [source ledger](sources.md#behavioral-surface-correspondence)
records immutable source locators. The sections below link the definitions,
proofs and distinguishing fixtures for each construct. Source modules do not import the finite checker;
fixture modules may use its proved correspondence to infinite traces.

Covers:
- `req~behavioral-modifiers~1`
- `req~behavioral-transition-sugar~1`
- `req~behavioral-patterns~1`
- `req~behavioral-properties~1`

## Reviewed source choices

The [review summary in #127](https://github.com/kbak/clafer-semantics/issues/127)
collects these decisions for Clafer developers. The compiler comparison is pinned
at `gsdlab/clafer@af858ec0fe3ce2ceacb7fd120947c058233086d6`.

| Choice | Adopted source meaning | Distinguishing trace / provenance |
| --- | --- | --- |
| Response between q and r | Every p in a completed interval needs s before its first closing r. | Reject q@0, p@1, r@3, no s. The pinned expansion tests p only at the opening q. |
| Precedence after q | Start at the first q; a later q cannot erase an earlier violation. | Reject q@0, p@1, q@2, s@3. The pinned expansion can choose q@2. |
| Reference modifiers | `finalref` fixes each live head's reference; `finaltarget` fixes its parent's target image; `final` fixes heads and references. | Two heads swapping targets preserve `finaltarget` and violate `finalref`. The pinned compiler uses per-head equality for both. |

The [response/modifier decision](https://github.com/kbak/clafer-semantics/issues/127#issuecomment-6689325093)
and [first-opener decision](https://github.com/kbak/clafer-semantics/issues/127#issuecomment-6689399331)
authorize these interpretations. The behavioral paper §§6.1–6.2, p.2:32 defines
`final` child-set stability and nested lifetime limits; it does **not** define
`finalref` or `finaltarget`. Their precise distinction is an explicit completion
of T8/CheatSheet's separate modifiers, not a recovered paper equation. These
choices do not certify compatibility with the pinned compiler. The
[revision comparison](sources.md#pr113-modifier-and-pattern-revisions) identifies
these discrepancies at the historical pin and their corrections in `b2875f3`;
`8a12ae7` separately retains all reference modifiers. These source inspections
neither replace the pin nor supply a new Haskell execution receipt.

## Modifiers and anchors

[Modifiers.lean](../Clafer/Behavioral/Modifiers.lean) uses the richer
`Structural.Core` and `Structural.current` inherited-reference observations.
Heads, head/target pairs and the target image remain separate. For declaration d:

| Modifier | Direct meaning | Lifetime that limits equality |
| --- | --- | --- |
| `initial` | At every birth of an instance of d's parent declaration, at least one d child exists. | Every parent birth, including time zero and reappearance |
| `finalref` | Each head's complete current dereference set is constant. | That head's uninterrupted life |
| `finaltarget` | The parent's image of d heads under current dereference is constant. | That parent's uninterrupted life |
| `final` | Both `FinalHeads` and `FinalRef`. | Parent life for heads; head life for references |

`Stable` quantifies over any two times in one uninterrupted life.
`stable_iff_adjacent` proves that adjacent equality suffices; no comparison crosses
a gap. `final_implies_finalTarget` derives target stability from full finality.
Finality is shallow: descendants are not recursively frozen. In a continuous
parent life, final heads cannot disappear, so final references stay fixed there.
Reference-free declarations have empty reference views. An inherited modifier
accumulates along the super chain (`Effective`); refinements can add modifiers,
not remove inherited ones. `Holds` combines every effective modifier. Effective `finalref`
and `finaltarget` impose both obligations. Their conjunction allows a departing
head to be replaced by a new head at an existing target; `final` rejects that
change of head identity. The image in `finaltarget` is a **set**, not a multiset
of reference occurrences. Three bag heads may change {A,A,B} to {A,B,B} while
the image stays {A,B}; losing A or adding C during one parent life changes it.
The structural head and group counts continue to count all three occurrences.
`enumLiteral true` adds finality to each dynamic enum literal; the static case
adds no temporal modifier. Parsing and enum declaration construction remain
frontend responsibilities.

[ModifierBoundaryExamples](../Clafer/Behavioral/ModifierBoundaryExamples.lean)
uses a model with exactly three heads per live parent for direct and inherited
references. Its
`replacement_both` / `replacement_not_final`, `swap_target_only` and
`loses_target_only` / `adds_target_only` separate the three obligations; combined effective annotations
are checked through `Holds`. The bag fixture preserves all head identities and
counts. A head can change its target after its own gap while its parent and
target image persist; a parent gap permits a new target image. Every fixture has
full structural admission, including its repeating last state. Existing
`ModifierExamples` swap, inherited-owner, shallow-finality and birth witnesses
remain in place.

`expand` produces resolved placement/formula pairs. Initial attaches to parent
instances. Head/target equality attaches to live identities and has empty views
outside the applicable parent fibers; per-head reference equality attaches to d
instances. Equality captures the current set with `let`, then compares at the
next state if the attachment itself survives. This explicit survival test is
necessary because ordinary temporal X is bounded by the attachment's **parent**.
`expand_agrees` and `lower_agrees` require `Structural.Valid`; they use total set
observations and inherited-owner lookup, without an arithmetic-definedness premise.

[Anchors.lean](../Clafer/Behavioral/Anchors.lean) characterizes `initially` as
satisfaction at every context birth and `finally` at every last live state.
These anchors concern the context's own life. A permanent life has no final
state: `finally` is vacuous, even if its unused body has undefined observations.
The inherited [partial-domain contract](behavioral-structure.md#captured-static-atoms-and-partial-temporal-composition)
applies whenever an anchored body is required.

## Transitions and attachment

[Transitions.lean](../Clafer/Behavioral/Transitions.lean) gives a resolved `Chain`
with immediate/eventual arrows and optional entry guards. Let c be the retained
attachment's presence test, a the source and b the required suffix:

| Link | Expansion |
| --- | --- |
| `a --> b` | `a => X b` |
| `a -[g]-> b` | `(a && g) => X b` |
| `a -->> b` | `a => ((c && a) U b)` |
| `a -[g]->> b` | `(a && g) => ((c && a) U b)` |

Only the first link is conditional. `sequence` requires each later source and
guard as well as its step, so `a --> b --> c` means `a => X (b && X c)`.
The eventual persistence condition excludes the entry guard. Disappearing source
or context can violate it while the parent remains alive; only parent loss
cancels the obligation. Reappearance creates new attached obligations.

`declaration` supplies `this` as source and context for a declaration arrow.
The frontend must attach this expansion to that declaration's instances, retaining
each actual parent, and conjoin additional outgoing constraints. The generic
`Chain.expand context` interface requires its caller to supply the correct presence
formula; it does not resolve names or silently change the attachment identity.
`entry`, `advance`, `required` and `meaning` interpret the sequence directly.
Their agreement proofs cover both source polarities and arbitrary temporal guards.
The [qualification composition](behavioral-qualification.md) connects these
expansions and every pattern/scope case to finite checking with the original
strict partial domain, exact context selectors and complete model inventories.

Every constraint is checked at every live applicable attachment/time, through
`Constraint.Holds` / `Formula.PartialAttached`. At a persistent root, unanchored
`sometime p` thus requires recurrence (`∀ t, ∃ j ≥ t, p j`), whereas
`initially (sometime p)` requires only one occurrence from time zero.
`Anchors.root_recurrence` and `root_anchored_existence` state the exact total-atom
hypotheses; recurrence is not replaced by a single existential witness.

## Patterns and scopes

[Patterns.lean](../Clafer/Behavioral/Patterns.lean) covers all six rows and five
columns of the [profile matrix](behavioral-profile.md#complete-pattern-and-scope-inventory).
`Judgment` supplies positive and negative operand signals. `Interval` quantifies
directly over natural-number intervals, including parent loss; `meaning` combines
those judgments without calling the formula expander, normalizer or evaluator.
`expand` separately builds formula syntax. `expand_agrees` proves all 30 cases,
both signs, all times, environments and temporal operands. `lower_agrees`
composes signed normalization and lifetime lowering. The independent event-level
`response_interval` and `first_opener` theorems characterize the two corrected
clauses under a persistent parent, classical events and an identified first boundary.

Whole suffix starts now. Before excludes the first r; after includes the first q.
Between and after-until include q and exclude the next r; simultaneous q/r opens
no nonempty interval. Missing q is vacuous. Between requires a closing boundary
for an existence obligation; after-until can require existence even when r never
arrives. Repeated openers may impose overlapping obligations before the same close.
`lonce` permits at most one contiguous episode, including no episode; adjacent p
states do not count separately. Precedence and response allow simultaneous s/p.
The full signed interval table, rather than a Boolean scope shortcut, specifies
behavior when temporal operands or parent cancellation are involved. In particular,
the negative judgment of F r is G !r, not classical failure of bounded F r.

`PatternExamples` fixes row order N,E,L,A,P,R and column order suffix,before,after,
between,after-until. Its admitted four-state infinite lasso opens q at 0 and closes
r at 3. `all_thirty_positive`, `all_thirty_negative` and
`all_thirty_opposite_signs` check every cell; `source_agrees` connects the computed
finite result to infinite source meaning. Positive/negative row valuations are:

| Row | Satisfying valuation | Violating mutation |
| --- | --- | --- |
| N | no p | p@1 |
| E | p@1 | no p |
| L | p@1,2 | p@0,2 |
| A | p throughout | p only at 1 |
| P | p@1, s@0 | p@1, s@2 |
| R | p@1, s@2 | p@1, no s |

Additional named fixtures cover first/repeated q and r, no opener/closer,
unfinished scopes, simultaneous boundaries, events at opening/closing, context
loss, parent cancellation and reappearance. The two pinned-expansion mutants
are retained as kernel-checked regressions, not as an external compiler run.
`root_attachment_not_initially` checks the assertion attachment API on q@0,2,
s@0 and p@3 (persisting thereafter). The first scope has its precedent at 0;
the later opener has no subsequent s. Initially accepts the first evaluation,
whereas implicit always rejects the later obligation. The distinction preserves
each evaluation's first opener rather than collapsing all openers into a single
global scope.

## Models, assertions and scenarios

[Properties.lean](../Clafer/Behavioral/Properties.lean) defines `Model.behavioral`
from structural well-formedness, valid infinite traces, effective modifiers,
partial observations and attached constraints. `Model.Satisfies` requires all
model constraints. `Asserts` quantifies over **every** satisfying trace and all
selected instances. `Counterexample` is a satisfying trace with meta-level
classical failure of the interpreted assertion, including its definedness.
`counterexample_iff` proves the universal/existential duality. Source `!` does
not implement this failure after lifetime cancellation.

`Possible` asks for one model trace satisfying every added scenario constraint;
`withScenario` conjoins model and scenario constraints. `possible_iff` proves
the correspondence. `Constraint.root` and `nested` expose explicit attachment;
`nested_holds` covers every applicable instance, not one chosen instance.
A scenario requiring a starting state uses the required sequence and explicit
anchor: a conditional first transition can be vacuous. Likewise a negative
scenario intended to exclude `a && X b` must not be rewritten as `!(a => X b)`.
The API represents these distinct formulas without inventing a parser rule.

## Downstream interface and limits

The executable syntax expansions are `Modifiers.expand`, `Chain.expand` /
`sequence` / `declaration`, and `Patterns.expand`. Their direct meanings and
reduction proofs are the upstream interface for downstream elaboration. The
existing `Formula.normalize` and `lower` are Lean `noncomputable` definitions
with proved agreement; this change does not claim a production executable
normalizer. Downstream code generation must implement its own checked
representation or discharge agreement with this interface.

For partial observations, use `Chain.partial_agrees`, `Patterns.partial_agrees`
and `Constraint.lowered`: retain the original expanded formula's `Defined`
predicate **alongside** the normalized core. Strict undefinedness cannot be
removed by a vacuous source/guard or a Boolean simplification. S4 owns the
atom/domain adapter; downstream parsing, resolution, enum expansion and backend
preservation remain separate proof obligations. Finite witnesses establish
specific infinite lassos, not completeness of bounded search.
