# Behavioral formulas, source signs and environments

The optional `Clafer.Behavioral` entry point supplies independent source formulas,
signed evaluation, normalization and lowering to ordinary infinite-time temporal
logic. The [trace foundation](behavioral-traces.md) supplies identities, presence,
structural validity and lifetime boundaries. This contract implements the signed
temporal part of the [behavioral profile](behavioral-profile.md), with the
[approved identity-observation decision](https://github.com/kbak/clafer-semantics/issues/125#issuecomment-6684850305).
Structural atom integration, surface reductions and lasso evaluation retain their
separate owners. No compiler, finite checker or Alloy outcome defines truth here.
The recursive denotations and syntax translations are noncomputable mathematical
definitions, reducible and checked by Lean's kernel. Executable lasso evaluation
and its agreement proof remain with [S6](https://github.com/kbak/clafer-semantics/issues/128).

## Formula and observation domain

[`Formula`](../Clafer/Behavioral/Formula.lean) is indexed by lexical depth. Atoms
and set-valued binder domains are independently supplied families at that depth;
`Observation` interprets each over an environment and natural-number time.
Constructors include truth, atoms, source negation, conjunction, disjunction,
implication, equivalence, xor, Boolean conditionals, X/F/G/U/W, initial/final
anchors, all/some/no/one/lone, and set capture (`letSet`). The representation uses
resolved positions, not names or a parser. Multiple binders can be nested; a
frontend must retain source disjointness restrictions in its resolved domains.

The observation interface is **total**: atom values are propositions, and domains
are sets. The supplied `Observation.sets` implements independently defined total
set observations (nonemptiness, equality and inclusion) over `SetExpr`.
It has no finite-identity assumption and counts quantifier witnesses by identity.
`one` means a unique satisfying identity; `lone` means at most one. Infinite
domains are meaningful for both, without a finite-cardinality operation.

This total interface does not identify undefined values with false. The separate
[partial-atom contract](behavioral-structure.md#captured-static-atoms-and-partial-temporal-composition)
provides `StaticObservation` and primitive-expression adapters with explicit
captured-environment and definedness obligations. `Formula.Defined` requires all
operands/members and every active temporal observation defined; `Satisfies`
combines that domain with the signed denotation below. Completion independence
and exact total compatibility justify reuse. The current static `Expr.not` and
its partial denotation remain unchanged.

## Captured values and current navigation

[`Environment`](../Clafer/Behavioral/Environment.lean) retains an attachment
identity `this` and a `Fin n`-indexed map to captured sets. There is no lookup
for an unbound index. `push` retains `this`, binds the new value at zero and
shifts previous variables. A quantifier captures one identity as a singleton;
`letSet` captures the complete domain value at evaluation time. A temporal step
retains those values. It does not re-evaluate their defining paths, discard absent
captured identities, or replace them with a newer instance of the same class.

Navigation evaluates relations at the **current** time. The concrete set grammar
distinguishes these operations:

| Expression | Meaning at time t |
| --- | --- |
| standalone `this` | The context singleton intersected with current presence |
| bound variable | Its stored set, including identities now absent |
| `root` | The fixed synthetic-root singleton; legal traces keep it live |
| declaration extent | Current live objects whose direct types refine the declaration |
| parent step | The fixed actual parent, filtered by the parent's current presence; source presence is unnecessary |
| child step | Current declared containment, including live endpoints and inherited head views |
| dereference step | Current reference relation with live source and target endpoints |
| direct `this` navigation (`thisStep`) | Start at the fixed context identity, then apply the current step |

Further steps use ordinary relational image. Union, intersection, difference
and empty sets are ordinary set operations. A direct `this.parent` can reach a
surviving parent after the context disappears, whereas navigating from the
observed standalone `this` starts from the empty set. This distinction is explicit
in resolved syntax; it is not a theorem equating those expressions while absent.
Invalid raw dereferences still fail trace validity; filtering an observation does
not repair a malformed trace.

These are the adopted D1 semantics, a deliberate departure from the paper's
snapshot-tagged evaluator on pp. 2:26–28. `captured_set` and `captured_deref`
state capture and current-reference equations. The changing-reference witness
captures head 3 and observes target 6 at time 3, then target 5 at time 4 without
a new head lifetime. Capturing target set `{6}` instead retains `{6}`. No general
equivalence to the paper's historical snapshot-pair evaluator is claimed.

## Attachment and cancellation

[`Trace.ParentPresent`](../Clafer/Behavioral/Environment.lean) looks up the fixed
actual parent of the **original attachment identity**, even when that identity
is absent. For the synthetic-root context it is always true. Top-level objects
have the synthetic root as their actual parent under the trace validity contract,
so their obligations also persist. A binder changes only variable lookup; it
does not attach the body to the quantified object. `context_parent_present`
derives parent presence when a context is live in a valid trace.

[`Formula.Attached`](../Clafer/Behavioral/Denotation.lean) requires the positive
body at every time for every live applicable context. Each such evaluation starts
an obligation. Loss of that context does not cancel its pending future; loss of
its parent does. Moving a constraint from a source state to its parent therefore
changes which lifetime bounds it, as required by T3. This defines attachment, not
the frontend reduction of declaration transitions or assertion/scenario meaning.

Write P for parent presence. `Lifetime.Through P t j` means uninterrupted parent
presence on the inclusive interval from t to j. The independent operator meanings
in [`Lifetime`](../Clafer/Behavioral/Lifetime.lean) are:

- X a: if the parent is live at t+1, a holds there.
- F a: the parent becomes absent at some future time, or a holds within the
  uninterrupted remaining parent lifetime, including t.
- G a: a holds at every point in that uninterrupted lifetime.
- a U b: some endpoint is either parent absence or b, and P and a hold at every
  preceding point from t to that endpoint.
- a W b: parent-bounded G a or parent-bounded a U b.

The left operand of U is still required before cancellation: parent termination
does not excuse an earlier violation. `always_before_end` and
`until_witness_before_end` bound the relevant interval/witness by any observed
absence; `not_through_after_end` excludes every later time even after reappearance.
`eventually_cancel` discharges F at the gap. A new live context can start a new
obligation later, but the earlier one never resumes. On an always-true P,
the five operators reduce to ordinary infinite-time semantics.

Initial/final anchors guard their body by `Trace.Starts` and `Trace.Ends` for the
**context**, not its parent. Starts includes time zero and every reappearance;
Ends is the last live state before absence. Both source signs retain the anchor
and change the body sign. A permanent root starts at zero and never ends. The
anchor atoms retain absolute trace history; no loop-periodicity assumption is
made for a later finite evaluator.

## Signed source meaning and normalization

`Formula.denote` directly defines positive and negative source judgments by
structural recursion. It does not refer to the normalizer or lowered core.
Source `not` flips the sign. Atoms and truth use classical polarity. Boolean
connectives compose signed operands: implication uses negative antecedent and
positive consequent, equivalence expands to two implications, xor to its two
opposite-sign cases, and a temporal conditional to its two guarded branches.
Temporal-free guards have classical signs by `temporalFree_polarity`.

Negative X retains X; negative F/G exchange G/F. Negative U becomes
`!b W (!a && !b)` and negative W becomes `!b U (!a && !b)`.
all/some exchange under negative polarity; positive no is all with a negative
body, and negative no is some with a positive body. Domain values are captured
at the quantifier time and body evaluation retains the attachment.

one/lone are **classical barriers**. Their result can be classically negated,
and their entire body is interpreted by `Formula.raw`: Boolean negations inside
that body are classical, with temporal nodes still parent-bounded. This preserves
the actual fallback in pinned `AlloyLtl.pushNegations`; it does not recursively
normalize a counting body. For example, after cancellation, `all x | !F error`
can hold while `one x | !F error` over a singleton fails. Nested all/some inside a
counting barrier likewise use raw Boolean meaning. `letSet` propagates the sign
to its body without changing its captured value or attachment.

[`normalize`](../Clafer/Behavioral/Normalization.lean) builds a formula with signs
pushed to literals or counting barriers. `normalize_normal` proves that shape;
`normalize_agrees` proves raw evaluation of the normalized result equivalent to
the independent source judgment, for every constructor, sign, environment and
time. `double_negation` is source double-negation elimination. Lean's own logic
remains classical throughout.

[`lower`](../Clafer/Behavioral/Lowering.lean) then constructs `Core`, whose temporal
operators are unbounded and whose negation is classical. It explicitly inserts
parent-presence guards and lifetime-anchor atoms. G lowers to ordinary
`(P && a) W !P`, which terminates at the first gap. `lower_agrees` proves agreement
with raw bounded interpretation; `normalize_lower_agrees` composes the two
independent proofs. `attached_lower_agrees` lifts the result to all attached
constraints. Lowering before normalization is not a semantics-preserving source
translation, as the `late_negation_rejected` countermodel demonstrates.

## Checked boundaries and source correspondence

[`FormulaExamples`](../Clafer/Behavioral/FormulaExamples.lean) uses the valid
cycling trace, rather than assuming validity of an arbitrary signal sequence.
Its witnesses cover both F polarities after cancellation, nested negation,
persistent-parent rejection, source/parent/root attachments, context-only death,
no resumption, all/some/no and one/lone distinctions, Boolean expansions, U/W,
initial/final anchors, captured sets and changing references. The general
`persistent_eventually_consistent` theorem rules out both F polarities for any
total atom under persistent parent presence. It makes no general contradiction
claim for vacuous initial/final anchors.

The primary source is the behavioral paper §5 Definitions 4–5 (pp. 2:27–28) and
§6.1 (pp. 2:30–32), deliberately amended by pinned T2/T3/T7 and D1. The
[source ledger](sources.md#behavioral-profile-sources) retains immutable hashes,
licenses and candidate locators. SoSyM remains authoritative for the untouched
static constraint semantics. These total-core theorems do not prove compiler
preservation, surface-pattern correctness or finite-lasso completeness.
`Formula.satisfies_iff_lowered` in `PartialCompatibility` supplies
the separate partial bridge while retaining the original formula's definedness.
