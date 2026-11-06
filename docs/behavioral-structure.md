# Behavioral structural prerequisites

`impl~behavioral-structural-audit~1`

The [behavioral profile](behavioral-profile.md) requires structural atoms beyond
the guarded [trace foundation](behavioral-traces.md). This audit identifies the
existing declarations that can be reused, their assumptions, and the missing
bridges owned by [structural atom compatibility (S4)](https://github.com/kbak/clafer-semantics/issues/126).
The checked observation and conversion interfaces below do not assert proofs
for the remaining richer structural cases.
The [source ledger](sources.md#behavioral-profile-sources) fixes the 0.5.7
candidate and document hashes. S1–S11 below name its static errata; T8/T10/T11
name its temporal errata, not implementation milestones.

## Reuse and required extensions

| Prerequisite / profile rows | Existing declarations and exact boundary | Remaining S4 obligation |
| --- | --- | --- |
| Own and inherited groups; B05/B32; S1–S5, T10–T11 | `Semantics.Groups.ChildObjects` unions child heads over the super closure, independently of Compile. `Compile.Groups` retains definitionally equal aliases and unchanged proofs. `GroupObservation.childrenEquiv`, `bounds_iff` and `holds_iff` transport the complete union to the live carrier. `Configuration.Groups` in the guarded snapshot bridge counts direct children only. | Enforce the inherited predicate in richer behavioral states. The transport theorem does not derive inherited-group validity from direct-only validity. |
| Abstract types and ordinary inherited fields; B01/B05 | `Realization.Core` retains authored abstractness. `Realization.Abstracts` covers explicit abstracts; `View`, `Contains`, `Deref`, `same_parent_fiber` and `deref_agrees` restrict existing objects/links. `Core.Selected` only admits the documented Appendix 6 combinations. | Extend realization to nested explicit abstracts and parent refinement (S6), retaining one object/parent through inherited views. The current selected theorem does not supply this extension. |
| Nested abstractness and parent refinement; B01; S6 | `AST.WellFormed.nested_abstract` and `MCS.Family.WellFormed.nested_abstract` require an abstract parent of an effective abstract child. Their `inheritance_parent` clauses require equal declared parents when the super has one. | Support an abstract type under a concrete parent and a subtype nested under a refinement of the super's parent through a richer behavioral model and explicit common-fragment adapter. This implements S6; the module split is an engineering choice. Removing `EffectiveCore.Supported` alone cannot admit these cases. |
| Inherited references; B04/B06/B18; S8–S9, T8 | `Family.reference` and `Configuration.deref` are declaration-indexed. `EffectiveCore.Supported` requires basic abstract heads and basic subtype declarations; `Realization.Core.Selected` requires basic super targets. `InheritedReference.Owner` resolves the nearest declared reference, with unique owner/ancestry proofs; `deref` and `shared_head` retain its current relation on shared heads. | Integrate these observations into richer state validity, including reference refinement between distinct owners. Distinguish subtype heads from their targets and retain reference kind and resolved target view. |
| Set versus bag occurrences; B04; S4, T11 | `Configuration.References` requires one target per head. `Keys` identifies equal parent/target pairs only for set references. `Trace.snapshot_distinct` retains different heads, and the existing bag fixture retains two heads at one target. | Extend the same rules to inherited references. Verify that two bag heads count twice in child groups and remain distinct when targets change. The target image may still be a singleton. |
| Target validity and disappearance; B04/B06 | `Trace.StateValid.typed` uses `Configuration.Typed` on `Trace.raw`; both dereference endpoints must belong to live heads. Raw relations are not filtered to hide invalid endpoints. `Trace.Valid.parent_live` also requires live parents independently of declaration views. | Preserve live, typed targets in the richer model. Distinguish a dead head from a live head with a dead target: the latter violates validity. Relate current observations to these obligations explicitly. |
| Actual parent, root and top-level policy; B01/B06; S7 | `Identities` fixes actual parents independently of declaration parents. `parent_stable` spans all lifetimes; `top_level_parent` derives the synthetic root in the guarded model. `raw.contains` only supplies parent-bearing declaration views. | Supply actual-parent navigation for abstract contexts with mixed top-level/nested realizations. A parentless abstract declaration must not acquire an invented declaration parent. The observation of a stored absent identity is different from live containment. |
| Resolved head/target navigation; B06/B08; S8–S9 | `Constraints.Support` retains explicit head, parent, dereference, target and inclusion map occurrences. `Expr.map`, `image`, `join` and widening have independent meanings; repeated support occurrences retain resolved identity obligations. | Prove resolved inherited target-view agreement. Implicit dereference insertion and the unresolved name-search order stay with the frontend; source meaning must not guess them. Explicit dref must not be inserted a second time. |
| Live sets, this, stored variables and quantification; B07–B08 | `Constraints.Environment` stores one context object and singleton lexical variables. `Admissible` requires current class membership. `Expr.denote_support_congr` compares observed extents/maps with a fixed environment and integer realization; it is not a temporal-environment transport theorem. | Use the accepted D1 capture/current-observation rule. Relate singleton environments on their admissible domain, and account separately for stored sets, absent identities and live-filtered standalone this. Prove quantifier agreement with the domain evaluated before binding. |
| Primitive observations; B31 | `IntegerBinding` represents all mathematical integers. Strict extraction retains its singleton obligations. `ReferenceObservation.finite_targets` derives a finite target image from finite heads and functional dereferences; `valid_finite_targets` derives functionality from guarded trace validity. `IntegerObservation.coerce` implements the reviewed finite-set-sum conversion. | Connect richer structural/temporal atoms to these interfaces and supply range obligations for bounded downstream arithmetic, without making the whole integer domain finite. |
| Arithmetic operations; B31; S11 | `Arithmetic` supplies mathematical addition, subtraction, multiplication, negation and partial truncating division/remainder, with zero divisors rejected. `Expr.Defined` and `Expr.Holds` keep undefined distinct from false; quantification requires every body on a domain member defined. | Integrate these operations with temporal atoms; connect occurrence-indexed sums/products and finite min/max selectors to resolved temporal expressions. Existing static meanings and proofs cannot be cited as implementations of these remaining operators. |
| Defaults and initializers; B32; S1–S2, T10 | `Defaults` validates supplied effective groups, keyword provenance, multiplicities and abstractness. It does not elaborate syntax. The pinned CheatSheet distinguishes constant `=` from default `:=` and says no backend supports the latter. | Preserve adopted child defaults. Classify initializer forms explicitly with S5/C6/C7; neither form is automatically a temporal birth initializer. Any exclusion of required syntax needs profile review, not a silent unsupported guard. |

`Realization` currently imports `Compile.GroupSemantics`. A behavioral module
cannot import it wholesale while satisfying the independent-source boundary.
Reuse therefore needs an owning-module extraction with unchanged static
theorems, or an independent definition with a proved correspondence. The
[dependency tests](../tests/behavioral_dependencies.lean) must continue to
exclude Compile and Verification from `import Clafer.Behavioral`.

## Distinguishing cases

These cases expose missing obligations rather than declare a new meaning.
Existing checked witnesses are identified separately from required new ones.

* **Inherited group:** abstract xor A owns optional x/y; B extends A and adds
  optional z. A B instance with only z meets the effective inherited xor.
  Enforcing A's original x/y invariant as well would reject it. The
  [group contract](group-compilation.md#source-and-selected-meaning) and its
  checked fixtures already establish this selected rule.
  [`GroupObservation.childrenEquiv`](../Clafer/Behavioral/GroupObservation.lean)
  preserves the whole inherited union under live projection; `bounds_iff` and
  `holds_iff` preserve its bounds without requiring finite object carriers.
* **Nested abstract:** a concrete System owns abstract Port and concrete p : Port.
  S6 permits the pattern; `Family.WellFormed.nested_abstract` excludes it.
  A sibling pattern with SubSystem extending System and owning p : Port also
  needs parent refinement rather than declared-parent equality. Neither is
  covered by `Realization.Core.Selected`.
* **Inherited reference:** abstract engine references Engine; motor extends
  engine. A motor head must use the inherited reference without allocating a
  second occurrence. T8 requires later final/finalref/finaltarget rules to see
  it. The current basic-super guards exclude this required example.
* **Repeated targets:** the existing
  [trace examples](../Clafer/Behavioral/Examples.lean) retain two bag heads and
  prove that mapping only to targets is noninjective. They also reject a
  dangling target and accept a target change during a continuous head lifetime.
  These are common-fragment witnesses, not inherited-reference tests.
* **Stored reference:** bind a head at time 0 with target a; change its target to
  b at time 1. The D1 disposition requires navigation from the stored head to
  observe b. A variable holding the target set captured at time 0 still holds
  a. Replacing the head by a new identity must not rebind either stored value.
* **Absence:** an absent stored head is not a member of the current live class,
  so the unchanged static `Environment.Admissible` cannot be asserted for it.
  Direct actual-parent navigation can still observe its surviving fixed parent
  under D1. A live-subtype snapshot alone cannot represent this environment.
* **Primitive finiteness:** `DenotationExamples.infinite_integer_cardinality`
  rejects counting the whole integer domain. `head_count`, `target_image` and
  `reduced_target_count` distinguish two heads from one target. A finite head
  observation with a functional dereference needs a finite-image proof; it
  does not justify a finite primitive universe or arbitrary singleton extraction.

The reference-modifier interface supplies three separate observations: the
child-head set for a parent, the head-to-target relation on those heads, and
its target image. Equal target images do not imply equal heads or equal
head-to-target assignments. Swapping two targets between two surviving heads
preserves the target set while changing both assignments.
[`ReferenceObservation`](../Clafer/Behavioral/ReferenceObservation.lean) defines
`heads`, `assignments` and `targets`. `snapshot_heads`, `snapshot_assignments`
and `snapshot_targets` prove exact image agreement through the live embedding,
assuming the existing `Trace.Valid` and a live parent. `target_live` and
`absent_head_no_deref` expose current validity; `absent_parent_heads` needs no
validity assumption. `finite_targets` only assumes finitely many heads and
functional references. Its guarded specialization does not require a finite
ambient carrier. The [witnesses](../Clafer/Behavioral/ReferenceObservationExamples.lean)
check swapped assignments, two bag heads at one target, head absence and a finite
integer observation in the infinite `Int` carrier. These are observations for
later modifier meanings, not proofs of final/finalref/finaltarget themselves.

[`InheritedReference`](../Clafer/Behavioral/InheritedReference.lean) adds a nearest
owner relation over declared references, not preflattened effective annotations.
An own reference stops lookup; a basic node follows its super. Successful lookup
has a unique ancestor owner with a target. Its `deref` observation restricts that
owner's current relation to the existing subtype heads. `shared_head` proves
agreement of two views sharing the owner; `functional` and `target_live` inherit
guarded trace validity, while `absent_head` follows directly from live membership.
The [fixtures](../Clafer/Behavioral/InheritedReferenceExamples.lean) retain two bag
heads at a shared target, observe a target change without replacing the heads,
and reject navigation after their disappearance. Lookup also stops at a nearer
redeclared reference. Agreement between distinct redeclared owners, richer model
admission and the complete inherited set-key obligations remain separate; these
fixtures do not claim those results.

## Integer-set conversion

The [reviewed D3 conversion](https://github.com/kbak/clafer-semantics/issues/126#issuecomment-6685233729)
uses the sum of a finite observed integer set for an arithmetic operand. An absent
optional numeric clafer contributes zero in arithmetic. Presence and relational
equality still operate on the original collection: the empty set is not `{0}`.
This convention is shared by the pinned Alloy generator's arithmetic functions
and Choco's `AstCompiler.asInt`. It sums distinct targets; explicit `sum`/`product`
over reference heads is a separate occurrence-sensitive operation.

[`IntegerObservation.coerce`](../Clafer/Behavioral/IntegerObservation.lean) is
defined exactly when its observation is finite and entirely in the supplied
`IntegerRealization.domain`. `coerce_empty` gives zero; `coerce_singleton` gives
the encoded integer. `agrees_with_extract` proves agreement on the entire defined
domain of historical singleton extraction. `operand` propagates a missing
expression result; it does not confuse that result with a defined empty set.
Infinite or noninteger observations remain undefined, and the arbitrary
off-domain decoder is never used. The
[witnesses](../Clafer/Behavioral/IntegerObservationExamples.lean) distinguish
absence from a present zero, check multiple distinct values and duplicate targets,
reject infinite/noninteger observations, and retain arbitrary mathematical `Int`.

The historical `IntegerRealization.extract`, `Expr.integerOf`, static denotation
and their requirements remain unchanged. The behavioral conversion is an explicit
additional interface. It does not itself add operators to a temporal expression
grammar.

## Mathematical arithmetic

The [reviewed scalar rule](https://github.com/kbak/clafer-semantics/issues/126#issuecomment-6685442865)
uses mathematical integers, division truncating toward zero, and the corresponding
signed remainder. Both division and remainder are undefined at a zero divisor,
including `0/0` and `0%0`. Undefined operands propagate. Thus an absent optional
number can contribute zero to addition or as a numerator, but makes a denominator
zero and the resulting division undefined. No source operation wraps at a backend
bit width or at the machine integer limit.

[`Arithmetic`](../Clafer/Behavioral/Arithmetic.lean) defines `Binary.apply`,
strict `Binary.eval`, and `negate`. `defined_iff` gives the exact domain;
`division_remainder` proves `b*q+r=a` for defined quotient and remainder.
`static_arithmetic_agrees` preserves historical scalar addition/subtraction.
The [witnesses](../Clafer/Behavioral/ArithmeticExamples.lean) cover signed division
and remainder, all zero-divisor cases, absence in either operand position,
propagation through multiplication by zero, and values beyond 32-bit range.

The [backend audit](https://github.com/kbak/clafer-semantics/issues/126#issuecomment-6685412556)
shows why these are explicit source choices. Alloy 6.2.0 admits bitvector
wraparound and total zero-divisor results by default; its `--nooverflow` mode
rejects the tested zero-divisor and overflowing witnesses. The pinned Choco
backend rejects constant `5/0` but simplifies `0/0` to zero before checking the
divisor. It does not wrap at the modeled Alloy bit width, but some Java constant
calculations wrap at 32 bits. Neither behavior is forced by model checking.
Future encoding correspondence must state finite-observation, nonzero-divisor
and sufficient-range assumptions, including intermediate expressions. These
probes compare specific pinned implementations; they are not a general
backend-correctness proof. Pins and source hashes are in the [source ledger](sources.md#behavioral-arithmetic-comparison).

## Aggregates and extrema

The [reviewed empty-extrema rule](https://github.com/kbak/clafer-semantics/issues/126#issuecomment-6685652746)
preserves a defined empty result for `min`/`max` of an empty integer collection.
Applying arithmetic conversion to that result gives zero; relational equality
with `{0}` remains false. A finite nonempty integer observation selects its unique
minimum/maximum object. Infinite or noninteger inputs are undefined.

[`Aggregate.Extreme.select`](../Clafer/Behavioral/Aggregate.lean) implements these
selectors; `select_defined_iff`, `select_subset`, `select_singleton`, `select_empty`
and `empty_extreme_operand` prove their domain, observed-object and conversion
properties. The same module supplies `Fold.eval` for explicit sums/products over
occurrence indices. It requires finitely many indices and a defined integer value
at each one, with empty identities zero and one respectively. Two heads pointing
to 3 sum to 6 and multiply to 9; implicit coercion of their distinct target set
`{3}` gives 3. `fold_defined_iff`, `fold_missing` and `fold_infinite` retain these
boundaries. The [examples](../Clafer/Behavioral/AggregateExamples.lean) check these
cases and positive/negative extrema, missing values and invalid observations.

The occurrence-indexed interface leaves frontend construction explicit. The pinned
compiler splits syntactic union operands before explicit aggregation; overlapping
operands can therefore contribute repeatedly. Agreement with a deduplicated union
requires disjointness, or the frontend must retain separate operand occurrences.
Neither the selector nor the fold makes the whole primitive domain finite.

## Source dispositions and open decisions

The [accepted profile](behavioral-profile.md#errata-coverage-and-deliberate-departures)
already adopts S1/S2/T10 child defaults, S3/S4/T11 effective group counting and
set-only keys, and S7's actual-parent/root distinction. S5's frontend rejection
of an unreachable group lower bound stays separate from the source meaning of
an empty context. S8/S9 require explicit resolved views; the separate
[name-resolution decision](https://github.com/kbak/clafer-semantics/issues/121)
does not block semantics over those resolved views. S10's missing compiler
support for concrete supers is a compiler limitation, not a reason to rewrite
the existing static semantics. S11's bounded backend arithmetic is not source
integer overflow semantics.

D1 now has an explicit
[stable-identity/current-navigation disposition](https://github.com/kbak/clafer-semantics/issues/125#issuecomment-6684850305).
Capture retains quantifier identities and evaluated let collections. Extents and
navigation use the observation time; standalone this is live-filtered, direct
navigation starts from its identity, and actual-parent navigation requires a
live target parent without requiring the child live. This deliberately differs
from the paper's snapshot-tagged expression equations (§5, pp. 2:26–28).
The pinned `AlloyLtl.genPExp'`, `thisAlive`, direct-this join and `parentRel`
support this comparison. Its `genConstraints` constrains reference targets only
while a head is live; agreement for off-live reference data must not be inferred
from those clauses.

The [source audit](https://github.com/kbak/clafer-semantics/issues/126#issuecomment-6685083999)
distinguishes the required S6/S9/T8 structural extensions from new arithmetic
choices. D3's finite-set conversion, zero-divisor rejection and mathematical
arithmetic and empty extrema are resolved above; integration with temporal
expressions and resolved aggregate operands remains required. The compiler distributes `sum`/`product` over
syntactic union, so overlapping operands cannot be claimed equivalent to
aggregation over a deduplicated head set without a disjointness condition.
For D4, constant `=` is a presence-guarded constraint; `:=` is documented as
unsupported and is currently emitted as an assertion. Neither supplies temporal
birth-initializer meaning. S5/C6/C7 still owe its explicit profile disposition.
The proposed full S4 requirement IDs remain reserved; the implemented conversion
and arithmetic interfaces have their own narrower requirements; they do not
discharge full S4 acceptance.

## Unchanged agreement domain and completion

`Trace.admissible_projection` still requires `EffectiveCore.WellFormed`,
`EffectiveCore.Supported` and `Trace.Valid`. Its result is exactly
`StructuralSatisfies` on the live carrier. `StaticCorrespondence.constant_admissible`
still requires those two model guards, `StructuralSatisfies`, and the explicit
direct-type/head-closure and parent/containment correspondence witness.
`constant_snapshot` recovers the complete original configuration through the
live-carrier equivalence. None asserts existence of that witness for every
structural configuration or covers all rows above.

All missing structural bridges above remain S4 work, including the inherited,
nested and integer cases excluded by the initial guard. S3 owns signed formula
composition and temporal environment operations; S5 owns modifier and initializer
surface meaning; C6 owns resolved structural elaboration; C8 owns arithmetic
and reference encoding correspondence. Required rows cannot become unowned
gaps or be discharged by tables alone. Acceptance needs actual declarations,
assumptions, positive/negative witnesses, full validation and semantic review.
Historical SoSyM and static compiler/oracle profiles retain their existing pins.

Covers:
- `req~behavioral-profile~1`
- `req~behavioral-structural-boundary~1`
