# Initializer contract

This contract defines the hard initializer extension adopted in the
[definedness](https://github.com/kbak/clafer-semantics/issues/169),
[supported-form](https://github.com/kbak/clafer-semantics/issues/170) and
[environment/lifetime](https://github.com/kbak/clafer-semantics/issues/171)
reviews. These are constraints on a trace; they neither assign values in sequence
nor provide overridable defaults. Production `Initializers.elaborate` selects the
accepted clocks and diagnostics. Its generated expansion is proved equivalent to
the independent [equations](behavioral-structure.md#candidate-initializer-equations).
The historical strict-implication and `:=` rejection API is explicitly retained in
`Initializers.Legacy`; the static importer and broader source-profile pin are unchanged.

## Declaration classification

Classify each authored `:=` once, preserving its declaration, RHS environment and
clock through inheritance. A refined declaration can add its own initializer;
the obligations conjoin. Refining multiplicity does not reclassify an inherited
initializer, override its RHS, or partition its original collection into separate
subtype collections. All members of the original declaration view participate.

The [resolved classifier](../Clafer/Behavioral/InitializerClassification.lean)
receives authored abstractness, presence of a containment parent, optional authored
multiplicity and the complete effective parent group. Ordinary top-level declarations
have the permanent root as their containment parent. Parentless abstracts have no
such structural parent. Names, types, groups and inheritance must already be valid;
this interface does not implement a parser or resolver.

| Declaration carrying its own initializer | Clock |
| --- | --- |
| Ordinary declaration with effective upper bound 0 or 1 | Every head's birth; zero heads impose no obligation |
| Parented declaration with explicit upper bound greater than 1 or unbounded | Every birth of the declared enclosing parent context |
| Abstract declaration with omitted multiplicity | Every instance's birth, requiring scalar RHS admission |
| Parented abstract with explicit upper bound 0 or 1 | Every instance's birth, requiring scalar RHS admission |
| Parentless abstract with explicit `*` or trailing `0..*` | Global collection at time zero |
| Parentless abstract with another authored bound | Unsupported in this initializer profile |

Explicit bounds override child defaults. Ordinary omitted bounds use the
[accepted child-default policy](sources.md#current-child-default-policy): numeric
`0..*` groups yield `1..1`, whereas keywords and other numeric groups yield `0..1`.
An omitted group inherits the complete effective group, including keyword provenance.
Thus `opt` and numeric `0..*` have equal group ranges but different child defaults.
A one-child xor can require an optional child to exist without changing its clock.

Neither RHS cardinality, set/bag reference kind, arbitrary constraints such as
`#xs <= 1`, nor backend scope changes the classification. Omission must remain
distinguishable from explicit `*`, even where their allowed head counts coincide.

## Guard, collection and inheritance meanings

For head set H, distinct target image T and partial RHS observation r, the equation
is `H.Nonempty → r = some T`. The guard is outside general Boolean evaluation.
Empty heads impose neither definedness nor equality. `none` and `some ∅` remain
different; neither satisfies an active reference equation with nonempty heads.
General Boolean implication remains strict.

For per-instance initialization, each head's birth requires the RHS to equal its
singleton target. For a parented collection, only parent births check the complete
target image. Later additions, removals, replacements and target/RHS changes impose
no new collection obligation. Parent rebirth checks again. Multiplicity, reference
totality, keys, group constraints and modifiers continue to apply independently.

A parentless abstract collection includes all live instances of its abstract view,
across concrete realizations and actual parents. It is attached to the permanent
root evaluation context and checked at time zero. Concrete parent births and
rebirths do not restart it. This supplies no structural parent map, global head
cardinality or global reference key for the abstract. The theorem
`Candidate.permanent_context_iff` proves that the birth equation for any context
present throughout the trace reduces to its time-zero guard.

Bag initialization compares distinct targets, not occurrence counts. Three heads
with targets `1,1,2` or `1,2,2` both match RHS `1,2`; repeated RHS literals are
idempotent. Missing or extra targets fail. The same three-head configuration with
a set arrow cannot satisfy uniqueness and a two-target initializer. Cardinality
counts heads even when dereferences coincide.

Inheritance preserves both clock and scope. For `abstract Val -> integer := 1`
and an own `xs : Val * := 2`, an empty parent birth followed by a late head at 1
is allowed. A late head at 2 fails the inherited per-instance obligation. At a
nonempty parent birth the two obligations conflict. Conversely, inheriting a
parented collection `X * := 1` and narrowing its realization to `?` still permits
a late head at 7. Narrowing to exactly one permits a later replacement born at 7,
provided the initial head starts at 1 and the count stays one.

## Scalar admission and its proof boundary

Every per-instance abstract `:=` requires an at-most-one RHS result bound when
defined. This admission restriction applies in static and temporal models, even
to unused abstracts. It does not require evaluation or definedness at inactive
births. An optional RHS is admissible but an empty result cannot initialize a
present head. A scalar expression such as `1 / 0` is admissible; an active birth
requiring it fails definedness.

[`Bounds.scalar`](../Clafer/Behavioral/InitializerBounds.lean) gives a conservative
analysis of the existing resolved `CollectionExpr`, without changing evaluation:

| Expression | At-most-one admission rule |
| --- | --- |
| Resolved set/navigation leaf | Supplied declaration/navigation bound certificate |
| Integer literal or scalar integer expression | Admit when defined |
| Minimum/maximum selection | Admit when defined, including a defined empty selection |
| Union of two equal integer literals | Admit; repeated target is idempotent |
| Other union | Not established by this analysis |
| Intersection | Admit if either operand has an at-most-one bound |
| Difference | Admit if its left operand has an at-most-one bound |

The analysis is conservative, not a complete semantic cardinality decision
procedure. It is kernel-reducible; as with the source evaluator, `noncomputable`
suppresses native recursion helpers for the mutual syntax. This does not add
choice or termination axioms, or claim delivery of a native frontend checker.
The analysis must not consult arbitrary model constraints. For example, a
declared `pool *` remains an unbounded leaf even with `#pool <= 1`; `pool ?`
provides an at-most-one declaration bound. `pool.dref ** 1` is scalar by its
intersection rule. Bound analysis never discards undefined operands.

`scalar_sound` proves that every admitted defined result is a subsingleton,
assuming sound bounds for the resolved leaves in the evaluated environment.
`heads_scalar_of_bound` extracts that property from an actual at-most-one head
bound, and `reference_image_scalar` transports it through functional references.
`captured_deref_scalar` establishes the optional-navigation case against the
actual set evaluator, using structural validity and a captured head bound.
These are independent premises, not bounds inferred from the initializer equation
being checked. The frontend must supply the leaf lookup and establish its
declaration/navigation correspondence. Arbitrary supplied Boolean labels alone
are not certificates; compiler preservation must discharge `leaf_sound`.

`aggregate_iff_singletons` proves the key compatibility step: for one head set H,
target function f, and one scalar partial RHS r,

```text
Guarded H (f '' H) r  ↔  ∀ x ∈ H, r = some {f x}.
```

The same RHS observation must be used for each head of that attachment. This is
where lexical environment preservation matters. For concrete single declarations,
`aggregate_iff_singletons_of_head_bound` obtains the same equivalence from an
at-most-one head bound, with no scalar-RHS restriction.
`supported_constant_iff_aggregate`
composes this result with #169's constant-trace theorem: birth-only singleton
initialization and every-live singleton equality both agree with the aggregate
guard for live heads and stable live/head/target/RHS observations in the admitted
domain: either the concrete head bound or the abstract scalar admission suffices.
The collection theorem retains separate context stability. Stable undefined RHSs
are allowed behind empty guards. It is not a theorem that merely moving source
names preserves their environment.

Without scalar admission, two abstract instances valued 1 and 2 can jointly
satisfy static aggregate equality to `1,2`, while neither singleton can satisfy
per-instance initialization, even on a constant trace. The restriction excludes
that `:=` form; it does not change the existing aggregate `=` meaning. A concrete
optional `x := 1,2` is different: both static and temporal meanings already force
absence, so it remains a well-formed constraint conflict.

## Diagnostics and explicit support limits

Invalid names, incompatible types and invalid multiplicity intervals are source
errors regardless of presence. Frontend checking precedes the resolved classifier.
Unsupported scalar admission or nontrivial parentless abstract bounds produce
unsupported-form diagnostics, not an alternative initializer interpretation.

The scalar diagnostic reports that the supported rules cannot establish an
at-most-one bound. It must not assert that the model necessarily produces several
targets. Classification is identical across static/temporal modes and backends.
There is no fallback that picks a target, distributes RHS entries, or changes clocks.

Well-formed constraint conflicts remain constraints. Under a mandatory parent:

| Example | Outcome |
| --- | --- |
| `x -> integer 0 := 1 / 0` | Allowed; no evaluation obligation |
| `x -> integer 0 := missingName` | Name error |
| `x -> integer 2..1 := 1` | Invalid range |
| `x -> integer ? := 1,2` | Allowed source; x cannot be present |
| `xs -> integer 2 := 1` | Allowed source; no satisfying configuration |
| `xs ->> integer 2 := 1` | Allowed with two heads targeting 1 |

Diagnostics must distinguish an impossible nonempty birth from an impossible
instance: `X * := 1,2` refined to `x ?` can start empty and later gain a head at 7.
An impossible child configuration may force an optional parent absent rather
than make the whole model unsatisfiable. No generic “has no effect” warning follows.

Only omitted or explicitly unrestricted multiplicities are admitted on parentless
abstract initializers. Trailing `0..*` and `*` normalize to the same authored bound;
omission retains separate provenance. Bounds such as `?`, `1`, `2` and `1..*`
need a separately accepted global-cardinality contract. They must not be ignored
or silently interpreted per actual parent. To require two global X heads at every
state, use an explicit `G (#X = 2)` constraint alongside `X * := 1,2`; initialization
still checks target equality only at time zero.

## Production transport and proof domain

[`Initializers`](../Clafer/Behavioral/Initializers.lean) separates `Meaning` from
`expansion`; `expansion_agrees` connects them. It accepts a resolved RHS syntax
family and its partial observation adapter. Thus full formula conditions are not
restricted to the older `CollectionExpr` grammar. The adapter must implement its
source language independently; an arbitrary callback is not a frontend
preservation certificate. Resolved declaration metadata, names/types and scalar
leaf bounds remain the caller's obligations. `Structure.metadata` constructs
classification metadata from the structural declaration and supplied authored
multiplicity; authored/default provenance is never reconstructed from values.

[`Transport`](../Clafer/Behavioral/InitializerTransport.lean) constructs a frame
with the child's attachment, a reserved generated-binder slot, the original
context identity, and unchanged captures in successor slots. `restore_move`,
`restore_push` and `observation_preserved` prove equality of complete partial
observations at every time. The restored environment is passed to the whole
source evaluator, including its temporal operators, anchors and nested binders.
No equality between independently supplied moved/original observations is assumed.
`attach_parent` uses fixed actual ownership; `Structure.parent_rhs` derives it
from containment. A parentless abstract retains root even in a nested realization.
Names and reference-owner identities are not resolved again during transport.

`Transport.condition` observes a full formula's raw truth after checking its
strict domain. `choose` requires both branch values. The generated outer
`initially` tests the child for per-instance initialization; temporal operators
and anchors inside the RHS still inspect the original context. If Box and x
disappear after zero, `if X (some flag) then 1 else 2` in Box observes the next
state under root and yields 2 when flag is absent. A name-only move into x cancels
X when Box disappears and yields 1. The transport witnesses retain this difference,
direct navigation through absence and captured-value/binder equations.

[`Structure`](../Clafer/Behavioral/InitializerStructure.lean) constructs complete
head/target views from valid traces, proves shared inherited targets, and obtains
original environments from fibers. Effective inheritance retains the complete
authored obligation, including clock, RHS and scope. `Bundle` conjoins obligations;
its permutation theorem states simultaneous constraint meaning. Qualified or
same-name super lookup remains [compiler #129](https://github.com/kbak/clafer-compiler-lean/issues/129).
A replacement parent cannot own the old child identity; fixed ownership requires
a different child with a fresh birth obligation.

[`Compatibility`](../Clafer/Behavioral/InitializerCompatibility.lean) connects
production meaning to aggregate/singleton agreement. Concrete bounds come from
structural multiplicity; abstract scalar bounds come from the independent
primitive analysis, and strict conditionals preserve scalarity from both branches.
[`Static`](../Clafer/Behavioral/InitializerStatic.lean) proves stability of every
primitive collection/integer/fold constructor on the canonical constant embedding
and composes it with production/static agreement. Structural validity, the guarded
common fragment and scalar/head-bound admission stay explicit. Temporal value
conditions can depend on anchors even on a structurally constant trace; their
stability is a separate obligation. Empty guards still permit `none`.

## Finality and inherited equations

[`Finality`](../Clafer/Behavioral/InitializerFinality.lean) proves that, on an
initialized uninterrupted lifetime with fixed target q, every-live equality adds
exactly the requirement that the original RHS stay defined and equal to q.
`production_equivalence` obtains `:=`/`=` agreement under `finalref`, within-life
RHS observation stability and the singleton/scalar admission needed to connect
aggregate equality. Stability outside that lifetime is unnecessary. This theorem
does not apply to a collection's different initialization clock.

A changing RHS or one that becomes undefined later separates the forms even
with final references. Adding `final` fixes heads as well; it does not evaluate a
later RHS or remove this distinction. Own and inherited equations conjoin even
when their original environments differ. Contradictory birth equations forbid
that instance; optional absence can still satisfy the model. Mixed `:=`/`=`
obligations do not override each other. Reference lookup, source order or names
cannot introduce an override policy.

Frontend construction of resolved input, static-first temporal classification,
backend preservation and [temporal-let reference compatibility](https://github.com/kbak/clafer-semantics/issues/174)
remain downstream. The present transport preserves the adopted captured-value
semantics and does not assert agreement with Haskell substitution. Pure assertions
remain separate from model constraints, and soft constraints/default optimization
remain outside this initializer API.

## Verification and source correspondence

The resolved classification, bounds, transport, structural observation and
production compatibility results are available through `Clafer.Behavioral`. The lifecycle fixtures in
[`InitializerLifecycleExamples`](../Clafer/Behavioral/InitializerLifecycleExamples.lean)
retain actual parents, inherited reference ownership, abstract coverage and exact
head/target observations. Optional and exactly-one multiplicity variants are
structurally checked. `parented_abstract_observations` connects the inherited
collection to its abstract declaration view; `global_observations` connects the
parentless collection to all live abstract heads. The fixture has one concrete
realization, exercised under two actual parents; it is not a source elaboration
proof for arbitrary subtype families.

Production witnesses additionally exercise the resolved source adapters and the
generated formulas:

| Obligation | Evidence |
| --- | --- |
| Full temporal condition in Box, versus a name-only move into x | [`SourceExamples.temporal_condition_counterexample` and `source_elaboration`](../Clafer/Behavioral/InitializerSourceExamples.lean) |
| A replaced parent and its fresh child use the new original context | [`ReplacementExamples.replacement_elaboration` and `fresh_parent_child`](../Clafer/Behavioral/InitializerReplacementExamples.lean) |
| Simultaneous `x := y` and `y := x`, with later changes allowed | [`SimultaneousExamples.both_birth_equations` and `later_change`](../Clafer/Behavioral/InitializerSimultaneousExamples.lean) |
| Inherited root RHS versus own parent RHS, retained super record, and conflicting own birth/every-live equations | [`ProductionExamples.inherited_context_initializes`, `inherited_record_preserved` and `own_context_conflicts`](../Clafer/Behavioral/InitializerProductionExamples.lean) |
| Changing or later-undefined RHS under fixed heads and references | [`ProductionExamples.final_does_not_remove_rhs_distinction`](../Clafer/Behavioral/InitializerProductionExamples.lean) |
| Direct navigation through absence and generated/source binder separation | [`TransportExamples.absent_direct_navigation`, `moved_absent_parent` and `capture_avoiding`](../Clafer/Behavioral/InitializerTransportExamples.lean) |

The inherited-context fixture has one concrete realization; the simultaneous
fixture has two distinct resolved sibling references. Their source observations
and structural states are explicit. They establish semantic elaboration, not
frontend parsing, same-name lookup or reference-compiler compatibility.

The following results in
[`InitializerContractExamples`](../Clafer/Behavioral/InitializerContractExamples.lean)
record the distinguishing outcomes. Finite target identities stand for distinct
values; their arithmetic interpretation is irrelevant to these clock/collection
checks.

| Obligation | Evidence |
| --- | --- |
| Empty parent birth, then inherited value 1 versus own collection RHS 2 | `late_one_two_clocks`, `late_two_rejected_by_inherited` |
| Conflicting equations at a nonempty shared birth | `distinct_birth_obligations_conflict` |
| Later removal and undefined/changing RHS | `removal_and_changing_rhs` |
| Narrowing to exactly one, then replacement with a fresh different value | `exactly_one_replacement` |
| Narrowing to optional: empty birth, then a value outside the initializer RHS | `optional_collection_late_outside_rhs` |
| One global collection across two parents, unlike two parent collections | `global_cross_parent` |
| Empty global birth and later concrete parent/head birth | `global_late_parent` |
| Three bag heads with distributions A,A,B and A,B,B at fresh time zero | `Bags.repeated_bag_birth` |
| Missing/extra bag targets at fresh birth, head-count and key conflicts | `Bags.missing_and_extra_rejected`, `cardinality_not_waived`, `repeated_bag_conflicts_with_key` |
| Concrete optional multi-target conflict and two-head set/bag contrast | `optional_multitarget_iff_empty`, `set_two_heads_singleton_rejected`, `two_bag_heads_singleton` |
| Scalar admission and the excluded abstract grouping counterexample | `scalar_admission_examples`, `multivalued_abstract_counterexample` |

The diagnostic conflict results include general observation-level proofs; they
are not all complete source-model witnesses. Bag restarts retain structural
admission, including exact-three head and group constraints. Testing a bad initial
target set at a fresh time zero does not forbid that set later in an existing
parent lifetime. The classifier's `ordinary_default_single` covers every effective
group, and `default_and_abstract_matrix` checks keyword/numeric provenance,
omitted/explicit abstract bounds and diagnostic distinctions. Frontend name/type
checking and construction of resolved provenance remain integration obligations.

Existing #169 witnesses cover undefined/empty RHSs and parent rebirth; the new
results extend those obligations without weakening their structural premises.
Source snippets are explanatory examples, not outputs of a verified parser or a
new Haskell/Alloy comparison.

The [source ledger](sources.md#initializer-supported-form-decisions) records the
accepted decision comments, paper sections and immutable supplementary compiler
revision. The production extension uses these equations with proved original-context
transport; the historical strict profile remains available explicitly in `Legacy`.
