# Initializer contract

This contract consolidates the accepted collection and supported-form decisions
in [the initializer review](https://github.com/kbak/clafer-semantics/issues/170).
It describes hard constraints, not defaults that can be overridden. The
[candidate equations](behavioral-structure.md#candidate-initializer-equations)
remain separate from the versioned production `Initializers.elaborate` API.
Production adoption, source environment transport and compiler preservation are
tracked in the [integration task](https://github.com/kbak/clafer-semantics/issues/173)
and [environment review](https://github.com/kbak/clafer-semantics/issues/171).

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

## Verification and source correspondence

The resolved classification and bound results are independently importable and
remain outside the production behavioral aggregator. The lifecycle fixtures in
[`InitializerLifecycleExamples`](../Clafer/Behavioral/InitializerLifecycleExamples.lean)
retain actual parents, inherited reference ownership, abstract coverage and exact
head/target observations. Optional and exactly-one multiplicity variants are
structurally checked. `parented_abstract_observations` connects the inherited
collection to its abstract declaration view; `global_observations` connects the
parentless collection to all live abstract heads. The fixture has one concrete
realization, exercised under two actual parents; it is not a source elaboration
proof for arbitrary subtype families.

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
revision. The maintained production profile remains unchanged until the separate
integration work proves source environment transport and adopts these equations.
