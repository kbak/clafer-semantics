# Key proved properties

<!-- [impl->req~public-foundation~1] -->

Clafer Semantics proves properties of mathematical models, transformations and
candidate checkers in Lean 4. This guide selects the results that explain what a
user can rely on and what a downstream tool must still establish. A *configuration*
is one state of a system; a *trace* is an infinite history of states. A *span*
represents links with their own identities, so two links can share endpoints
without becoming one link.

The declaration links below cite the accepted [structural and behavioral source
revision](https://github.com/kbak/clafer-semantics/tree/f00e5dacb07eed51026f69fcf699683210d394d3).
The [source map](sources.md) retains the precise paper locators, immutable compiler
comparisons and accepted corrections: SoSyM Appendix 2 underlies DPGraph;
§6 and Appendices 4–6 underlie structural compilation; the behavioral paper's
§§5–6 and the [adopted profile](behavioral-profile.md) underlie traces and temporal
meaning. These results describe those corrected contracts, including deliberate
language choices, rather than an unqualified equivalence to either publication.

| Start here | What the proofs establish |
| --- | --- |
| [Graph foundations](#graph-foundations) | How links compose and models move between diagrams |
| [Metamodel realization](#metamodel-realization) | Exactly when encoded syntax satisfies the metamodel, and what can be reconstructed |
| [Structural Clafer](#structural-clafer) | Valid Compile output, conditional gluing/preservation and exact finite candidate checking |
| [Behavioral Clafer](#behavioral-clafer) | Snapshot agreement, meaning-preserving reductions and finite evaluation of supplied histories |
| [Worked model and execution evidence](#worked-model-and-execution-evidence) | A concrete satisfying model, and the distinction between proofs and external comparisons |

Unless marked as a concrete example, each result quantifies over all inputs
meeting its stated hypotheses. The linked declarations contain the complete
statements; the focused contracts explain their assumptions. Source-local
[IntentBond annotations](traceability.md#lean-artifacts) connect declarations to
requirements. This guide is a reading route, not a second coverage inventory.

## Graph foundations

### Composing links preserves routes and multiplicity

A composite span keeps each pair of links whose middle endpoints match.
Reparenthesizing three compositions preserves all link identities up to an
explicit bijection. Forgetting identities afterwards yields exactly ordinary
relational composition. This lets clients reason about reachability without
confusing the number of routes with the number of endpoint pairs.

Lean: [`DPGraph.Span.associator`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/DPGraph/Span/Composition.lean#L69) (a constructed
isomorphism) and [`DPGraph.Span.red_comp`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/DPGraph/Span/Relation.lean#L114).
These laws need no finite-carrier or injectivity assumption. Recovering the
composite span from its endpoint relation is stronger:
[`DPGraph.Span.comp_iso_relation_iff`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/DPGraph/Span/Relation.lean#L145) requires the
composite endpoint pairing to be injective. Two distinct routes with the same
outer endpoints violate that condition. See the
[span-composition correction and exact assumptions](sources.md#adopted-correction-and-exact-assumptions).

### Models restrict along declaration-preserving maps

If a diagram map sends every source declaration to a target declaration, every
target model gives a source model by following that map first. Translating an
individual formula and then interpreting it gives the same truth value as
interpreting its original binding through the map. These laws justify reuse of
models under structure-preserving mappings.

Lean: [`DPGraph.Interpretation.satisfies_translate`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/DPGraph/Semantics.lean#L49) and
[`DPGraph.Interpretation.isModel_reduct`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/DPGraph/Semantics.lean#L100).
The interpretation is fixed, and formulas retain their full graph bindings.
The reverse whole-model implication requires the target declarations to be
*exactly* the translated source declarations, as in
[`DPGraph.Interpretation.isModel_iff_of_declarations_image`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/DPGraph/Semantics.lean#L63);
extra target constraints can invalidate it. See
[DPGraph models](architecture.md#dpgraph-core-and-models) and
[exact declaration images](architecture.md#shared-semantic-infrastructure).

### Compatible component models combine on a supplied pushout

Given a carrier pushout—a graph that joins two graphs along a shared part with
its universal mapping property—models of the union of translated declarations
correspond exactly to pairs of component models agreeing on that shared part.
This gives a modular way to assemble interpretations without losing constraints.

Lean: [`DPGraph.Pushout.modelEquiv`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/DPGraph/Pushout/Models.lean#L59), a constructed
equivalence. The carrier colimit proof is supplied, agreement is equality of
restricted graph maps, and the semantic graph must fit the carrier universes.
The result neither constructs pushouts for every setting nor identifies concrete
Clafer gluing with one. See the
[conditional pushout/model construction](architecture.md#dpgraph-core-and-models).

## Metamodel realization

### Syntax satisfies the metamodel under two exact conditions

A well-formed class diagram can be encoded as objects representing its classes,
maps and declared formulas. That canonical encoding satisfies the unchanged
Figure 21c metamodel **if and only if** every declared formula has at least one
arity arrow and its symbol plus argument bag distinguishes it from every other
declared full formula. This identifies the precise obstacles to treating syntax
as a metamodel instance.

Lean: [`FormalCD.Metamodel.Realization.model_iff`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/FormalCD/Metamodel/Realization/Correctness.lean#L173).
The conditions apply to declared formulas, not unused vocabulary symbols.
Argument links retain repeated occurrences, while descriptors retain isolated
vertices and full bindings. This proves satisfaction of the metamodel by encoded
syntax, not satisfiability of the encoded diagram's own constraints. No universal
realizability follows. See the [restricted realization contract](metamodel-realization.md).

### Encoding and decoding recover the entire raw diagram

Decoding the canonical encoding recovers the original raw diagram on its fixed
carrier, including declarations, names, predefined identifiers and map modes.
Thus this representation loses no source syntax even when the two realization
conditions above fail.

Lean: [`FormalCD.Metamodel.Realization.decode_encode`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/FormalCD/Metamodel/Realization/Reconstruction.lean#L66).
Decoding uses the encoded map, the explicit name/arity context and separate mode
data. A bare Figure 21c graph alone does not contain all that information; the
result is not a decoder for arbitrary metamodel instances. See
[faithfulness and reconstruction](metamodel-realization.md#faithfulness-and-all-effective-declarations).

### The particular metamodel is a semantic instance of itself

For Figure 21c itself, the support and separation conditions are proved, so its
canonical encoding satisfies all thirty metamodel declarations. This is a concrete
self-instantiation result, beyond merely describing the metamodel's syntax.

Lean: [`FormalCD.Metamodel.Realization.Self.self_instantiation`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/FormalCD/Metamodel/Realization/Self.lean#L150).
The interpretation uses the context constructed for that diagram in a bounded
universe. It is not a universal context or a universe fixed point. Its finite
formula inventory does not make the entire interpretation finite: symbols and
strings retain their complete domains. See the
[assessment of the particular metamodel](metamodel-realization.md#assessment-for-the-particular-metamodel).

## Structural Clafer

### Compile produces a valid structural assembly

For every accepted resolved input, Compile constructs a valid model of Clafer
Shapes (MCS), deriving its hierarchy, naming, cojoining and formula disciplines.
The generated bank includes the local Shape declarations, inclusions and every
attached constraint occurrence. This establishes that the mathematical
transformation produces the intended structured assembly.

Lean: [`Clafer.Compile.wellFormed`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Compile/Basic.lean#L74),
[`Clafer.Compile.shape_declared`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Compile/Basic.lean#L78) and
[`Clafer.Compile.constraint_declared`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Compile/Basic.lean#L92).
`Compile.Input` supplies a finite resolved/defaulted AST, well-formed identities
and names, typed bodies on their exact boundaries, and **positive map support for
every attached constraint**. Context-only Boolean literals need not meet that
last condition. This is neither a parser/resolver theorem nor a satisfaction
proof for the generated formulas. See the [Compile contract](compile.md).

### Gluing preserves declarations and conditionally yields a valid class diagram

Gluing identifies roles with equal resolved referents and translates their full
formula bindings. The resulting declarations are exactly the translated bank.
With compatible incidence and metadata, valid naming and complete effective
defaults, the glued raw diagram is a well-formed FormalCD. This makes shared
references usable without identifying unrelated objects merely because their
names coincide.

Lean: [`Clafer.MCS.Gluing.declared_iff`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/MCS/Gluing.lean#L119) and
[`Clafer.MCS.Gluing.raw_wellFormed`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/MCS/Gluing.lean#L211).
Equal display names are insufficient for identification. Defaults must already
include inclusion predicates and ordinary-map set-valuedness; MCS validity alone
does not imply their completeness. Diagram validity still does not prove model
existence or automatic descent of arbitrary interpretations. See
[MCS gluing](architecture.md#mcs-gluing) and the
[model-descent boundary](metamodel-realization.md#source-to-obligation-comparison).

### Selected source constraints agree with the generated and glued model

For the selected inherited-realization fragment, extended structural satisfaction
and truth of every attached source body are equivalent to the corresponding
whole-model obligations on the canonically descended glued diagram. Constraint
meanings come from the typed bodies. This connects compilation to independent
source meaning, beyond syntactic validity.

Lean: [`Clafer.Compile.ConstraintMeaning.whole_model`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Compile/ConstraintMeaning.lean#L267).
The theorem takes `Compile.Input`, explicit external-binder domains, an integer
realization, a `Selected` inherited core and an `Admissible` shared-object
configuration. Admissibility requires literal inclusion and the chosen integer
extents. Typedness, root conditions and declaration disjointness remain explicit
on the target side. The exact generated bank, interpretation and canonical
descent matter: this is not unrestricted textual compiler correctness or
reflection for arbitrary gluing. See
[constraint preservation](constraint-preservation.md#binding-and-transport-assumptions)
and the [selected inherited fragment](inherited-realization.md).

### The finite structural checker decides its supplied candidate exactly

For a well-formed supported effective core, the Boolean checker returns true
exactly when the finite candidate realizes independent structural satisfaction.
This includes inheritance, root/parent/reference conditions, multiplicities,
groups and declaration disjointness. It makes acceptance and rejection meaningful
for that candidate rather than a heuristic approximation.

Lean: [`Clafer.Verification.check_correct`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Verification/Finite.lean#L121).
The [supported fragment](structural-checker.md#effective-input-and-domain) excludes
user expressions, primitive targets and richer inheritance combinations. Candidates
have a fixed finite object inventory; malformed input and unsupported models are
handled separately by the public interface. No instance generation or general
unsatisfiability result follows from checking one candidate. See the
[executable contract](structural-checker.md#executable-interface).

There is also a representation result:
[`Clafer.Verification.finite_model_representable`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Verification/Representation.lean#L48)
encodes any finite model of the exact local bank into an accepted candidate after
normalization and an object bijection. It requires the same well-formed/support
guards and explicit global conditions on the normalized model. This rules out a
representation gap within that domain; it does not prove every model is finite.
See [interpretation and normalization](structural-checker.md#meaning-and-interpretation).

## Behavioral Clafer

### Valid histories have valid structural snapshots

At every time, a valid trace gives a structurally satisfying configuration of its
currently live objects. Identities are shared across time; projecting a snapshot
preserves the occurrence fibers used for cardinalities and groups. This connects
changing systems to the static model without counting absent objects as members
of a configuration.

Lean: [`Clafer.Behavioral.Trace.snapshot_structural`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Behavioral/Snapshot.lean#L49).
The hypothesis is `Trace.Valid` and the snapshot's ambient carrier is `Trace.Live`
at that time. The stronger language-admission guards are separate.
The converse for the common structural fragment is
[`Clafer.Behavioral.Properties.Model.constant_iff`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Behavioral/Composition.lean#L137):
a constant history satisfies the behavioral model with no added modifiers or
constraints exactly when the original configuration satisfies the static model.
It needs a well-formed supported core, effective-group agreement and an explicit
`StaticCorrespondence` fixing direct types, actual parents and inherited extents.
See [projection and constant embedding](behavioral-traces.md#projection-and-constant-embedding)
and the [exact common fragment](behavioral-qualification.md#exact-static-common-fragment).

### Signed normalization and lifetime lowering preserve meaning

Normalizing source signs before inserting lifetime guards gives ordinary temporal
core formulas with exactly the original signed meaning. The proof covers every
constructor, both signs, all captured environments and every time. It justifies
the order of these transformations for downstream implementations.

Lean: [`Clafer.Behavioral.Formula.normalize_agrees`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Behavioral/Normalization.lean#L60)
and [`Clafer.Behavioral.Formula.normalize_lower_agrees`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Behavioral/Lowering.lean#L100).
These theorems use total observations. They preserve the original attachment's
parent lifetime and captured identities; `one`/`lone` retain their raw counting
bodies. Source negation is generally not classical complement after lifetime
cancellation. The translations are noncomputable mathematical definitions, not a
proved executable frontend. See the [signed formula contract](behavioral-formulas.md).

For partial observations,
[`Clafer.Behavioral.Formula.checkedCore_agrees`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Behavioral/PartialLowering.lean#L108)
adds a proved domain condition alongside signed truth. This preserves strict
undefinedness, including all required operands, quantified members and active
temporal observations; an early witness does not excuse later missing values.
See [strict partial lowering](behavioral-qualification.md#full-model-and-strict-partial-core).

### Modifiers, transition chains and all scoped patterns reduce to that core

The surface constructions have meanings that agree with their formula expansions:
initial/final reference and target obligations use the required attachment views;
transition chains retain required subsequent steps; all six patterns in all five
scopes preserve their signed judgments. This allows the common core proofs to
apply to these language constructs.

Lean: [`Clafer.Behavioral.Modifiers.expand_agrees`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Behavioral/Modifiers.lean#L241),
[`Clafer.Behavioral.Transitions.Chain.expand_agrees`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Behavioral/Transitions.lean#L122)
and [`Clafer.Behavioral.Patterns.expand_agrees`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Behavioral/Patterns.lean#L166).
Modifier agreement requires `Structural.Valid` and the supplied structural set
observations. Transition/pattern agreement uses total observations and covers
both signs and arbitrary temporal operands. Partial use retains the expanded
formula's strict domain. The adopted pattern intervals and reference views include
reviewed departures from the pinned compiler; no blanket equality to its emitted
Alloy is claimed. See the [surface contract](behavioral-surface.md), especially
[patterns and scopes](behavioral-surface.md#patterns-and-scopes).

### Complete source models reduce without dropping obligations

A behavioral model satisfies its source meaning exactly when its core is
well-formed, its trace is structurally valid, all effective modifier obligations
hold in the temporal core, and every attached constraint holds with its strict
domain. This composes the reductions above into a model-level result.

Lean: [`Clafer.Behavioral.Properties.Model.behavioral_core_iff`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Behavioral/Composition.lean#L97).
The model supplies the full constraint set, the declared modifiers and the
trace-dependent partial observations. Inherited modifiers are included through
`Modifiers.Effective`; structural validity remains an explicit conjunct rather
than being inferred from formula truth. See
[source composition](behavioral-qualification.md#full-model-and-strict-partial-core).

### Finite lasso evaluation agrees with the infinite history it represents

A lasso stores a finite prefix and a nonempty repeating loop. Evaluating core
formulas over its finite clock gives exactly their truth on its infinite unfolding.
The clock distinguishes the initial visit from later visits, so lifetime births,
deaths and cancellation also agree at loop boundaries.

Lean: [`Clafer.Behavioral.Core.finite_agrees`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Behavioral/FiniteEvaluation.lean#L225).
The fixed identity inventory and captured sets are finite. `FiniteObservation.Agrees`
must prove atom and domain agreement for every environment and absolute time;
matching a few stored samples is insufficient. Structural admission is a separate
gate. This is soundness and completeness for **one supplied lasso**, not a claim
that every source trace has a finite lasso representation or that searching a
bound decides unbounded satisfiability. See
[finite evaluation and observation agreement](behavioral-verification.md#initial-history-and-exact-temporal-evaluation).

For full model checking,
[`Clafer.Behavioral.Properties.bodyCheck_correct`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Behavioral/FiniteComposition.lean#L141)
connects a satisfied result to source-model satisfaction, with independently
proved richer structural admission, exact constraint/modifier inventories,
finite context selectors and certified partial adapters preserving missingness.
[`Clafer.Behavioral.Properties.commonCheck_correct`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Behavioral/FiniteComposition.lean#L172)
also executes structural checks on the guarded common fragment, retaining its
well-formedness, support and effective-group agreement assumptions. This finite
carrier cannot contain the whole mathematical integer domain; finite integer
adapters need separate adequacy and intermediate-range proofs. See
[finite composition and its boundaries](behavioral-qualification.md#finite-composition-and-its-boundaries).

### Assertions and scenarios have different quantifiers

An assertion fails exactly when some model trace is a counterexample. A scenario
is possible exactly when the original model extended with its scenario constraints
has a satisfying trace. This prevents treating one successful scenario as evidence
that every model behavior satisfies a property.

Lean: [`Clafer.Behavioral.Properties.Model.counterexample_iff`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Behavioral/Properties.lean#L74)
and [`Clafer.Behavioral.Properties.Model.possible_iff`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Behavioral/Properties.lean#L79).
These are logical equivalences over all model traces, not algorithms for searching
them. Counterexample failure classically negates the whole interpreted judgment,
including definedness, rather than inserting source `!`. See
[models, assertions and scenarios](behavioral-surface.md#models-assertions-and-scenarios).

## Worked model and execution evidence

### The complete telematics fixture has a satisfying interpretation

The manually resolved Appendix 6 fixture satisfies its actual compiled and glued
bank, with all twelve source bodies and final selections established together.
It demonstrates that the conditional structural and constraint bridges can have
their hypotheses discharged for a substantial concrete model.

Lean: [`Clafer.Examples.Telematics.compiled_glued_model`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Examples/Telematics/Compiled.lean#L191).
This is a concrete example proof, not a universal compiler result. It uses the
adopted inherited-field and paper-correction contracts, explicit integer
realization and an unrestricted primitive head. Its integer extent is infinite,
so it is not a finite-checker run. See the [complete telematics model](telematics.md).

### What execution and comparison establish

Lean proofs establish their formal propositions under the linked assumptions.
The repository's [validation](../CONTRIBUTING.md#setup-and-checks) separately builds
and kernel-replays declarations, audits allowed axioms and checks layer boundaries.
An ordinary native checker invocation is not a fresh kernel proof certificate for
its output, nor a verification of the native compiler/runtime.

The [bounded Haskell/Alloy comparison harness](bounded-comparison.md) supplies
empirical evidence about exact supplied candidates, manual scopes, selected
source pins and external solver runs. Agreement is useful corroboration;
disagreements can expose missing assumptions. Neither result proves universal
compiler correctness, complete trace search or unbounded UNSAT.

Parsing, name resolution, executable elaboration, target encoding, serialization
and solver integration belong to
[Clafer Compiler](https://github.com/kbak/clafer-compiler-lean).
Its [companion key-properties guide is tracked in compiler issue #97](https://github.com/kbak/clafer-compiler-lean/issues/97);
until that guide is published, use its
[qualification contract](https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/docs/qualification.md).
That accepted compiler revision pins the semantics revision cited here. Upstream
semantic equivalences supply its foundations; downstream compiler guarantees
require the compiler's own proofs and representation, scope and arithmetic
hypotheses.
