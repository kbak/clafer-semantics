# Architecture

This document explains how the three libraries fit together, why their
representations were chosen, and what their proofs establish. Read the
[product overview](intent.md) for scope and navigation, the [source map](sources.md)
for correspondence with the paper, and the trace maps for individual
implementation and proof declarations.

The repository `kbak/clafer-semantics` contains one Lake package, `clafer`, with sibling
public roots. Imports flow `Clafer -> FormalCD -> DPGraph -> Mathlib`.

| Layer | Responsibility | Public entrypoint |
| --- | --- | --- |
| `DPGraph` | Reusable graphs, spans, predicates, model restriction and conditional pushouts | [DPGraph](../DPGraph.lean), independently importable |
| `FormalCD` | Class-diagram metadata, morphisms, metamodel disciplines, restricted realization and bounded self-instantiation | [FormalCD](../FormalCD.lean), built on `DPGraph` |
| `Clafer` | Resolved syntax, Shapes, MCS, Compile/gluing, constraint meanings and finite structural verification | [Clafer](../Clafer.lean), built on `FormalCD` |

## DPGraph core and models

[Signature.lean](../DPGraph/Signature.lean), [Formula.lean](../DPGraph/Formula.lean)
and [Basic.lean](../DPGraph/Basic.lean) represent symbols with graph arities,
full `Prefunctor` bindings and declaration sets. A carrier is a directed
multigraph: `x ⟶ y` is an arrow type without identity/composition operations.
The category of bundled graphs supplies maps between carriers, not composition
inside a carrier. A binding retains vertex images, isolated arity vertices and
distinct arrow occurrences with equal images. Declarations require neither
global finiteness nor decidable equality or inference closure.

[Morphism.lean](../DPGraph/Morphism.lean) translates bindings by postcomposition
and proves declaration preservation. Maps can identify vertices/arrows, and a
target can have extra declarations. [Category.lean](../DPGraph/Category.lean)
uses these maps at a fixed signature and carrier universes. Syntax, arity,
carrier and semantic universes remain independent; see the
[representation decision](#dp-graph-representation-decision) for size and equality details.

[Semantics.lean](../DPGraph/Semantics.lean) interprets each predicate as a set
of satisfying arity maps into a fixed semantic graph Ω. A model map m satisfies
φ when `φ.binding ; m` belongs to that set. Associativity gives
`sat m (translate φ F) ↔ sat (F ; m) φ`; declaration preservation then restricts
models contravariantly along `F : S → T`. No closure/invariance axiom on meanings
is needed. The formula equivalence does not reflect whole-model satisfaction,
since T can declare more formulas. The derived split-map
[injectivity](spec.md#model-reduct-injectivity) and
[surjectivity](spec.md#model-reduct-surjectivity) results retain explicit composite
identity hypotheses. [SemanticsExamples.lean](../DPGraph/SemanticsExamples.lean)
checks small and larger semantic universes.

The concrete semantic graph uses subsets of one ambient U as vertices and spans
between their subtype carriers as arrows. Shared objects retain ambient identity.
For `U : Type u`, links in `Type (max u w)` give arrows in
`Type (max u w + 1)`; this is a bounded graph, not an all-universes SetMap.
[Supporting-source alternatives](sources.md#generalized-sketches-and-model-reduct-coherence)
compare ordinary signatures with marked/dependency-enriched arities and typed
pullback instances. They do not establish a bridge or justify another dependency;
closure, consistency, size and coherence would require separate contracts.

[Pushout/Basic.lean](../DPGraph/Pushout/Basic.lean) places the
[union of translated declarations](spec.md#declaration-unions-on-carrier-cocones)
on a supplied carrier cocone and records compatible component models.
[Universal.lean](../DPGraph/Pushout/Universal.lean) lifts a supplied carrier
colimit to a [DP-graph colimit](spec.md#pushout-universal-property): the mediator
preserves the union and inherits factorization/uniqueness from the carrier.
[Models.lean](../DPGraph/Pushout/Models.lean) derives
[model amalgamation](spec.md#model-amalgamation-on-a-carrier-pushout) using that
same universal property and satisfaction under translation. Here Ω shares the
fixed carrier universes. No global pushout existence or concrete Clafer gluing
theorem follows. [Trace artifacts](dpgraph-trace.md) give the named declarations.

Examples, including [Examples.lean](../DPGraph/Examples.lean), are checked
separately from public imports. The [validation workflow](../CONTRIBUTING.md#setup-and-checks)
discovers every owned module, rejects reverse/unowned imports and audits all
project declarations, including unimported helpers.

## DP-graph representation decision

Keep Mathlib `Quiver`, `Prefunctor` and bundled `Quiv` for SoSyM Appendix 2
Definitions 6–10. The [graph representation assessment issue](https://github.com/kbak/clafer-semantics/issues/13)
records the acceptance evidence and dependency-cost comparison. The delivered
[core requirements](spec.md#graphs-signatures-and-typed-declarations) and
[trace artifacts](dpgraph-trace.md#core-representation) state the checked contract.

The [decision table](#nine-architectural-decision-areas) records the alternatives
for [graph representation (A1)](#design-a1), [full bindings and declaration sets
(A2)](#design-a2), [morphisms (A3)](#design-a3), and [interpretations (A5)](#design-a5).
The details below explain the representation's equivalence, size and equality
boundaries.

An explicit vertex/edge/source/target record is mathematically equivalent to
endpoint-indexed arrows: take the total edge type `Σ x y, (x ⟶ y)` in one
direction and the fiber `{e // source e = x ∧ target e = y}` in the other.
This is an explanatory correspondence, not a new Lean equivalence theorem.
`Set (Formula σ G)` matches Definition 9 without global finiteness or decidable
equality; finite lists, `Finset` and executable maps belong at algorithmic
boundaries. `Quiv` also supplies the category and colimit interfaces. A local
Quiver/Prefunctor bundle could reduce the syntax-only import closure, but would
need adapters for the delivered carrier cocones and conditional pushout/model
amalgamation results; see the [dependency-cost decision](#dependency-cost-decision).

The independent universes in `Signature.{s,va,ua}` bound symbols, arity arrows
and arity vertices. `DPGraph.{s,va,ua,v,u}` adds carrier arrow and vertex bounds;
`Interpretation` adds independent semantic bounds. `Hom` supports different
source and target bounds, while each category fixes its carrier bounds. A
dependent binding's arrow action has endpoints determined by its vertex action:
`Hom.ext_of_obj_map` therefore uses the endpoint transports of `Prefunctor.ext`,
and `Hom.ext` removes only the proof-field distinction. Translation and morphism
laws reuse `Prefunctor.comp_id`, `id_comp` and `comp_assoc`. These obligations are
exercised by the existing [structural](../DPGraph/Examples.lean) and
[semantic](../DPGraph/SemanticsExamples.lean) witnesses, including noninjective
arrow maps, repeated arguments, isolated vertices, failed declaration
preservation and larger semantic universes.

### Dependency-cost decision

Retain the current `Mathlib.CategoryTheory.Category.Quiv` import and both
dependency pins. That module includes category, adjunction and path-category
machinery beyond the smaller `Mathlib.Combinatorics.Quiver.Prefunctor` import.
The [representation assessment](https://github.com/kbak/clafer-semantics/issues/13) measures the exact imported environments, cached import
processes and rebuilding each named Mathlib module with cached prerequisites.

Retained and fresh full validation runs assess a fresh project build with pinned
dependencies already provisioned against the baseline scope's 900-second test
limit; CI separately has a 60-minute job limit. This evidence supports the
existing design in that environment. It does not measure rebuilding the whole
dependency closure from source or a machine with cold filesystem caches, nor
guarantee the same timing on another runner. The unchanged check retains its
source-build fallback when the optional Mathlib cache is unavailable.

The larger import closure alone does not justify a local wrapper: the public
foundation already uses graph-category colimits, so such a change needs an
end-to-end comparison including adapters, build/kernel checks and public API
compatibility. Reassess if supported-runner validation approaches its budget or
a separately scoped syntax-only consumer needs smaller imports. Measurements,
commands, source identities and review results are retained with the
[representation review PR](https://github.com/kbak/clafer-semantics/pull/39).

The original representation criteria are met by the delivered core and its
witnesses. The [formalization roadmap issue](https://github.com/kbak/clafer-semantics/issues/2)
retains the dependency and acceptance history. The
[self-description and telematics PR](https://github.com/kbak/clafer-semantics/pull/38)
establishes the bounded results described below; neither semantic
self-instantiation nor global pushout existence follows.

## Spans and indexed mappings

[Span.Basic](../DPGraph/Span/Basic.lean) keeps a link type and two endpoint
functions in independent universes. `Span.Iso` renames links while preserving
endpoints; inversion swaps the legs and is involutive, without supplying a
categorical inverse. [IndexedFamily](../DPGraph/Span/IndexedFamily.lean) uses
source-fiber indices and evaluation. Its sigma-head conversion and roundtrips
use equivalences across universes, not finite multisets or resizing.

[Composition](../DPGraph/Span/Composition.lean) retains every composable link
pair; family composition uses a dependent sum of indices. Units and associativity
are canonical span isomorphisms. [Relation](../DPGraph/Span/Relation.lean)
forgets link identity by existential endpoint membership. Joint endpoint
injectivity, fiberwise evaluation injectivity and isomorphism to the reduced
relation span characterize set-valuedness (B.1 Theorem 2).

The [span-composition correction](sources.md#span-composition-q1-research-for-4) states the exact
reduction/isomorphism criterion and sufficient hypotheses. The
[examples](../DPGraph/Span/Examples.lean) preserve two-path and parallel-link
counterexamples, empty heads and universe joins; the
[trace map](dpgraph-trace.md#span-representation) supplies the full proof inventory.

## Concrete predicates

[Predicates.Signature](../DPGraph/Predicates/Signature.lean) separates symbols
and real arity graphs from [Meaning](../DPGraph/Predicates/Meaning.lean).
Inverse has opposite arrows; commutation has a triangle; keys use a common source;
cover/disjointness use a common target. Family arities retain their center at
zero arity and permit repeated bindings. Generic `DPGraph` adds no set-valued default.

Inverse and triangle commutation compare spans up to link isomorphism; keys compare
source fibers as bags; cover and corrected disjointness inspect reachable values.
Inclusion fixes ambient object identity, and multiplicity bounds count links via
finite-type embeddings, with no finiteness requirement for an unbounded upper
limit. The [predicate contracts](sources.md#predicate-contracts-and-the-accepted-q8-correction)
record exact meanings, empty-family cases, invariance and the common-target disjointness correction.

[FunctionalKey](../DPGraph/Predicates/FunctionalKey.lean) derives the
[ordinary-key correspondence](spec.md#ordinary-key-correspondence-and-repeated-marriages)
under componentwise totality/single-valuedness. Its
[repeated-marriage witness](../DPGraph/Predicates/Examples/FunctionalKey.lean)
does not impose those hypotheses on general bag keys.
[Interpretation](../DPGraph/Predicates/Interpretation.lean) connects these meanings
to generic satisfaction and reduct. [Examples](../DPGraph/Predicates/Examples.lean)
and the [trace map](dpgraph-trace.md#typed-vocabulary-implementation) cover the
acceptance boundaries. VC belongs to the separate `FormalCD` extension; arbitrary
path equations beyond triangles and all-universes SetMap remain outside this slice.

## Shared semantic infrastructure

[Relational span laws](../DPGraph/Predicates/Relational.lean),
[ambient navigation](../DPGraph/Predicates/Navigation.lean) and the
[finite-range bridge](../DPGraph/Predicates/Finite.lean) belong to DPGraph.
They retain link identities and explicit functionality, inclusion and local
finiteness hypotheses. Clafer specializes them for parent/reference roles.
`Interpretation.isModel_iff_of_declarations_image` proves whole-model equivalence
only for exact translated declaration sets; `isModel_range_translate` specializes
it to banks, including collisions. The arbitrary-morphism reduct remains one-way.

[DPGraph gluing](../DPGraph/Gluing.lean) constructs used-referent graphs and
labels complete bindings using Quiv/Prefunctor. [FormalCD gluing](../FormalCD/Gluing.lean)
descends compatible metadata and proves validity under naming and complete-default
hypotheses. The Clafer adapter selects role endpoints, referents and origin metadata.
No generic graph/CD acquires Clafer root, ownership, group or declaration-disjointness
rules from these constructions.

## Formal class diagrams

[FormalCD.Basic](../FormalCD/Basic.lean) adds a shared `Registry`, class/map
names, predefined annotations and map modes to the authoritative DP declaration
set. `Raw` exposes data and invalid cases; `CD` bundles `Raw.WellFormed`.
Registry identifiers determine predefined identity/kind, independently of spelling.
Entries are optional; user names may repeat, and there is no global name-injectivity
or inheritance-acyclicity condition at this layer.

Declarations are effective: ordinary maps require setValued membership and
inclusions require inclusion membership. Bag mode adds no default, while authored
bag setValued declarations remain expressible. These syntactic obligations assert
neither satisfaction nor model existence; general primitive/object-diagram
semantics remain separate. Exact [source/default obligations](sources.md#formalcd-structure-and-selected-morphisms)
and [naming requirements](spec.md#formalcd-naming-and-predefined-identity) retain
these distinctions.

[Morphism](../FormalCD/Morphism.lean) specializes DP morphisms by preserving
names, optional registry identities and modes. Source/target CDs independently
satisfy well-formedness; carrier maps may identify user vertices/arrows and targets
may declare more. [Semantics](../FormalCD/Semantics.lean) applies the existing
reduct after forgetting metadata. The [structural](../FormalCD/Examples.lean) and
[semantic](../FormalCD/SemanticsExamples.lean) fixtures and
[trace map](formalcd-trace.md) record the laws and counterexamples.

## Figure 21c and compatible vocabularies

[FormalCD.Signature](../FormalCD/Signature.lean) defines `Vocabulary` through
a built-in symbol embedding and inverse arity Prefunctors. `extend` adds disjoint
symbols; embedding commutes with translation and interpretation restriction.
`RawOver`, `CDOver` and `HomOver` generalize the original built-in wrappers without
changing their metadata/default obligations. General vocabularies retain independent
universes; the disjoint extension uses small arities.

[The metamodel](../FormalCD/Metamodel/Basic.lean) uses this API with explicit
naming/arity subgraphs. The [source inventory](sources.md#figure-21c-metamodel)
owns nodes, arrows, declarations and inferred nd/ad attachments. Class, modeled
class and object identities stay separate; no node denotes all Lean types.

`Candidate` stores the symbol, every vertex image and indexed total-arrow images;
its endpoint-valid candidates are equivalent to `DPGraph.Formula`. `Context`
supplies embeddings/data, never validity. `ArityDiscipline` checks complete fiber
indexing, endpoints, argument values and selected symbols; `NameDiscipline` checks
names, registry identities/kinds and the predefined naming square. Their bounded
interpretations use the existing subset/span graph and independent syntax universes.

Full binding identity, literal bag-key satisfaction and total args are separate
obligations. The [projection witnesses](sources.md#literal-key-total-args-and-the-19-obligation)
explain why positional/isolated bindings and zero-arrow arities prevent a universal
realizability inference. Fragment satisfaction and whole-metamodel satisfaction
remain distinct; see the [named discipline proofs](formalcd-trace.md#discipline-correspondence-and-identity-laws).

[Integer.lean](../FormalCD/Integer.lean) owns the explicit integer encoding,
image domain and partial singleton extraction. Figure 21 VC and Clafer constraint
bindings share it. Its domain is mathematical Int; registry metadata still does
not impose primitive domains on arbitrary models.

## Bounded self-description and Figure 21b

[SelfDescription.lean](../FormalCD/SelfDescription.lean) reuses `Metamodel.diagram`
in the small `CDOver` family with the nd/ad vocabulary and SING registry.
`bounded_self_description` combines representation, well-formedness and the
inventory; `metamodelFormulaRepresentation` reuses `Candidate.formulaEquiv`.
It establishes syntactic self-description. The separate
[realization theorem](metamodel-realization.md) proves semantic self-instantiation
under the canonical bounded context, after checking support and bag separation.

[Telematics/Basic.lean](../FormalCD/Telematics/Basic.lean) supplies Figure 21b's
four nodes, five arrows and twelve effective declarations.
[VC.lean](../FormalCD/Telematics/VC.lean) adds a four-arrow predicate with an
explicit integer-domain embedding/decoder. Its meaning follows actual server,
inclusion and version links; `builtins_unchanged` preserves generic meanings.
Under inclusion and 1..1(version), `satisfies_vc_iff_guarded` gives the corrected
comparison; 0..1(server) is single-valued without totality, and 0..5(display)
bounds its inverse. [Source locators and the guarded version-comparison correction](sources.md#figure-21b-and-the-accepted-q7-correction)
retain the exact order, guard and drawn annotations.

[Examples.lean](../FormalCD/Telematics/Examples.lean) uses `Bool ⊕ Int`, all
integers and an optional server link with its inverse. `model_iff` characterizes
whole Figure 21b models: greater/equal versions pass, lower fails only VC, and
an unserved display passes. These are separate from Figure 21c fragments and
the bounded self-description result; the [trace map](formalcd-trace.md#figure-21b-satisfaction-and-counterexamples)
links the full witness inventory.

## Roadmap and validation accounting

`impl~formalization-roadmap-architecture~1`

The three layers below are implemented within their stated boundaries. Follow
these dependencies to understand how the results build on one another. Ticket
closure does not strengthen a theorem: the [proof-status table](#theorem-statements-and-proof-status)
states what is proved and what remains outside scope.

The [GitHub Project](https://github.com/users/kbak/projects/2),
[three phase milestones](https://github.com/kbak/clafer-semantics/milestones?state=all)
and [formalization roadmap issue](https://github.com/kbak/clafer-semantics/issues/2)
retain planning and acceptance history. The
[source-audit and roadmap PR](https://github.com/kbak/clafer-semantics/pull/40)
and [supporting-source assessment PR](https://github.com/kbak/clafer-semantics/pull/43)
record their documentation acceptance. The
[supporting-source research issue](https://github.com/kbak/clafer-semantics/issues/41)
retains the bounded assessment and conditions for further research.

Covers:
- `req~formalization-roadmap~1`

| Layer | Construction order (links to planning issues) | Delivered result and limit |
| --- | --- | --- |
| Reusable DP-graphs | [Graph representation](https://github.com/kbak/clafer-semantics/issues/13) → [typed declarations and maps](https://github.com/kbak/clafer-semantics/issues/14) → [category and model restriction](https://github.com/kbak/clafer-semantics/issues/15), with [split restriction laws](https://github.com/kbak/clafer-semantics/issues/28) and [conditional pushouts](https://github.com/kbak/clafer-semantics/issues/30). Separately, [link-preserving spans](https://github.com/kbak/clafer-semantics/issues/4) support [concrete predicate meanings](https://github.com/kbak/clafer-semantics/issues/16). | The [DPGraph proof inventory](dpgraph-trace.md) covers these results. The library remains independently importable; pushout and amalgamation results require a supplied carrier pushout. |
| Formal class diagrams | Concrete predicates → [CD structure and morphisms](https://github.com/kbak/clafer-semantics/issues/17) → [metamodel vocabulary and disciplines](https://github.com/kbak/clafer-semantics/issues/18) → [bounded self-description and telematics](https://github.com/kbak/clafer-semantics/issues/19). | The [FormalCD proof inventory](formalcd-trace.md) covers metadata, compatible vocabulary, Figure 21c and guarded Figure 21b models. The separate [restricted realization](metamodel-realization.md) proves a bounded semantic self-instance under its canonical context; syntactic self-description alone does not imply it. |
| Structural Clafer | [Resolved syntax and Shapes](https://github.com/kbak/clafer-semantics/issues/3) support [MCS disciplines](https://github.com/kbak/clafer-semantics/issues/20) and [typed constraints](https://github.com/kbak/clafer-semantics/issues/21), then [Compile](https://github.com/kbak/clafer-semantics/issues/22), [resolved-referent gluing](https://github.com/kbak/clafer-semantics/issues/23) and [representative integration](https://github.com/kbak/clafer-semantics/issues/24). | [Compile](compile.md) and gluing retain their input and default-completeness assumptions. [Representative models](representative-models.md) check structure, xor groups and version attachment. [Core denotation](constraint-denotation.md) and [selected preservation](constraint-preservation.md) connect typed bodies to predicate satisfaction; the [complete Appendix 6 model](telematics.md) supplies simultaneous satisfaction for one concrete model. Textual elaboration and unrestricted compiler correctness remain outside these results. |

### Nine architectural decision areas

The table records the main design choices, alternatives and supporting proofs.
It complements the [graph representation rationale](#dp-graph-representation-decision).
A1–A9 label the architectural areas in this table; the separate
[source questions](sources.md#question-dispositions-and-validation-tasks) record
corrections and interpretations of the paper.
Deferred alternatives need their own scope and validation before implementation.

| Area | Choice and alternatives | Evidence and remaining validation |
| --- | --- | --- |
| <a id="design-a1"></a>A1 — graph representation and Mathlib reuse | Use `Quiver`/`Prefunctor`/`Quiv`. Endpoint-indexed arrows retain loops and parallel arrows; a second vertex/edge record would duplicate the graph-map API. Carrier arrows need no categorical composition. | [Core examples](dpgraph-trace.md#example-proofs) check isolated vertices and noninjective maps. The [dependency-cost decision](#dependency-cost-decision) explains why the broader `Quiv` import is retained and when to reassess it. |
| <a id="design-a2"></a>A2 — signatures, arities and declarations | Use graph-valued arities, full dependent bindings and declaration sets. Untyped arrow lists lose incidence and isolated vertices; injective bindings lose repetitions. | [Translation proofs](dpgraph-trace.md#translation-proofs) and [binding-boundary examples](formalcd-trace.md#checked-discipline-and-projection-boundaries) establish the selected representation. The [supporting-source assessment](sources.md#generalized-sketches-and-model-reduct-coherence) compares dependency-enriched sketches; adopting them would need a separate scope and compatibility argument. |
| <a id="design-a3"></a>A3 — morphisms and categorical structure | Fix a signature and allow maps to identify elements and targets to add declarations, as in Definition 10. Embeddings or reflection would impose stronger conditions. `FormalCD` additionally preserves metadata. | [DPGraph category laws](dpgraph-trace.md#category-laws-and-extensionality) and [FormalCD morphism laws](formalcd-trace.md#morphism-laws-and-semantic-interoperability) support this choice. Model transport and pushout results retain explicit hypotheses. [Gluing](#mcs-gluing) separately proves declaration preservation and CD validity under complete defaults; it does not prove generic pushout existence or arbitrary-model reflection. |
| <a id="design-a4"></a>A4 — spans, identities and universes | Retain explicit links and pullback composition in independent universes. Relations discard multiplicity; a graph of all Lean types would need an additional size principle. | [Span roundtrips and composition](dpgraph-trace.md#span-representation) and the [corrected relational-reduction law](sources.md#span-composition-q1-research-for-4) preserve link identity. Concrete predicates count links and share ambient objects. MCS and gluing preserve these distinctions across role encodings. |
| <a id="design-a5"></a>A5 — predicate syntax and meaning | Separate symbols/arities from interpretations and model maps. Generic syntax imposes no set-valued default; `FormalCD` supplies effective defaults. Primitive domains and version comparison require explicit interpretations. | [Model restriction](dpgraph-trace.md#model-restriction-proofs) follows from precomposition. [Concrete predicates](#concrete-predicates) use [common-target disjointness (Q8)](sources.md#predicate-contracts-and-the-accepted-q8-correction); [telematics](#bounded-self-description-and-figure-21b) supplies guarded version comparison. [Core denotation](constraint-denotation.md) and [integer extraction](integer-extraction.md) supply expression meaning and partial scalar conversion separately from typing. |
| <a id="design-a6"></a>A6 — formal-CD metamodel and self-description | Reuse `CDOver` with an explicit vocabulary/registry, node/arrow discipline meanings and full-binding correspondence. Syntactic well-formedness does not imply semantic self-instantiation or a Lean universe fixpoint. | [Bounded self-description](formalcd-trace.md#bounded-syntactic-self-description-proof) and [Figure 21b witnesses](formalcd-trace.md#figure-21b-satisfaction-and-counterexamples) establish the selected results. Ordered and isolated bindings expose bag-key and argument-totality limits. The [restricted realization](metamodel-realization.md) supplies the support/separation hypotheses and an actual self-instance; universal realizability remains obstructed. |
| <a id="design-a7"></a>A7 — Clafer syntax, MCS and finiteness | Use a deep resolved AST and typed role graphs, with raw data and explicit well-formedness propositions. A shallow Lean encoding would obscure source syntax and compilation; global finiteness would restrict reusable DP-graph semantics. Finite data belongs at the executable boundary. | The [syntax source map](sources.md#resolved-2014-clafer-and-individual-shapes) covers Figures 16/22 and the top-level abstract correction. The [MCS inventory](mcs-invariants.md) records guarded Appendix 5 clauses and corrected ownership bounds; Shapes still enforce exact role presence. Nonempty examples and Compile's derived structural proofs validate the finite presentations. |
| <a id="design-a8"></a>A8 — names, generated identity, Compile and gluing | Keep role identities, resolved class/map referents and display names separate. Repeated parent/dref/isA strings do not identify arrows. Gluing identifies exactly equal resolved referents and retains the exact declaration image. | [MCS disciplines](mcs-invariants.md) state the equality used by cojoining and cover repeated names. [Compile](compile.md) establishes generated identities, freshness and termination. [Gluing](#mcs-gluing) proves incidence/declaration preservation under referent consistency, with a separate CD-validity proof under effective defaults. |
| <a id="design-a9"></a>A9 — constraints and end-to-end claims | Use resolved typed expressions with explicit inheritance widening and graph support. Typing and structural Compile/gluing correctness do not establish constraint preservation. The original Alloy translation informs the language's semantics; correspondence with the selected SoSyM meaning and a later compiler revision requires an explicit contract. | [Core typing](#resolved-syntax-and-individual-shapes) checks binders, navigation and types. [Representative coverage](representative-models.md) states supported examples and omissions. The [preservation bridge](constraint-preservation.md) combines [denotation](constraint-denotation.md), exact binding/label transport and [inherited realization](inherited-realization.md). Textual elaboration and unrestricted preservation remain outside this claim. See the [source comparison for stronger claims](sources.md#metamodel-realization-and-translational-semantics). |

### Theorem statements and proof status

The roadmap assessment adds no Lean theorem. The existing named
[DPGraph](dpgraph-trace.md), [FormalCD](formalcd-trace.md) and [Clafer](clafer-trace.md) proof artifacts
link to the actual declarations; the statements below bound what may be inferred.

| Statement | Status and scope |
| --- | --- |
| Translation preserves identity/composition; declaration-preserving maps form a fixed-signature category. | Proved in the [translation](dpgraph-trace.md#translation-proofs) and [morphism laws](dpgraph-trace.md#morphism-proofs), using `Formula.translate_id`, `translate_comp` and `Hom` laws; B.4 Definitions 6–10. |
| A model of T restricts to a model of S along F : S → T, contravariantly. | Proved as `Interpretation.isModel_reduct` and [`reduct` laws](dpgraph-trace.md#model-restriction-proofs); abstract B.5 Theorem 3. No whole-model reflection is claimed. |
| Restriction along F is injective if J.comp F = id T, and surjective if F.comp J = id S. | Derived and proved in [`ModelTransport`](../DPGraph/ModelTransport.lean), not verbatim paper theorems. |
| A supplied carrier pushout lifts to a DP pushout; its models correspond to compatible component models. | Derived and proved as [`Pushout.isColimit`/`modelEquiv`](dpgraph-trace.md#public-pushout-interfaces). The equivalence fixes semantic and carrier universes together; no global existence or concrete Clafer gluing theorem. |
| Span reduction commutes with composition; isomorphism to the relational composite requires injective composite endpoint pairing. | Proved [corrected span-reduction statement](sources.md#span-composition-q1-research-for-4), with counterexamples to the unqualified source assertion. |
| The metamodel has a bounded syntactic CD representation; guarded VC agrees with the selected integer comparison and the example models. | Proved as `bounded_self_description`, `satisfies_vc_iff_guarded` and [`Examples.model_iff`](formalcd-trace.md#figure-21b-satisfaction-and-counterexamples); preserve their vocabulary/registry, integer-domain, inclusion and version hypotheses. Those results are separate from the semantic self-instance below. |
| A well-formed resolved AST compiles to an MCS satisfying the explicitly enumerated invariants. | Derived by `Compile.compile`/`wellFormed` under `Compile.Input`, including canonical naming and positive constraint support. Finite traversal/lookup and owner-role identities establish termination and freshness; see [the contract](compile.md). |
| The role-label map is a DP morphism, and the glued structure is a well-formed formal CD. | Proved separately in `Gluing.labelHom` and `raw_wellFormed`: approved referent incidence/metadata consistency, with naming and effective-default completeness additionally required for CD validity. |
| Representative resolved models preserve structural relationships through compilation and gluing; generated xor distinguishes zero/one/two children. | Proved in `Examples.Integration`; `Examples.VersionCompilation` derives selected operand definedness from emitted local formulas plus integer-domain realization. [Coverage](representative-models.md) distinguishes structural attachment, definedness, predicate truth and whole-model satisfaction. |
| Selected resolved constraint truth corresponds to generated/glued predicate satisfaction. | `Compile.ConstraintMeaning.constraint_iff`, `compiled_model_iff`, `glued_constraint_iff` and `whole_model` use body-derived meanings, explicit external domains, primitive realization and selected canonical model candidates; see the [contract](constraint-preservation.md). |
| The finite structural checker accepts exactly the satisfying supplied candidates in its admitted fragment. | [`Verification.check_correct`](../Clafer/Verification/Finite.lean) assumes a well-formed supported effective core. [`run_correct`](../Clafer/Verification/ProtocolProofs.lean) connects the public protocol under checked core/fragment certificates, valid raw tables and typed decoding. This is neither configuration generation nor a fresh kernel proof of each native verdict; see the [checker contract](structural-checker.md). |
| The complete manually resolved Appendix 6 telematics model has a concrete satisfying compiled/glued interpretation. | [`Examples.Telematics.compiled_glued_model`](../Clafer/Examples/Telematics/Compiled.lean) discharges the selected whole-model hypotheses for all twelve bodies and final selections. Its integer extent is infinite; it does not use the finite checker or verify source-text elaboration. See the [complete model](telematics.md). |
| Compilation/gluing preserves every source-language constraint meaning. | Deferred beyond the selected bridge above. Generic formula satisfaction already commutes with graph translation; extending the source-language result requires explicit elaboration, interpretation and model-descent contracts. |
| Every well-formed CD has a faithful semantic encoding as an instance of Figure 21c. | Unrestricted inference is obstructed by the checked argument-bag and zero-arrow witnesses. `Realization.model_iff` proves the exact restricted contract: the canonical encoding is a model iff declared arrow support and symbol-plus-bag separation hold. An enriched metamodel still requires a separate design decision. |
| The particular Figure 21c metamodel semantically instantiates itself. | Proved as `Realization.Self.self_instantiation` under `context diagram`, with thirty formula objects, forty-six args links and exact reconstruction. This uses the existing DP model semantics, not general concrete primitive domains. |

The [realization contract](metamodel-realization.md) separates the implemented
syntax theorem from general source-language preservation. Its
[source comparison](sources.md#metamodel-realization-and-translational-semantics)
includes original Alloy encoding rules, pinned compiler context/constraint
handling and Diskin's generalized-sketch foundations. Predicate meanings remain
unchanged. `Encoding` builds the exact extents and spans; `Context` derives nd/ad;
`Correctness` proves all thirty obligations and the iff; `Reconstruction` decodes
full syntax plus explicit metadata; `Self` checks and realizes the particular
metamodel. The [proof index](formalcd-trace.md#restricted-realization-and-reconstruction-proofs)
links those results and the acceptance boundaries. No source satisfiability,
global-context or indexed/fibred equivalence follows from this reification.

The [source disposition](sources.md#project-critical-source-disposition) retains
missing-text audit limits and conditions for further acquisition. Closing the
bounded research tasks does not make unread material audited or prove the deferred
statements above. The [validation and review workflow](../CONTRIBUTING.md#setup-and-checks)
separates automated checks from semantic acceptance.

## Resolved syntax and individual Shapes

[Clafer.Syntax](../Clafer/Syntax.lean) uses mutually inductive `Tree`/`Forest`
containment with resolved `DeclId` edges for references/inheritance. `Origin`
distinguishes root, primitive domains and users; strings are repeatable metadata.
Containment supplies structural recursion/depth, inheritance uses a rank witness,
and reference/super IDs are never recursive children. The recursors and finite
lookup remain kernel-reducible; `noncomputable` suppresses compiler-generated
partial native helpers rather than introducing choice or termination axioms.
No native compiler executable or finite-carrier restriction on lower layers follows.

Authored/effective multiplicities and abstractness remain inspectable. `Defaults`
validates supplied data under the adopted
[child-default policy](sources.md#current-child-default-policy), including inherited
keyword provenance and explicit overrides; it does not elaborate defaults or realize primitive values.
The [syntax/source correspondence](sources.md#resolved-2014-clafer-and-individual-shapes)
records the supported forms, traversal measures and accepted parentless-head rule.

[Clafer.Context](../Clafer/Context.lean) separates the syntax boundary from typed
expressions: context, scope/domain occurrences and binder IDs/names survive without
deduplication. [Constraints.Typing](../Clafer/Constraints/Typing.lean) supplies
Boolean/integer terms and unary/binary collections with lexical positions,
endpoint-checked joins and explicit inheritance paths for widening.
[Constraints.Support](../Clafer/Constraints/Support.lean) gives finite occurrence
graphs retaining isolated/repeated identities, used as constraint arities by
Compile. The [typing requirement](spec.md#resolved-core-constraint-typing) and
[Appendix 4 notation decisions](sources.md#appendix-d-rule-dispositions-q3) distinguish this
interface from resolution, general evaluation and preservation. The
[integer-extraction extension](#integer-extraction-boundary) supplies its separate
partial primitive bridge.

[Clafer.Shape](../Clafer/Shape.lean) uses finite role subtypes with both endpoint
equations in arrow types. Kind and parent presence determine availability;
`Located.shape` decodes a local inventory, `Realization` binds it to a CD and
`Inclusions` supplies shared-role inclusions for a selected super.
[Local diagrams](../Clafer/Shape/Diagram.lean) add inverse, triangle, multiplicity,
default and set-reference-key declarations. [MCS](../Clafer/MCS/Basic.lean) supplies
global cojoining/naming; [gluing](#mcs-gluing) uses referents. Local CD validity
asserts no model. [Clafer trace](clafer-trace.md) links the complete proof inventory.

## MCS structural representation

[MCS/Basic.lean](../Clafer/MCS/Basic.lean) represents a resolved structural
family with Shape-presence guards. Shared class-role vertices and distinct ordinary/
inclusion slot occurrences make cojoining and ownership inspectable.
`Family.canonicalRoles` constructs cojoining from resolved edges; it is not the
AST compiler. `Family.WellFormed`/`Labels.WellFormed` enforce the
[Appendix 5 inventory](mcs-invariants.md), and `Model` bundles those proofs.

`Formulas` retains the owner and full graph binding of every formula, with separate
literal-key and total-args obligations. [MCS/Metamodel.lean](../Clafer/MCS/Metamodel.lean)
encodes Figure 23, explicit nd/ad context and the corrected source ownership bounds; exact source
clauses and their proof map belong to the inventory. [Examples](../Clafer/MCS/Examples.lean)
exercise nonempty families, primitive domains, repeated names and guarded inclusions.
Local formulas transport through `Roles.localDiagram`; [Compile](../Clafer/Compile/Basic.lean)
generates the local/constraint bank. No semantic self-instantiation follows.

## Finite structural verification boundary

The [compiler compatibility contract](resolved-ir-comparison.md) selects a
guarded structural fragment and an effective input boundary for the finite checker.
Whole-model semantics, representation and erasure bridges live under
`Clafer/Semantics/`; finite candidates and the verified executable checker live
under `Clafer/Verification/`. These remain in the single `clafer` package and
add no reverse dependency or finite-carrier condition to `DPGraph` or `FormalCD`.
[EffectiveCore](../Clafer/Semantics/EffectiveCore.lean) defines the data and guards
without importing Compile. [Compile/EffectiveCore](../Clafer/Compile/EffectiveCore.lean)
provides `erase` and its correspondence proofs. Core structural/constraint meanings
import neither Compile nor Verification; group semantics use the shared DPGraph
finite-range bridge without importing the checker. [Import tests](../tests/semantic_dependencies.lean)
and [group dependency tests](../tests/group_dependencies.lean) enforce these boundaries.
The reusable local bank is the existing structural Compile bank. Global root,
abstract-cover/disjointness, declaration disjointness and group obligations must
be stated and interpreted
in addition to that bank; local Shapes alone do not establish whole-model meaning.

Finite ordinary relation tables retain head objects as occurrence identities.
Derived reference-target spans retain composable links. Inheritance uses the same
ambient objects, and group counts use the union of child head fibers.
`Configuration.DeclarationDisjoint` independently requires super-edge comparability
for shared declaration membership. It is a satisfaction condition, with overlap
still available in raw candidates. Inherited field/context restrictions are not
fresh declarations. The same global condition accompanies normalization and the
compiled/glued whole-model correspondences; no generic subset/span restriction is
introduced.

The [structural checker guide](structural-checker.md) identifies the domain,
compiled-bank and arbitrary-span normalization bridges, protocol and proof APIs.
The theorem checks the executable algorithm against independent satisfaction;
an ordinary native invocation supplies a verdict, not a fresh kernel proof.
No per-instance proof-certificate or solver theorem is claimed.

The [resolved importer](resolved-import.md) lives in `Clafer/Verification/Import*.lean`.
Its fieldwise representation and normalization bridge reuse the effective core
and checker. External capture and strict protocol scripts live under
`scripts/verification/`; tests and fixtures live under `tests/`. Same-generation
receipts retain backend state omitted from JSON. No authored/default provenance
is reconstructed. The [bounded comparison harness](bounded-comparison.md) lives in
`scripts/verification/`, with regression sources and tests under `tests/`. Its
external candidate pin/decode relation, scoped SAT4J calls, enumeration and replay
reuse the importer and checker. It adds no solver imports to public Lean roots
and asserts no universal backend theorem. Full pinned validation
and independent semantic review apply to the importer and comparison relation.

## Structural Compile

[Compile/Structure.lean](../Clafer/Compile/Structure.lean) traverses resolved
entries in preorder, allocates class IDs and resolves finite edges.
[Binding.lean](../Clafer/Compile/Binding.lean) builds complete constraint bindings;
[Local.lean](../Clafer/Compile/Local.lean) generates Shape/inclusion declarations;
[Basic.lean](../Clafer/Compile/Basic.lean) combines banks and validity proofs.
[GroupSupport.lean](../Clafer/Compile/GroupSupport.lean),
[Groups.lean](../Clafer/Compile/Groups.lean) and
[GroupSemantics.lean](../Clafer/Compile/GroupSemantics.lean) add full inherited group
supports, a separate augmented declaration component, exact union gluing and
child-object counting correspondence. The old structural bank remains intact;
vertex-only groups do not claim its total-args discipline. See the
[group contract](group-compilation.md) for inherited bounds, empty inventories
and the checker/realization boundaries.
The [Compile contract](compile.md) owns exact input assumptions, identity/sharing
rules, formula generation and guarantees. It derives structural MCS validity,
with [representative gluing integration](representative-models.md). The separate
[constraint-preservation bridge](constraint-preservation.md) adds selected semantic
correspondence under explicit model assumptions.

## MCS gluing

[Gluing.lean](../Clafer/MCS/Gluing.lean) builds the graph of used class/map
referents. Representatives define endpoints/metadata, and `Incidence`/`Compatible`
make those choices independent of representatives. `classLabel_eq_iff` and
`labeledArrow_eq_iff` establish exactly referent equality as the identification
rule; different parallel-map referents remain distinct despite equal names/endpoints.

`labelHom` transports full formulas to their exact image. Translation retains
isolated vertices and repeated arguments, but may identify source formulas, so
the source bank's key does not imply injectivity of translated formulas.
`raw_wellFormed`/`cd` separately require naming and effective-default completeness;
[Origins.lean](../Clafer/MCS/Gluing/Origins.lean) derives naming from valid origins,
while `ofValid` still requires compatibility/defaults. No missing defaults are
silently added. The [gluing boundary](mcs-invariants.md#gluing-boundary),
[resolved-referent identity decision](sources.md#mcs-gluing-and-the-approved-q4-rule) and
[requirements](spec.md#mcs-gluing-identity-and-incidence) own the precise contract.

[Examples](../Clafer/MCS/Gluing/Examples.lean) and
[Boundaries](../Clafer/MCS/Gluing/Boundaries.lean) exercise merges, parallel maps,
formula collisions, defaults and full-binding transport; the
[trace map](clafer-trace.md#mcs-gluing-representation) gives exact declarations.
DP preservation, CD validity and model satisfaction are distinct. The
[representative integration](representative-models.md) establishes concrete
Compile/gluing obligations with the derived compatibility and default proofs.
Global pushout existence and general constraint-semantic preservation remain
separate obligations.

## Integer extraction boundary

[Constraints/Integer.lean](../Clafer/Constraints/Integer.lean) assigns the partial
meaning of `Expr.integerOf`: exact singleton equality with an encoded mathematical
integer. `Support.integer` marks the operand class; `Support.Resolved.integers`
checks its resolved primitive origin. `IntegerBinding` supplies the integer domain,
equal-ID correspondence and inheritance inclusions. Typing does not certify
runtime uniqueness. The operation returns `none` for invalid collections.

[IntegerNavigation.lean](../Clafer/Constraints/IntegerNavigation.lean) supplies
the selected Appendix 6 resolved fragment, typed comparison and conditional
operand-definedness theorem. Head and dereference maps remain distinct;
1..1 version/server heads and functional dereferences derive singleton images.
The accompanying examples evaluate the actual navigation and comparison for
arbitrary integer versions. This extension reuses the explicit Figure 21 integer
realization, while its VC predicate and guarded optional-server semantics remain
separate. The [conversion contract](integer-extraction.md) owns detailed limits;
the [core denotation](constraint-denotation.md) extends these equations to all
supported constructors and the c01–c12 inherited paths. The
[selected preservation bridge](constraint-preservation.md) connects those meanings
to Compile and gluing; the [complete fixture](telematics.md) discharges its assumptions for one selected configuration.

## Selected inherited realization

`Clafer.Semantics.Realization` retains AST authored flags alongside the effective
core and defines Appendix 6 contextual fields as subsets of existing owned
objects. `Clafer.Compile.Realization` preserves the [generated group bank](group-compilation.md) and adds explicit
abstract families and realized-field groups, with exact gluing and structural
correspondence. See the [source/combination contract](inherited-realization.md)
and [proof index](clafer-trace.md#selected-inherited-realization). The new modules
remain in Clafer; the [finite checker](structural-checker.md) retains its guarded
domain and the public layer order is unchanged.

## Independent constraint denotation

`Clafer/Constraints/Denotation.lean` interprets the resolved core over explicit
model bindings and lexical environments. Mathematical propositions, integers and
sets have partial meanings only where singleton conversion or finite cardinality
requires an obligation. Constructor laws, invariance and structural numeric
well-definedness live in adjacent modules. The [denotation contract](constraint-denotation.md)
explains local finiteness, span reduction, global abstract extents and the manual
Appendix 6 inventory. `Clafer/Examples/Telematics/*.lean` connects those expressions
to the delivered inherited structural carrier. The separate
[constraint preservation extension](constraint-preservation.md) composes them with
generated predicate meanings under explicit model assumptions. The guarded
structural checker remains unchanged.

<a id="complete-appendix-f-fixture"></a>

## Complete Appendix 6 fixture

The `Clafer.Examples.Telematics` full-model modules assemble the existing
resolved declarations and bodies, prove the input and generated banks valid,
and construct one configuration over finite nonprimitive objects plus all Int.
The primitive head has unrestricted bounds and root containment. Every printed
body and final selection is proved on the actual arity reduct of this same
configuration. The selected whole-model theorem then establishes satisfaction
of its canonical descent into the complete glued bank. The [full-model contract](telematics.md)
owns the attachment map, proof boundaries and rejection witnesses. It neither
extends the finite checker nor replaces the earlier subset fixtures.
