# Intent

## A maintainable foundation for formal semantics

`intent~formalization-foundation~1`

Develop a maintainable Lean 4 formalization grounded in the published SoSyM paper
(online 2014; journal issue 2016),
with reusable foundations supporting structural Clafer. The repository
`kbak/clafer-semantics` contains one Lake package, `clafer`, and sibling public roots
`DPGraph`, `FormalCD` and `Clafer`. Dependencies flow
`Clafer -> FormalCD -> DPGraph -> Mathlib`; `DPGraph` remains independently importable.
Reusable span/navigation laws and
referent graphs live in DPGraph; compatible metadata descent and explicit integer
realization live in FormalCD. Clafer supplies language-specific policies and
preservation bridges, retaining independent source meanings.

| Layer | Delivered scope | Boundary |
| --- | --- | --- |
| `DPGraph` | Link-preserving spans and indexed mappings (B.1–B.2), typed diagram predicates and their fixed-signature category (B.4), abstract model restriction (B.5), conditional model transport/pushout/amalgamation results, and selected Table 3/A.1 meanings over subsets and spans | Independent universes and shared object/link identities; no all-universes SetMap, inference closure or automatic set-valued defaults |
| `FormalCD` | Class diagrams with names, predefined identities, effective defaults and name-preserving morphisms; compatible signatures, Figure 21c naming/arity disciplines, restricted realization with exact reconstruction and bounded semantic self-instantiation; complete Figure 21b with twelve declarations and guarded integer VC models | Syntactic validity, fragment satisfaction and whole-model satisfaction are separate; no universal realizability or general primitive-domain realization |
| `Clafer` | Resolved syntax, typed constraint meanings, Shapes/MCS, structural Compile and gluing, selected preservation, and the complete telematics fixture | Resolved inputs and explicit model assumptions; no name resolution, default elaboration or unrestricted source-language preservation |

The [source edition and locator convention](sources.md#published-locators-and-legacy-aliases)
identifies the publisher e-offprint, its PDF pages and legacy subsection aliases.
The [paper companion](sosym-errata.md) explains the accepted corrections and
clarifications in reader-facing terms; the [source map](sources.md) retains their
exact locators, source identities and limits. These include link-preserving
composition, common-target disjointness, guarded version comparison, top-level
abstract heads and corrected ownership bounds. Full formula bindings, literal
bag keys and total arguments remain distinct. The selected language also adopts
[practical numeric-group child defaults](sources.md#current-child-default-policy)
so numeric choices can be optional without annotating every child. This is a
language evolution from Appendix 3, separate from the accepted paper corrections;
the historical SoSyM checkpoint preserves the original default convention.

Structural Compile derives MCS validity under its [resolved-input contract](compile.md).
Role identities, resolved referents and display names remain separate. Gluing
uses equal referents under incidence/metadata consistency, with complete effective
defaults required for `FormalCD` validity. The [group contract](group-compilation.md)
adds predicates over own and inherited child heads, including empty inventories;
the [inherited realization contract](inherited-realization.md) distinguishes
ordinary fields from explicit abstract types and restricts their shared maps.

The [constraint denotation](constraint-denotation.md) supplies independent core
meanings and explicit primitive/definedness obligations. The
[selected preservation bridge](constraint-preservation.md) connects these meanings
to generated/glued predicates under stated model assumptions. The
[complete telematics fixture](telematics.md) discharges those assumptions for one
concrete model with all twelve bodies and final selections. The
[representative models](representative-models.md) retain their narrower structural,
group and version-attachment claims.

The [finite structural checker](structural-checker.md) decides satisfaction for a
supplied candidate in the guarded [effective-core fragment](resolved-ir-comparison.md).
It distinguishes constraint violations from malformed or unsupported input.
Reference occurrences retain identity at repeated targets; declarations
incomparable through super edges have disjoint extents in satisfying models.
Overlapping raw candidates remain supported violations. This
[declaration-disjointness clarification](sources.md#declaration-disjointness-clarification)
leaves generic `DPGraph`/`FormalCD` subset/span models unrestricted.

The [pinned importer](resolved-import.md) preserves effective identities and bounds
without reconstructing authored/default provenance. The [bounded comparison
harness](bounded-comparison.md) tests exact supplied candidates against generated
static Alloy, with manual scopes, enumeration/seeded sampling and replayable
external evidence. It retains negative candidates and both discrepancy directions;
it supplies no universal compiler theorem.

The [roadmap and proof-status account](architecture.md#roadmap-and-validation-accounting)
records delivered results and deferred extensions. The bounded
[supporting-source assessment](sources.md#generalized-sketches-and-model-reduct-coherence)
leaves unread pages unaudited. Further acquisition is conditional on a named
necessary claim lacking adequate primary evidence, as stated in the
[source disposition](sources.md#project-critical-source-disposition). Stronger
representations or dependency-enriched signatures require separate authorization.

The [metamodel realization contract](metamodel-realization.md) gives a canonical
encoding that satisfies Figure 21c exactly when declared formulas have positive
arrow support and symbol-plus-argument bags separate their full bindings. The
encoding reconstructs the complete raw CD using explicit descriptor and mode
data. The particular metamodel meets both hypotheses and thus has a bounded,
context-dependent semantic self-instance. These results leave general
Compile/gluing preservation separate; the
[original Alloy translation, compiler and Diskin assessment](sources.md#metamodel-realization-and-translational-semantics)
retains their source differences and unresolved historical identities.

Exclude production instance generation, general Alloy/SMT/SAT integration,
production runtime configuration management, Claferize, post-2014 extensions beyond the adopted child-default policy,
a production parser and visualization. Keep the foundation reproducible and
reviewable. The brief README introduces Clafer, the formalization's purpose and
maturity, a build and checked example, and contribution routes. This document
owns the detailed scope; [requirements](spec.md) state the precise promises.
The [Lean walkthrough](getting-started.md) connects one small model to checked
statements and shows pinned downstream use; language examples remain at
[clafer.org](https://www.clafer.org/p/examples.html). Software citations identify
the source revision separately from the paper. Research snapshots follow
[independent review](maintenance.md#research-snapshots) and retain the research/API limits.

Needs: req

## Consistent work by people and agents

`intent~traceable-contributions~1`

Use IntentBond to maintain the relationship between intended outcomes,
requirements, implementation, and verification evidence as the project evolves.
Use GitHub issues and a Project for planning and tracking, including IntentMade
work, so work and outstanding semantic decisions remain visible.
Public contributors and agents can use issues and forks without private Project
access; maintainers reconcile Project membership and status.
Follow the [contribution instructions](../CONTRIBUTING.md) and
[documentation policy](../AGENTS.md#documentation).

Needs: req

## Documentation map

Use each document for its specific role; link to authoritative detail when
updating summaries. Keep conditions needed to understand a claim beside it.
Write for readers who have not followed the issue tracker: name each capability
and explain its current contract before linking to its history. Use descriptive
link text that identifies an issue or pull request when one is relevant; bare
numbers and ticket chains must not substitute for an explanation.

| Read or maintain | Purpose |
| --- | --- |
| This intent | Product goals, delivered scope and exclusions |
| [Getting started](getting-started.md) | One Lean model walkthrough and a pinned downstream Lake example; language learning links to clafer.org |
| [Requirements](spec.md) | Normative promises, acceptance obligations and stable OFT IDs |
| [Architecture](architecture.md) | Representation choices, module boundaries, roadmap and theorem status |
| [Source map](sources.md) | Paper correspondence, immutable source citations, decisions and audit limits |
| [Metamodel realization](metamodel-realization.md) | Exact restricted theorem, reconstruction, source-to-obligation comparison and bounded semantic self-instantiation |
| [Paper companion](sosym-errata.md) | Concise corrections and clarifications for SoSyM readers |
| [DPGraph](dpgraph-trace.md), [FormalCD](formalcd-trace.md) and [Clafer](clafer-trace.md) traces | Named implementation/proof artifacts and actual Lean declarations |
| [Constraint preservation](constraint-preservation.md) | Derived predicate meanings, exact binding/label transport and selected whole-model correspondence |
| [Constraint denotation](constraint-denotation.md) | Explicit environments, core equations and Appendix 6 elaboration |
| [Complete telematics model](telematics.md) | All twelve constraint bodies, final selections and concrete whole-model satisfaction |
| [Inherited realization](inherited-realization.md) | Authoritative declaration/constraint inventories, ordinary fields and explicit abstract families |
| [Group compilation](group-compilation.md) | Effective bounds, inherited child unions and augmented declarations |
| [Representative models](representative-models.md) | Checked integration, source/feature coverage and explicit Appendix 6 omissions |
| [Integer extraction](integer-extraction.md) | Primitive realization, partial extraction and Appendix 6 navigation assumptions |
| [MCS inventory](mcs-invariants.md) and [Compile contract](compile.md) | Detailed structural clauses and transformation assumptions |
| [IR comparison contract](resolved-ir-comparison.md) | Accepted comparison domain, compiler audit and external trust obligations |
| [Structural checker](structural-checker.md) | Finite candidates, independent satisfaction, protocol and correctness bridges |
| [Resolved import](resolved-import.md) | Pinned compiler capture, effective-core import and replay prerequisites |
| [Bounded comparison](bounded-comparison.md) | Exact candidate pins, Alloy search and discrepancy replay |
| [Contributing](../CONTRIBUTING.md), [trace convention](traceability.md) and [maintenance](maintenance.md) | Setup/checks, evidence links and repository administration |
| [Historical change records](https://github.com/kbak/clafer-semantics/tree/ee4c82835a67626b6eeb925033732e42b1c618c9/docs/changes) | Retained accepted scopes and plans at a revision preserving their relative link targets; not current architecture or status |

Internal labels identify [source questions Q1–Q9](sources.md#question-dispositions-and-validation-tasks),
[architectural choices A1–A9](architecture.md#nine-architectural-decision-areas), and
[compiler-comparison decisions D1–D8](resolved-ir-comparison.md#decisions-location-proposal-and-prerequisites).
These are project references, not paper section numbers. Explain a decision by
name and link to its definition when using its label outside the owning table.
Make each later reference clickable at the point of use, preferably to the
specific section or decision row rather than the top of a document.

Keep frozen change records unchanged until controller retention permits removal.
The historical link above reads the retained records in their original path
context. The local `changes/` copies retain historical filenames in references;
use the current map for maintained documents and the
[filename convention](../CONTRIBUTING.md#documentation-filenames) when adding or moving them.
Do not merge normative requirements with proof indexes or treat historical
proposals as current promises. Preserve artifact IDs, trace relationships, source
citations and existing link destinations when consolidating living prose.
