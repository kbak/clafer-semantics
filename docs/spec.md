# Foundation, DP-graph, FormalCD and Clafer requirements

These requirements state the repository's infrastructure and mathematical
obligations. The [canonical intent](intent.md) summarizes delivered scope and
links the focused contracts, including constraint denotation, finite structural
verification and the complete Appendix 6 model. The [documentation map](intent.md#documentation-map)
also defines the project decision labels used below. A research or planning
requirement alone does not authorize semantic implementation.

Browse requirements by topic:

- **Project:** [validation](#reproducible-lean-validation),
  [contribution workflow](#intentbond-on-every-contribution),
  [documentation](#focused-public-project-documentation) and
  [source research](#source-audit-and-three-layer-roadmap).
- **DPGraph:** [graphs and models](#graphs-signatures-and-typed-declarations),
  [spans](#link-preserving-spans-and-isomorphisms),
  [predicates](#bounded-semantic-graph) and
  [conditional pushouts](#declaration-unions-on-carrier-cocones).
- **FormalCD:** [structure](#formalcd-structure-and-semantic-boundary),
  [metamodel](#figure-21c-metamodel-shape),
  [realization](#faithful-restricted-metamodel-realization) and
  [Figure 21b](#complete-figure-21b-example).
- **Clafer structure:** [syntax and Shapes](#resolved-2014-clafer-syntax),
  [MCS](#mcs-metamodel-and-ownership),
  [Compile and groups](#structural-compile-input-contract),
  [gluing](#mcs-gluing-identity-and-incidence) and
  [inherited realization](#selected-inherited-field-and-explicit-abstract-realization).
- **Constraints:** [typing](#resolved-core-constraint-typing),
  [integer extraction](#integer-extraction-from-primitive-navigation),
  [denotation](#explicit-constraint-model-environments) and
  [preservation](#derived-source-constraint-predicate-meanings).
- **Finite verification:** [comparison contract](#resolved-ir-comparison-contract-and-compatibility-audit),
  [checker](#effective-structural-core-and-supported-fragment),
  [importer](#pinned-resolved-compiler-import) and
  [bounded comparison](#exact-bounded-candidate-comparison).
- **Worked models:** [walkthrough](#small-lean-model-walkthrough),
  [representative integration](#representative-compilation-and-gluing) and
  [complete telematics model](#complete-resolved-appendix-6-integration).
- **Shared foundations:** [span/navigation laws](#reusable-span-and-navigation-laws),
  [exact declaration images](#exact-declaration-image-semantics),
  [referent graphs](#reusable-referent-graph-construction),
  [metadata descent](#reusable-formalcd-metadata-descent) and
  [integer realization](#reusable-explicit-integer-realization).

## Reproducible Lean validation

`req~lean-validation~1`

The project pins Lean 4 and builds every module in the sibling `DPGraph`,
`FormalCD` and `Clafer` libraries of the single `clafer` Lake package. It treats
warnings as errors and rechecks every compiled project module with Lean's bundled
`leanchecker`, including examples and helpers not imported by the entrypoints.

Enforce `Clafer -> FormalCD -> DPGraph -> Mathlib`, including transitive imports
through helpers and roots; exercise `import DPGraph` and its public names without
the upper layers. Reject uncovered project modules and reverse dependencies,
testing rejection as well as the permitted graph.
The shared check command must fail if any
validation stage fails. This includes the DP-graph definitions, proofs and examples.

Run module discovery and its Python regressions before toolchain/dependency setup;
make that preflight available separately for development feedback. Report elapsed
time for build, kernel-check and test stages, identifying every kernel-checked
module in the output. CI streams the retained validation log while the check
runs and includes completed stage timings in its job summary, preserving the
IntentBond exit status even if log streaming fails. Batch module builds and
deduplicate overlapping kernel-check targets while retaining the complete
discovered inventory. Preflight success does not satisfy
the full validation requirement for Lean, build, validation or other executable changes.

After building, run the declaration/axiom audit and Lean/Python regression tests
before the more expensive kernel replay. Any failed gate stops later stages;
successful full validation still requires the complete kernel check.

Local and CI validation may instead run source-inventory preflight, its Python
regressions, document filename/link checks and validation-selection regressions when a
complete file-content and mode comparison with a frozen Git baseline proves that
only `README.md` or Markdown beneath `docs/` changed. Include additions, deletions
and nonignored untracked source. Only regular, nonexecutable Markdown qualifies;
other changed paths or modes, an unavailable baseline, an empty diff or uncertain
classification require full validation. Validation scripts, workflows, dependencies,
agent instructions and `scope.json` therefore require the full check.

Prepare the selection outside captured source and recheck its complete candidate
manifest inside the IntentBond snapshot before taking the documentation path.
A missing, malformed or stale selection falls back to full validation. CI selects
before provisioning Lean, the Haskell exporter or Alloy. Keep an explicit full-check
option and preserve the baseline identity, source manifests, selection reason and
actual check in evidence. Documentation validation does not claim new Lean validation:
IntentBond tracing, source matching and independent read-only semantic review
remain required, including review of changed mathematical claims and requirements.

CI may reuse unchanged compiled project modules through Lake's native artifact
cache, keyed by source contents, compiler options and transitive import traces.
Changed inputs must rebuild affected modules and their dependents; invalid source
must fail even when an earlier valid build is cached. The project inherits the
validation environment's cache setting, allowing `LAKE_ARTIFACT_CACHE=false` to
force fresh compilation in isolated snapshots. The shared check defaults caching
to disabled outside an explicitly enabled environment. Restore all artifacts to
the snapshot build paths before running the complete fresh kernel replay, axiom
audit and regression gates; cache hits never substitute for these checks.

CI and deployment-managed caches may also reuse pinned dependency artifacts.
Derive the optional Mathlib prefetch from imports in every discovered project
module and Lean test, including unimported helpers/examples and the pushout-cocone
dependency. Fetch their transitive dependencies through Mathlib's cache; an empty
inventory must not trigger a whole-Mathlib download. Cache failure must retain
the complete pinned source-build fallback.

CI persists native Lake dependency
and project artifacts and Mathlib downloads outside captured source, passing
their paths into the isolated check. Separate caches by OS, architecture, toolchain and dependency
manifest; save populated caches after successful validation and permit later
commits with the same dependency identity to reuse them. Always invoke the full
discovered module build so Lake validates every module's inputs before reuse;
never substitute an unchecked copy of a prior checkout's build directory.

Audit declarations by their originating project modules, including private and
generated declarations regardless of namespace, with complete `import all`
coverage. Reject unsafe/partial definitions, new axioms and transitive axiom
dependencies outside `propext`, `Classical.choice` and `Quot.sound`; report these
standard axioms separately. Reject an empty audit or one missing actual `DPGraph`
declarations. Zero declarations in a future root only indicate scaffolding.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, itest

## IntentBond on every contribution

`req~intentbond-workflow~1`

Agent instructions require the pinned IntentBond development skill. The repository
maintains intent and requirements with OFT links and a nonempty scope. CI checks
pull requests using the base branch's scope and retains evidence; first adoption
explicitly checks the candidate baseline and requires review. Exit 4 retains
semantic review as pending. Failed checks block the CI job.
The explicitly approved public-root migration expands only baseline `inputs`
and `review_paths` to `["."]`, preserving every other policy field and the actual
baseline commit. CI recognizes the exact original and migrated scope identities,
derives the expansion from the baseline and rejects arbitrary candidate policy
changes. Retain both identities and the transformation for independent review.

Covers:
- `intent~traceable-contributions~1`

Needs: impl

## GitHub planning and tracking

`req~github-tracking~1`

Agents plan work as public GitHub issues, tracked by maintainers in the configured
private Project. Contributors and agents without Project access use public issues
and forks. The helper's explicit `--no-project` option creates or closes only the
public issue, leaving Project reconciliation to a maintainer; it must make no
Project calls and must still fail on a public-operation error. The default mode
retains Project tracking and failure reporting. The ticket helper
creates issues from body files, adds them to the Project, sets their status, and
supports later edits, comments, and closure. GitHub operation failures must be
reported as failures; if issue creation succeeds before Project tracking fails,
the helper reports the created URL so tracking can be retried without recreation.
Planning tickets do not authorize starting semantic implementation.

Covers:
- `intent~traceable-contributions~1`

Needs: impl, utest

## Focused public project documentation

`req~public-foundation~1`

The repository keeps its MIT license and provides contribution and
private security-reporting guidance, issue/PR templates, a brief README, and links
to the SoSyM publication, free preprint, and maintained Haskell implementation.

The README explains Clafer and the formalization's purpose for new readers,
states the established results and their limits, and provides clone/build
instructions, a command for checking an existing example, and clear routes to
documentation, contribution guidance, issue tracking and security reporting.
Link the first mention of Lean to its [official site](https://lean-lang.org/).
Keep detailed mathematical inventories in the canonical documentation rather
than requiring familiarity with paper section numbers at the entry point.

Keep onboarding concise and link to clafer.org for language examples. Document
cache-assisted pinned setup, distinguish a Lean build from full validation and
state the latter's platform/prerequisite limits. Provide a minimal downstream
Lake example with an immutable published commit and matching toolchain, and
software citation metadata distinct from the source paper. Do not invent a
software DOI, release date or stable-API promise. A research snapshot is tagged
only after validation and independent semantic review of the selected commit;
keep its review disposition and evidence outside living documentation.

It distinguishes repository `kbak/clafer-semantics` from its single Lake package
`clafer`, with sibling public `DPGraph`, `FormalCD` and `Clafer` roots and the
dependency direction above. It distinguishes the delivered B.1 Definitions 1–5,
Theorems 1–2 and B.2.1–2 span operations (with the adopted [Q1](sources.md#span-composition-q1-research-for-4) reduction law),
B.4 Definitions 6–10 foundation, abstract B.5 model reduct and selected
Table 3/A.1 predicates (including the [common-target disjointness correction (Q8)](sources.md#predicate-contracts-and-the-accepted-q8-correction)) over a bounded semantic
graph, and the first `FormalCD` structure/name-preserving morphisms, from future
predicates, all-universes SetMap, universal realizability and the remaining
Clafer interpretation/integration increments.

It documents the delivered resolved
AST, typed core constraints, constraint boundary, individual Shapes, MCS
structural discipline, structural Compile and resolved-referent gluing.

It keeps private deployment configuration and credentials outside the source repository. Keep
[intent](intent.md) as the canonical overview, linking current architecture,
mathematical explanations, source citations, requirements and trace artifacts.

Use its documentation map to identify the authoritative location for each kind
of detail. Consolidate repeated explanations through links while retaining intent
and artifact IDs, trace relationships, source citations and existing link
destinations. Explain internal decision labels by name and link to their defining
table; readers must not need issue history to understand a correction or contract.
Name capabilities, dependencies and proof limits in the prose. Link to the current
contract or proof inventory for technical detail. Historical references must use
descriptive link text identifying the issue or pull request; do not use bare
numbers, number-only links or chains of tickets as explanations. Internal decision
references must link at each point of use to the relevant explanation or table
row, even when an earlier paragraph has already introduced the label.

Maintain the [documentation filename convention](../CONTRIBUTING.md#documentation-filenames)
and check maintained topic filenames during documentation validation. Document
moves update maintained references while preserving heading anchors and
commit-pinned citations. Read frozen records at their linked historical revision
to resolve relative links to former paths.

Keep frozen change records unchanged under their retention policy.
Follow the [documentation policy](../AGENTS.md#documentation): change comparisons
belong in PR descriptions and acceptance/execution evidence in external factory
artifacts. Retain controller-required historical snapshots and a concise current
plan until the retention policy permits removal.

Covers:
- `intent~formalization-foundation~1`

Needs: impl

## Small Lean model walkthrough

`req~lean-walkthrough~1`

Provide one manually resolved phone/optional-camera model within the existing
effective-core fragment. Explain its declaration IDs, object identities,
containment and 0..1 camera bound. Kernel-checked witnesses accept zero and one
camera and reject two. Discharge input validity and supported-fragment conditions,
and derive semantic satisfaction/non-satisfaction through the existing checker
correctness theorem. The walkthrough must distinguish manual source elaboration,
native evaluation and kernel-checked proofs; it adds neither parser correctness
nor configuration generation. Use SoSyM §5.3–5.5 and §6.2.2–5 through the existing
effective-core contract, with links to the detailed checker and telematics results.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## SoSyM reader companion

`req~sosym-reader-companion~1`

Maintain [corrections and clarifications](sosym-errata.md) as a concise companion
for readers of the hash-pinned publisher e-offprint. Give exact section,
figure, table or definition locators and one-based PDF pages including its two
cover sheets. Use published Appendix 1–6 numbering; retain explicit mappings for
legacy subsection aliases and source-to-code correspondences; preserve existing
heading anchors and update maintained links when modules move. Explain each
corrected reading and its reason, linking the accepted decision or source analysis
and relevant delivered proof/implementation evidence.

Cover the accepted composition, common-target disjointness, guarded version
constraint, top-level abstract-head and seven-association ownership corrections.
Clarify link/bag multiplicity, full formula bindings versus literal key and total
args, bounded self-description, guarded Appendix 5 clauses, gluing identity and
defaults, and Appendix 4 notation. Distinguish accepted corrections, clarifications,
explicit formalization choices and unresolved proposals. Do not present these as
publisher-issued errata or add new semantic claims. Link the companion from the
README, canonical intent and source map. Review its claims against paper passages,
issue decisions, merged history and the actual referenced Lean declarations.

Covers:
- `intent~formalization-foundation~1`

Needs: impl

## Source audit and three-layer roadmap

`req~formalization-roadmap~1`

Maintain the three reusable layers and explicit exclusions in [intent](intent.md),
the source-to-construct mapping in the [source map](sources.md), and representation
alternatives, dependencies and validation tasks in [architecture](architecture.md).
SoSyM is the primary semantic authority; identify exact sections/definitions/figures,
the inspected publisher e-offprint hash, edition/page convention and Mathlib commit.
Retain the preprint identity for historical provenance and free access.
Compare edition differences before changing a source-based semantic claim; do not
rewrite frozen records or versioned comparison manifests as if they used a later
source. Distinguish inspected full texts
and recovered-page subsets from abstracts, snippets and unavailable sources.
Record disagreements before selecting meanings; the compiler is supplementary
context and any use as evidence requires an immutable revision and a license check.

Acceptance of the [formalization roadmap issue](https://github.com/kbak/clafer-semantics/issues/2)
requires all of the following:

- Three phase milestones and a dependency-ordered backlog in the existing Project,
  linked from the maintained architecture.
- A source map with exact locators and the Mathlib pin, without compiler-driven semantics.
- A cross-check of all nine architectural decision areas, with alternatives,
  delivered evidence and explicit remaining validation tasks assigned to live issues.
- Honest available-source audit limits and dispositions of source disagreements,
  including gaps in 2003/2000 source coverage; recording a limit does not
  complete the missing-source research.
- PR review of maintained documentation, this scoped requirement and trace links.
  Research progress alone is not acceptance. Close the roadmap issue only after
  its deliverables are accepted and the implementing PR is merged; preserve
  its earlier discussion.

Distinguish proposed, proved and deferred theorem statements. This research
requirement adds no Lean theorem or mathematical implementation obligation;
later semantic increments require their own authorized scope. The existing
validation, IntentBond and GitHub-tracking requirements continue to apply.
Project-critical source research and the conditional sketch-extension assessment
have a separate [supporting-source assessment issue](https://github.com/kbak/clafer-semantics/issues/41).

Covers:
- `intent~formalization-foundation~1`
- `intent~traceable-contributions~1`

Needs: impl

## Resolved-IR comparison contract and compatibility audit

`req~resolved-ir-comparison-contract~1`

Maintain the documentation and source analysis specified in the
[compiler compatibility audit issue](https://github.com/kbak/clafer-semantics/issues/49), under
the [bounded semantic comparison project issue](https://github.com/kbak/clafer-semantics/issues/48), in
[the comparison contract](resolved-ir-comparison.md). Use SoSyM as the primary
semantic reference and pin the supplementary compiler to
`15adb2216909421bcb5022174d2d84ef2b42307c` for the original audit. Maintain the current
[0.5.4 comparison assessment](resolved-ir-comparison.md#compiler-054-compatibility)
separately, preserving immutable historical citations. Distinguish current Lean declarations,
proposed interfaces and unresolved source/version differences. This requirement
authorizes a specification and audit, not an executable comparison implementation
or a change to the current intent exclusions.

Acceptance requires:

- A cross-checked compatibility matrix with exact paper/compiler/Lean locators,
  proposed-supported, excluded and decision-pending forms/flags, including
  top-level abstract roles, inheritance, set/bag keys and multiplicity counts.
- A smallest useful structural fragment covering nesting, effective clafer/group
  bounds, abstractness, single inheritance and direct class-target set/bag
  references, with combination guards and a complete rejected-form/modifier
  inventory. Exclude user expressions, primitive values, temporal features,
  goals, backend escapes and reference-target expressions.
- A hashed same-IR/options JSON/Alloy boundary covering IDs, implicit registry,
  supers/bindings, unbounded limits, reference mode, keyword and global-card
  metadata, duplicate/dangling-ID rejection and backend state missing from JSON.
  Specify constrained options and any minimal additional export needed.
- An explicit disposition of lost authored/default provenance: an effective-core
  boundary with a justified, proposed semantics-preserving bridge, or a faithful
  minimal export. Invent neither provenance nor defaults/name-resolution proofs.
- Finite candidate object/link identity, exact same-candidate pinning/decoding,
  inheritance/root/unused-atom/renaming/auxiliary conventions, manual scopes,
  cardinality bitwidth/overflow conditions, pinned solver/options and an artifact
  schema. Keep scope-inference and optimization correctness outside the claim.
- Visible malformed, unsupported, unknown, timeout and error outcomes; proposed
  bounded soundness/reverse-comparison properties distinguishing random search,
  finite exhaustive checking and universal proof; positive and negative examples.
- A precise proposed companion-harness or separately bounded in-project location,
  with requirements/architecture amendments reviewed before implementation.
  Preserve policy and dependency layers during this planning increment.
- Whole-model interpretation and finite-checker bridge obligations explicitly
  allocated to the [structural-semantics issue](https://github.com/kbak/clafer-semantics/issues/50). Record a
  reviewed structural dependency disposition before any constraint-free shortcut;
  [Core typing](#resolved-core-constraint-typing), [structural Compile](compile.md)
  and [gluing](architecture.md#mcs-gluing) alone do not suffice. Preserve existing
  roadmap dependencies until that review, without requiring unrelated deferred
  language features to be completed first.
- Explicit source-decision records and review of the contract/matrix and
  documentation PR. Close the compatibility-audit issue only after review and
  acceptance/merge; automated
  validation or a proposed interface does not establish semantic implementation.

Keep the existing requirements `req~clafer-resolved-syntax~1`,
plus `req~clafer-input-wellformedness~1` and `req~clafer-individual-shapes~1`,
unchanged by this audit. Future executable
promises need separately reviewed implementing requirements. Existing source
audit, public documentation, tracking and IntentBond obligations remain in force.

Covers:
- `intent~formalization-foundation~1`
- `intent~traceable-contributions~1`

Needs: impl

## Supporting-source and coherence research

`req~supporting-source-research~1`

Maintain the bounded assessment authorized by the
[supporting-source assessment issue](https://github.com/kbak/clafer-semantics/issues/41), with SoSyM B.4 Definitions
7–10 and B.5 Theorem 3 as the semantic reference. Compare the inspected Diskin
& Wolter §4.1–3 signature dependencies, declaration closure, typed-instance
satisfaction and pullback coherence with the actual `Signature`, `Interpretation`
and reduct laws. Distinguish precomposition equalities from coherent
isomorphisms for chosen pullback reducts; assert no unproved equivalence of the
model representations and add no semantic or dependency change through this audit.

Record exact inspected statements, source/version identities and the limits of
browser excerpts, recovered-page subsets and acquired complete files. For partial
collections, record file/page hashes, page gaps and which claims are supported;
do not treat recovered passages as uninspected or missing passages as audited.

Bound acquisition by the claims required for an active increment. Use accessible
primary alternatives when they establish the exact needed statement, recording
its applicability limits. The unread 2003 keyed-sketch material and missing 2000
universal-arrow pages remain explicit audit limits; further acquisition is
deferred unless a named necessary claim lacks adequate primary evidence.

Review this disposition together with the [supporting-source assessment](sources.md#project-critical-source-disposition). Record hashes and locators for acquired
files, and retain failed-route evidence outside living documentation. Abstracts,
snippets and indexed PDF results do not establish a technical audit.
Assess accessible alternative Diskin sources by their exact statements and
applicability limits, without treating them as the missing full texts or as an
implicit choice of Clafer label identity.

Bound the Lean-library search by queries, inspected source trees and immutable
candidate revisions. Distinguish relevant foundations from a ready-made sketch
package, and static inspection from compatibility verified by building. Preserve
the adopted pins and separately review any future extension, adapter and license.
Keep source limits, architecture, canonical intent and trace links consistent.

Compare ordinary graph arities, marker-bearing arities and dependency-category
signatures; state the extra closure, preservation and semantic-consistency
obligations without importing them into the delivered API. Check proposed
dependencies against the actual bag-sensitive key and existing counterexamples.
This documentation requirement adds no Lean proof obligation. Acceptance requires
the bounded assessment and a reviewed disposition of remaining necessary claims;
a missing paper alone does not block an independently justified increment.

For the [metamodel realization investigation](https://github.com/kbak/clafer-semantics/issues/100),
distinguish the original Alloy translational semantics, the selected SoSyM
mathematics, versioned compiler behavior and generalized-sketch theory. State
which encoding, context, identity and satisfaction obligations each source
supports; record historical-version gaps and disagreements. Keep restricted
realization, particular self-instantiation and unrestricted compiler correctness
separate. Proposed theorem hypotheses and metamodel changes remain explicit
proposals until reviewed; this assessment does not alter the existing key,
argument-totality, universe or model-reduct contracts.
Maintain the [realization contract](metamodel-realization.md) with exact
encoded extents, external descriptor/metadata fields, source-only admissibility,
reconstruction and an exhaustive effective-declaration obligation table. Assess
the particular metamodel's declared formulas rather than imposing restrictions
on every symbol in its vocabulary. Record which conclusions are static source
assessments and which still need kernel-checked lemmas. Historical compiler
snapshots need their own license/version identity; generated examples and static
code observations must not be reported as executed compiler comparisons.
The separate realization requirements below own the authorized implementation
and proofs; this research requirement remains an assessment obligation.

Covers:
- `intent~formalization-foundation~1`
- `intent~traceable-contributions~1`

Needs: impl

## Graphs, signatures and typed declarations

`req~dpgraph-core~1`

Implement SoSyM Appendix B.4, Definitions 6–9, using Mathlib `Quiver`,
`Prefunctor` and bundled `CategoryTheory.Quiv`, with explicit independent symbol,
arity vertex/arrow and carrier vertex/arrow universe parameters. Pin Mathlib to
56a005855ea17e0b0958f73ec801ae140b0a1679 and preserve Lean v4.35.0. A signature
maps symbols to arity graphs; a formula pairs a symbol with a graph morphism from
its arity to the carrier; a DP-graph has a carrier and a `Set` of typed formulas.
Retain repeated arguments and isolated arity vertices. Do not impose categorical
structure on carrier arrows, global finiteness, decidable equality or dependency
closure. Explain the total-edge/dependent-sum correspondence. Provide the
independently importable `DPGraph` with no `FormalCD`/`Clafer` dependencies.

Covers:
- `intent~formalization-foundation~1`

Needs: impl

## Formula translation laws

`req~formula-translation~1`

For a fixed signature, translate a formula by postcomposing its arity-to-carrier
map with a graph morphism (SoSyM B.4, Definition 10). Prove translation preserves
identity and composition for arbitrary well-typed formulas and graph maps.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Declaration-preserving morphisms

`req~dpgraph-morphisms~1`

A DP morphism is a graph morphism with a proof that translation maps every
source declaration to a target declaration (SoSyM B.4, Definition 10).
For a fixed signature, provide identity and composition, prove their declaration
preservation, associativity and both unit laws, and provide extensionality from
the underlying graph map and its vertex/arrow actions. Reuse `Prefunctor` laws.
There is no injectivity requirement and no inference-closure condition.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Finite witnesses and failed preservation

`req~dpgraph-examples~1`

Construct a finite arity with two distinct parallel arrows and an isolated vertex,
a nonempty source declaration set and an explicitly described target declaration.
Give a nonidentity DP morphism identifying those arrows; prove distinctness,
equal images and declaration preservation. Apply the translation-composition
theorem to explicit composable maps. Exercise the isolated vertex's binding.

Provide a graph map to a carrier whose required declaration is absent and prove
that it cannot be equipped with a DP preservation proof. All these examples must
compile independently of `FormalCD`/`Clafer`. Their syntax-only predicate names carry
no unproved meaning; they do not implement SetMap or Theorem 3. Finiteness is
local to these examples, not a restriction on the core.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Fixed-signature category

`req~dpgraph-category~1`

For each signature and fixed carrier vertex/arrow universes, provide a Mathlib
`Category` instance on DP-graphs using exactly the existing `Hom`, identity and
composition from B.4 Definitions 9–10. Reuse their associativity, unit laws and
extensionality. Keep carrier arrows as arbitrary quiver arrows; the category
structure concerns maps between DP-graphs. Expose it through `import DPGraph`.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Abstract interpretation and satisfaction

`req~dpgraph-interpretation~1`

An interpretation for a fixed signature and semantic graph assigns each symbol
a set of graph maps from its arity to that semantic graph. Derive satisfaction
of a formula under a carrier-to-semantic-graph map by composing the formula's
binding with that map and testing membership in the symbol's meaning. Derive
the model predicate by requiring every declaration to be satisfied.
Prove the satisfaction condition under translation: for any graph map `F : G → H`,
formula `φ` on `G` and map `m : H → Ω`, satisfaction of `translate φ F` by `m`
is equivalent to satisfaction of `φ` by `F ; m`.

Keep semantic vertex and arrow universes independent of signature and carrier
universes. This abstract interface does not select concrete span predicate
interpretations. No all-universes SetMap object, resizing axioms, solver or
executable instance generation are included.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Contravariant model reduct

`req~dpgraph-model-reduct~1`

For a fixed interpretation, a declaration-preserving DP morphism `F : S → T`
and a `T`-model `m`, prove that precomposition `F ; m` is an `S`-model, the
abstract form of SoSyM B.5 Theorem 3. Provide restriction on models retaining
their underlying maps, and prove identity and composition laws:
`reduct (id S) m = m` and `reduct (F ; J) m = reduct F (reduct J m)`.

State the exact assumptions: a semantic graph, meanings on arity diagrams,
declaration preservation by `F`, and satisfaction of the target declarations.
No additional closure/invariance properties of meanings are assumed. Do not
claim reflection of whole-model satisfaction or preservation by arbitrary graph
maps, nor concrete SetMap semantics before those interpretations are supplied.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Model reduct injectivity

`req~model-reduct-injective~1`

For any `I : Interpretation σ Ω`, `F : Hom S T` and `J : Hom T S`, prove
`Function.Injective (I.reduct F)` from `J.comp F = Hom.id T`, with independent
signature, source/target carrier and semantic universes. Expose
`Interpretation.reduct_injective_of_comp_eq_id` through `import DPGraph`.
This is a derived library consequence of the existing reduct laws, grounded in
SoSyM B.4 Definitions 9–10 and the abstract B.5 Theorem 3, not a verbatim paper
theorem or concrete Clafer/span semantics. Require no finiteness, decidable
equality, interpretation invariance or injectivity assumptions, and assert no
whole-model reflection for arbitrary DP morphisms.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Model reduct surjectivity

`req~model-reduct-surjective~1`

For any `I : Interpretation σ Ω`, `F : Hom S T` and `J : Hom T S`, prove
`Function.Surjective (I.reduct F)` from `F.comp J = Hom.id S`, with independent
signature, source/target carrier and semantic universes. Expose
`Interpretation.reduct_surjective_of_comp_eq_id` through `import DPGraph`.
This is a derived library consequence of the existing reduct laws, grounded in
SoSyM B.4 Definitions 9–10 and the abstract B.5 Theorem 3, not a verbatim paper
theorem or concrete Clafer/span semantics. Require no finiteness, decidable
equality, interpretation invariance or injectivity assumptions, and assert no
whole-model reflection for arbitrary DP morphisms.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Interpreted witnesses

`req~dpgraph-semantics-examples~1`

Exercise a nonempty signature and declaration set with an explicit predicate
meaning that has both satisfying and failing diagrams. Construct a target model
and its reduct along a nonidentity DP morphism; exercise reduct identity and
composition through category notation. Exhibit the failure of restriction by a
bare graph map and the failure of whole-model reflection. Include an example
with semantic vertex and arrow universes larger than the syntax universes.
Example meanings are illustrative and do not claim the paper's concrete span
predicates. Keep all assertions kernel checked.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Link-preserving spans and isomorphisms

`req~span-representation~1`

Implement SoSyM B.1 Definitions 1–5 within `DPGraph`: a span from `A : Type u`
to `B : Type v` has a head `L : Type w` and total source/target functions.
The three universes are independent; distinct links may have equal endpoints.
An isomorphism is a head equivalence commuting with both legs, including across
head universes. Supply identity, symmetry and transitivity operations.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Span and indexed-family correspondence

`req~span-family-correspondence~1`

Represent indexed mappings by `I : A → Type w` and evaluation `∀ a, I a → B`.
Equivalence is fiberwise index equivalence preserving evaluation. Convert spans
to source fibers and families to heads `Σ a, I a`, in `Type (max u w)`.
Prove both roundtrips up to their respective equivalences, permitting the raised
head/index universes. Establish B.1 Theorem 1 through endpoint-membership equality:
span reduction is existence of a link with the given endpoints, and family
reduction is existence of an index evaluating to the target. Neither representation
requires finite indices or decidable equality.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Set-valued spans and relation reduction

`req~span-set-valuedness~1`

For SoSyM B.1 Theorem 2, a relation span has head
`{p : A × B // R p.1 p.2}` in `Type (max u v)`. Prove joint endpoint injectivity
iff every source fiber's target evaluation is injective, and iff a span is
isomorphic to the relation span of its existential reduction. Supply the
relation roundtrip by endpoint membership, preserving empty relations/fibers.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Pullback span composition and laws

`req~span-composition~1`

Implement SoSyM B.2.1 source-to-target composition with head
`{p : Lq × Lr // tq p.1 = sr p.2}`, in the join of the link universes.
Preserve every composable link pair. Prove compatibility with indexed-family
composition, whose indices at `a` are `Σ i : I a, J (f a i)`.
The identity has head `A` and identity legs. Supply endpoint-preserving left/right
unit isomorphisms and the canonical associator `((l,m),n) ↔ (l,(m,n))`, with
explicit universe joins; no strict equality of differently represented heads
is required. No finiteness or decidable equality is assumed.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Span inversion

`req~span-inversion~1`

Implement SoSyM B.2.2 inversion by retaining the head and swapping the legs.
Prove involution and that reduction is relational converse. This operation
asserts no categorical invertibility of arbitrary spans.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

<a id="relation-composition-adopted-q1-correction"></a>

## Relation composition: adopted [span-composition correction (Q1)](sources.md#span-composition-q1-research-for-4)

`req~span-relation-composition~1`

Adopt the [Q1 correction](sources.md#span-composition-q1-research-for-4) to
SoSyM B.2.1: for arbitrary spans `red(q ⋆ r) = red(q) ; red(r)`, where `;`
is existential relational composition in source-to-target order. Require no
finiteness, decidable equality or injectivity. Prove the canonical map from
composite links to the right-hand relation span is surjective, and existence
of a span isomorphism to it iff the outer endpoint map is injective.

For relational inputs, characterize this injectivity by at most one intermediate
object per outer endpoint pair. Prove sufficient cases: the first relation is
single-valued, or the converse of the second is single-valued; neither requires
totality. Uniqueness of intermediate objects alone does not suffice for arbitrary
spans, nor does single-valuedness of the second relation for relational inputs.
This correction is selected semantics, not a verbatim paper theorem.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Span witnesses and universe boundaries

`req~span-examples~1`

Provide kernel-checked examples of parallel links with identical endpoints;
empty spans and fibers; and relational inputs with two intermediate objects,
two composite links and only one reduced endpoint pair. Prove that the latter
composite is not isomorphic to the reduced relation span, even though its second
relation is single-valued. Include a parallel-input-link example where uniqueness
of the intermediate object fails to imply the stronger isomorphism. Exercise
conversions, unit/associativity laws and relation criteria at differing universe
levels. Expose the generic API via independent `import DPGraph`; examples remain
separate modules covered by the full build, kernel and axiom audits.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Bounded semantic graph

`req~setmap-semantic-graph~1`

Provide a graph over an ambient `U : Type u` whose vertices are subsets `A : Set U`
and arrows are existing spans between subtype carriers. Links live in an explicit
universe containing u (chosen as `max u w`); state vertex universe u and arrow
universe `max u w + 1`. Shared underlying objects retain their identity across
subsets. Reuse Quiv/Prefunctor without a category on span arrows, resizing or an
all-universes SetMap. Preserve unrestricted Span and Interpretation universes.
Exercise a larger link universe through the concrete interpretation.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Separate typed predicate arities

`req~predicate-arities~1`

Declare the selected Table 3/A.1 symbols with real arity quivers, separately
from meanings. Inverse has opposite arrows, commutation a triangle, key an
n-member common-source family, and cover/disjointness an n-member common-target
family. Unary maps and multiplicities have one-arrow arities; multiplicity
symbols carry a natural lower bound and finite natural or unbounded upper bound.
Retain the isolated central vertex for n=0 and repeated graph-map argument
bindings. Impose no global finiteness, decidable equality or implicit set-valued
default. Catalogue VC, naming/arity disciplines, arbitrary path equations beyond
the triangle and later `FormalCD`/`Clafer`-specific predicates as outside this generic
built-in vocabulary. `FormalCD` extensions supply nd/ad and the selected VC.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Inverse predicate

`req~predicate-inverse~1`

Interpret Table 3 inverse using B.1 Definition 2 and B.2.2: for opposite spans
q and r, require inhabited `Span.Iso q.inverse r`. This is leg-swapping, not a
categorical inverse equation. Prove symmetry and invariance under independent
endpoint-preserving relabelings of both link types, including across universes.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Triangle commutation

`req~predicate-commutation~1`

Interpret Table 3 equality as inhabited `Span.Iso (q.comp r) s` for a typed
triangle. Preserve every composable link pair and the continuing [Q1](sources.md#span-composition-q1-research-for-4) reduction
law. Prove invariance under relabeling all three spans. Exhibit relabeled
satisfying triangles and a two-composite-link/one-direct-link triangle whose
reduced relations agree but which fails commutation.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Bag-sensitive finite-family keys

`req~predicate-key~1`

A common-source finite family is a key exactly when target-preserving
equivalences between every pair of corresponding source fibers imply equality
of the two source objects. Compare full bags, retaining repeated values, with
no implicit totality, single-valuedness or set-valuedness assumption (Figure 21c).
Prove endpoint-preserving link-isomorphism invariance. Prove zero-member key
is equivalent to a subsingleton source. Check a key distinguishing bags with
identical support but different multiplicities and a failing key with equal
complete bag tuples at distinct sources.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Ordinary-key correspondence and repeated marriages

`req~predicate-key-functional~1`

Derive an ordinary-function specialization of `req~predicate-key~1` without
changing its unrestricted `Key`/`BagEquiv` meaning. Represent each function
`f i : A → B i` by a span with exactly one outgoing link at every source.
For every finite arity `n`, prove both directions of
`Key (fun i => Span.ofFunction (f i)) ↔ Function.Injective (fun a i => f i a)`.
For arbitrary span families, assume `Total` and `SingleValued` componentwise,
define their unique target values and prove the corresponding tuple-injectivity
equivalence, with justified link-preserving functional-span isomorphisms.
Set-valuedness alone does not provide a unique total value. Preserve independent
source, target and link universes; impose no inhabitance, finiteness or decidable
equality on the source or targets. Include zero arity, consistently with
`key_zero`, and empty/subsingleton sources.

Check a finite witness with two distinct marriages sharing wife and husband
values but having different dates: the spouse pair fails `Key` and the
spouse/date triple satisfies it. This establishes only that finite predicate
witness, not an unrestricted real-world marriage identity rule. Preserve the
existing multiplicity-sensitive, identical-support and equal-bag counterexamples.
Keep results independently available through `import DPGraph`, with examples
built and kernel checked by the existing module-discovery runner.

Primary semantics: SoSyM B.1 Definitions 1–5 / Theorems 1–2, Table 3 key and
Figure 21c. Supporting comparison: Diskin, Kadish, Piessens & Johnson (2000),
*Universal Arrow Foundations for Visual Modeling*, DOI 10.1007/3-540-44590-0_30,
§2.1 p. 348 (separating family / injective tuple), §3.3 pp. 353–354 / Figure 1
and §3.5 p. 356 (marriage key). These are derived library results under explicit
hypotheses; the 2000 set-valued notation is not identified with all SoSyM spans.
See the [partial-source assessment](sources.md#universal-arrow-foundations-partial-source-assessment)
and the [ordinary-key correspondence issue](https://github.com/kbak/clafer-semantics/issues/44).

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Covering common-target families

`req~predicate-cover~1`

Interpret Table 3 cover and §6.1.2 as every target object being reached by a
link in some family member. Permit bag-valued arrows. Prove invariance under
link isomorphisms and that zero-member cover is equivalent to an empty target.
Check positive and negative cover, repeated bindings and empty domains.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

<a id="disjoint-images-accepted-q8-correction"></a>

## Disjoint images: accepted [common-target disjointness correction (Q8)](sources.md#predicate-contracts-and-the-accepted-q8-correction)

`req~predicate-disjointness~1`

Use §6.1.2/Figure 21 common-target family maps: for distinct indices i and j,
no target value is reached by both maps. Table 3's common-source shape and
source-inequality condition are errors, not a second supported predicate.
Shared source objects do not exempt overlap. Permit bag-valued arguments and
prove link-isomorphism invariance and vacuity for zero-member families.
Check disjoint images, overlap, repeated nonempty inclusion bindings and empty
domains. Record the accepted interpretation and exact source locators.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Set-valued, total, single-valued and inclusion maps

`req~predicate-unary-maps~1`

Use B.1.4/Theorem 2 joint endpoint injectivity for set-valuedness; use A.1,
Table 2 and §6.1.1 source surjectivity for totality and source injectivity for
single-valuedness. Single-valuedness permits empty fibers and excludes duplicate
copies. Literal inclusion between subsets of U has a bijective source leg and
equal underlying source/target U values for every link. Prove each predicate
invariant under endpoint-preserving link isomorphism, the set-valued relation
characterization, total/nonempty-fiber and single-valued/subsingleton-fiber
characterizations, and inclusion's subset and identity consequences. Check a
literal and empty inclusion, a moving injective permutation and duplicate
identity links; existence of an injection alone does not imply inclusion.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Cardinal multiplicity bounds on links

`req~predicate-multiplicity~1`

Interpret Table 3 mult-trg/mult-src and B.1 indexed families by bounding each
outgoing/incoming link fiber, including repeated target/source values. Lower m
means an embedding from Fin m; finite upper n means an embedding into Fin n.
Unbounded upper * imposes no upper bound or local finiteness. Do not use a
natural cardinality that maps infinite types to zero. Prove isomorphism
invariance, source/target duality under inversion and agreement with distinct
reachable-value counts for set-valued spans. Check finite lower/upper boundaries,
empty fibers, repeated values, reversal and infinite fibers satisfying unbounded
ranges but failing every finite upper bound.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Concrete interpretation and generic model restriction

`req~predicate-interpretation~1`

Connect every symbol to its span meaning in the bounded semantic graph using
the existing Interpretation. Use delivered formula satisfaction, translation
and model reduct APIs. Demonstrate a satisfying concrete model, restriction
along a nonidentity declaration-preserving DP morphism, a rejected predicate
instance and explicit larger semantic link universes. Preserve the generic
interfaces and their lack of whole-model reflection.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Predicate acceptance witnesses

`req~predicate-examples~1`

Provide kernel-checked positive and negative witnesses for the complete selected
vocabulary: relabeled inverse/commutation; the [Q1](sources.md#span-composition-q1-research-for-4) two-path counterexample; one
versus two links with a repeated target; multiplicity-sensitive and failing
keys; cover/disjointness with repeated bindings, empty domains and zero-member
families whose central vertex survives; literal/empty inclusion and moving or
duplicated counterexamples; finite/empty/infinite ranges and reversal; concrete
formula translation and nonidentity model restriction; larger link universes.
Expose the reusable API through independent import `DPGraph` and keep examples
separate. The unchanged shared check must discover, build, kernel replay and
audit every added module; preserve warning enforcement, source export checks,
IntentBond coverage and independent semantic review. No solver is required.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Declaration unions on carrier cocones

`req~dpgraph-pushout-data~1`

For fixed-signature DP morphisms `F : Hom S T` and `J : Hom S U` at fixed
carrier vertex/arrow universes, a supplied carrier `PushoutCocone` determines a
DP-graph on its point. Declare exactly the union of the images of the left and
right declaration sets under formula translation by its two legs. Provide the
canonical declaration-preserving injections and their commuting DP-graph cocone.
Define compatible component models by equality of their reducts to `S`, keeping
semantic universes independent in that data type.

Expose `Pushout.CarrierCocone`, `obj`, `inl`, `inr`, `cocone` and `CompatibleModels` through
`import DPGraph`. These are derived constructions over SoSyM B.4 Definitions
9–10 and the abstract B.5 reduct, not concrete span, `FormalCD` or Clafer gluing.
Do not add finiteness, injectivity, inference closure or interpretation invariance.
The cocone data alone does not assert a universal property or model amalgamation.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof, itest

## Pushout universal property

`req~dpgraph-pushout-universal~1`

For `σ : Signature.{s, va, ua}`, `S T U : DPGraph.{s, va, ua, v, u} σ`,
`F : Hom S T`, `J : Hom S U`, `c : Pushout.CarrierCocone F J` and a supplied
`hc : CategoryTheory.Limits.IsColimit c`, provide
`noncomputable def Pushout.isColimit F J c hc : IsColimit (Pushout.cocone F J c)`.
Construct the DP mediator from the carrier universal property, prove preservation
of the union of translated declarations, both factorization equations and
uniqueness. Keep the explicit argument order `F J c hc` and expose the result
through `import DPGraph`. Its module `DPGraph.Pushout.Universal` independently
imports `DPGraph.Pushout.Basic`.

This is a derived result over the representation from SoSyM B.4 Definitions 9–10
and the abstract B.5 Theorem 3, not a verbatim paper claim. Keep signature
universes independent and carrier universes fixed; add no finiteness,
injectivity, semantic invariance, global pushout existence or model amalgamation
assumption. This requirement does not deliver a model equivalence.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof, itest

## Model amalgamation on a carrier pushout

`req~dpgraph-model-amalgamation~1`

For a signature in universes `s va ua`, fixed carrier universes `v u`,
`F : Hom S T`, `J : Hom S U`, `c : Pushout.CarrierCocone F J`,
`Ω : Quiv.{v,u}`, `I : Interpretation σ Ω` and `hc : IsColimit c`, provide
`Pushout.modelEquiv F J c I hc :
I.Model (Pushout.obj F J c) ≃ Pushout.CompatibleModels I F J`.

Its forward map must be exactly the pair of reducts along `Pushout.inl F J c`
and `Pushout.inr F J c`. Construct the inverse using the supplied carrier
colimit, prove that it satisfies the union of translated declarations, and
prove both inverse laws.

Prove `Pushout.modelEquiv_fst F J c I hc m` and
`Pushout.modelEquiv_snd F J c I hc m`, with exactly that explicit argument order,
stating respectively
`(modelEquiv F J c I hc m).val.1 = I.reduct (Pushout.inl F J c) m` and
`(modelEquiv F J c I hc m).val.2 = I.reduct (Pushout.inr F J c) m`.

Implement this in `DPGraph/Pushout/Models.lean` importing `Pushout.Basic`
independently of any DP-graph universal-property proof, and expose it through
`import DPGraph`. The semantic universe restriction is local to this result;
preserve all existing interpretation and reduct declarations. This is a derived
result over SoSyM B.4 Definitions 9–10 and abstract B.5 Theorem 3, not a verbatim
paper claim. Require no finiteness, injectivity, semantic invariance or separate
model amalgamation assumption, and assert no global pushout existence or concrete
`FormalCD`/`Clafer` gluing.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof, itest

## FormalCD structure and semantic boundary

`req~formalcd-structure~1`

Expose reusable `FormalCD` modules through `import FormalCD`, depending on `DPGraph`
and never Clafer. Reuse Quiv/Prefunctor, `DPGraph.Formula` and a declaration Set
at a supported signature containing the built-in predicates, retaining
`DPGraph.Predicates.signature` as the original specialization.

Annotate existing vertices/arrows with class/map
names, optional predefined identifiers and ordinary/bag/inclusion map modes.
Keep raw data independently inspectable from a WellFormed proposition and bundle
valid CDs with its proof. A shared registry provides stable identifiers, canonical
names and singleton/primitive kinds; entries are optional in each diagram.
Graph identities remain vertices/arrows, independent of their names. Preserve
typed bindings, repeated arguments and isolated arity vertices. Add no second
graph API, untyped arguments, formula identity tokens, dependency closure or
global finite/decidable assumptions.

WellFormed expresses syntactic/structural validity, not model existence or
satisfaction. Registry entries record identity/naming, not concrete primitive
or singleton domains. Generic models concern declared predicates under an explicit
interpretation. The metamodel-specific nd/ad meanings are specified below;
the selected VC extension is specified below. A general constraint language and
full object-diagram semantics remain future work.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## FormalCD naming and predefined identity

`req~formalcd-naming~1`

Require predefined classes to use their registry's canonical name and user-defined
class names to lie outside all registry-reserved names. Each selected predefined
identifier has at most one vertex realization. Inclusion arrows are named isA;
distinct inclusion arrows may share that name. Impose no global classifier-name
injectivity, inheritance acyclicity, compulsory predefined entries or map identity
based on names. Ground these obligations in SoSyM §6.1.1–3/Figure 21, distinguishing
the selected library representation from verbatim paper statements.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## FormalCD effective declarations

`req~formalcd-declarations~1`

Every inclusion-marked arrow must have its corresponding built-in inclusion
formula in the underlying `DPGraph`'s effective declaration set. Every ordinary
map must have its corresponding setValued formula. Explicit bag mode adds no
implicit setValued obligation, but authors may explicitly declare it. Inclusion
is separate from bag mode and receives its semantic consequences from the existing
inclusion interpretation. Use the typed unary binding with the actual arrow and
its endpoints; do not replace typed formulas with a weaker arity predicate.
Preserve all authored declarations in one authoritative effective set. Membership
obligations in WellFormed suffice; generic `DPGraph` defaults/meanings are unchanged.
These are the accepted §6.1.1–3 defaults, with Figure 21c's bag exception.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## FormalCD name-preserving morphisms

`req~formalcd-morphisms~1`

At a shared registry and supported signature (including the original built-in
specialization), a morphism between independently
well-formed CDs is an existing declaration-preserving `DPGraph.Hom` together with
equality of class names, map names, optional predefined annotations and map modes
at mapped vertices/arrows. Preserve none versus some and ordinary versus bag versus
inclusion exactly. Require neither global carrier injectivity nor reflection of
extra target declarations. This is an adopted library specialization of B.4
Definition 10, not an extra theorem attributed verbatim to the paper.

Provide identity, composition, extensionality from the underlying DP map and graph
map, associativity and both units. Prove all metadata obligations close under
identity/composition and that forgetting to `DPGraph.Hom` respects both operations,
reusing `DPGraph` laws. Reuse the existing satisfaction/model reduct after forgetting,
with explicit interpretation, contravariant direction and its identity/composition
laws. Do not re-prove the general reduct or claim arbitrary DP maps preserve metadata.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## FormalCD acceptance witnesses

`req~formalcd-examples~1`

Keep examples separate from the public entrypoint and kernel check:

- A finite valid CD with two distinct isA inclusion arrows, their endpoints and
  required declarations; an ordinary map's set-valued default and an explicit bag
  without that default (also allowing an authored bag setValued declaration).
- Invalid reserved user naming, incorrect predefined naming, duplicate realization
  of a predefined identifier, missing inclusion/ordinary defaults and an invalid
  inclusion name.
- A nonidentity morphism, explicit composable maps and their laws; a declaration-
  preserving DP map between valid CDs that cannot lift because a name or mode changes.
- An actual concrete interpretation/model and restriction, plus failing satisfaction
  illustrating the separate semantic condition.

Preserve independent `DPGraph` import, module discovery, import-layer checks, warnings,
kernel replay, axiom audits and trace coverage. The Figure 21c acceptance
requirements below extend these witnesses, together with the complete Figure
21b and VC requirements. No sorry/admit, unchecked axioms, unsafe/partial mathematical declarations,
disabled warnings, skipped checks or weakened scope/coverage.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Compatible signature extension

`req~formalcd-signature-extension~1`

Provide an injective inclusion of the built-in symbols with inverse arity graph
maps. Reuse `DPGraph` signatures, formulas and interpretations. Formula inclusion
must be injective and commute with translation; extension of interpretations must
restrict to the original meanings. Support independently bounded symbol, arity,
carrier, registry and semantic universes without narrowing `DPGraph`. Preserve the
original Raw/CD/Hom API and acceptance examples, ordinary/inclusion defaults,
bag behavior, optional registry metadata, forgetting, identity/composition and
model reduct laws at every supported common signature.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Figure 21c metamodel shape

`req~formalcd-metamodel-shape~1`

Construct the eleven-node, thirteen-arrow inventory in the source map as a typed
CD over an extended vocabulary. Retain distinct arrow identities despite equal
names. Include seven inclusions, five ordinary setValued defaults, total and
singleValued name/so/ta/pred annotations, total bag-valued args, two cover/disjoint
pairs and nd/ad/literal key declarations. Prove inventory, incidence and effective
declaration facts and local syntactic well-formedness. Distinguish the SING
metaclass, modeled class Sing and its object. Document inferred nd/ad bindings;
these must use existing figure incidence justified by the stated constraints.
No construction proof asserts semantic satisfaction or self-description.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Metamodel discipline meanings

`req~formalcd-metamodel-disciplines~1`

Give nd/ad mathematical meanings connected to the extended interpretation and
typed declarations. Name discipline checks canonical names of realized predefined
identifiers, user names outside the reserved set, optional-entry identity and kind
rules, inclusion names and compatible name restriction through the displayed
predefined inclusions. Impose no global classifier-name injectivity.

Arity discipline validates arbitrary candidate data against the selected symbol's
arity graph: every vertex image, both endpoints of every arrow, and a bijective
indexing of the actual args fiber by all arity arrows. Repeated argument values
are allowed. Explicit context supplies the signature, represented graph, registry,
name/identity interpretation, vertex images and occurrence indexing that the bare
graph does not recover. Missing, malformed and duplicated-index data can fail.
Derive the correspondence with existing typed Formula values in both directions.
The total args annotation separately excludes empty fibers; generic zero-arrow
arities remain legal. State the interpretation's bounded domain and universe joins.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Full graph-formula identity and projection limits

`req~formalcd-formula-identity~1`

Formula identity is the existing symbol and full binding. Prove extensionality
and a correspondence with valid raw binding data, including all vertex images
and indexed arrow actions. Distinct symbols, argument positions or isolated
vertex images can distinguish formulas. Retain repeated arguments.

Figure 21c's literal key(args,pred) uses the unchanged generic Key/BagEquiv meaning.
Its satisfaction is an additional instance condition. Check that bag projection
can forget positions and arrow-only projection can forget isolated vertices;
never quotient formulas by these projections or assert their injectivity without
hypotheses. Full-binding identity and the printed metamodel do not imply universal
realizability. The requirements below add the explicitly typed, signature/registry/universe-bounded
self-description statement, Figure 21b example and VC semantics. Add no self-containing
universe, resizing, unchecked casts or escape axioms.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Metamodel acceptance witnesses

`req~formalcd-metamodel-examples~1`

Kernel check the complete inventory/defaults, valid and invalid predefined/user
names and name restriction, invalid incidence and argument indexing, repeated
arguments, nontrivial symbol/binding identity, both projection failures, and the
zero-arrow/total-args boundary. Include a concrete nonempty extended interpretation
model. State which finite witnesses satisfy literal key and totality and which
fail, distinguishing fragments from whole metamodel instances. Preserve existing
examples, supported-signature morphism/reduct laws and independent public imports.
Run the unchanged shared validation and trusted trace checks without weakening
coverage, warnings, proofs or scope.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Bounded syntactic self-description

`req~formalcd-bounded-self-description~1`

For SoSyM §6.1.3 / Figure 21c, provide a named checked representation and
well-formedness statement reusing Metamodel.diagram and wellFormed in
CDOver with its concrete built-in-plus-nd/ad vocabulary, SING registry and
explicit small syntax/registry universes. Reuse the inventory and full-binding
Candidate.formulaEquiv correspondence. Class, Map and Signature remain ordinary
data. Preserve indexed occurrences, isolated vertex images, zero-arrow formulas,
literal bag key and total-args limitations. This is a syntactic representation
result, not semantic self-instantiation or universal every-CD realizability;
it requires no new axiom or metamodel-instance assertion.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Faithful restricted metamodel realization

`req~formalcd-metamodel-realization~1`

Implement the [realization contract](metamodel-realization.md) for any compatible
vocabulary, registry and well-formed CDOver, retaining independent universes.
Construct tagged classes, maps, exactly the effective full formulas, all symbols
and all strings; subclass membership preserves ambient identity. Include all
reserved registry names, even for unrealized identifiers. Argument links retain
every indexed arity-arrow occurrence, including repeated images. Construct the
name/arity contexts and descriptor without a target validity or model assumption.

Prove that this encoding satisfies every existing Figure 21c declaration iff
all declared formulas have nonempty arrow support and equal symbol/argument bags
separate full formulas. Derive nd/ad and the other 26 unconditional declarations;
prove necessity as well as sufficiency for total args and the literal key. Do not
alter predicates, quotient bindings, add dummy arrows, or require support of
unused vocabulary symbols, finiteness or absence of isolated vertices.

Decode the exact raw source on its represented carrier from the encoding,
context and explicit mode side data, without taking the original CD as a decoder
argument. Recover the effective declaration set, full vertex/arrow bindings,
names, predefined identifiers and modes even when realization hypotheses fail.
Distinguish syntax reification from source satisfiability and primitive-domain
realization. Preserve existing full-binding and bounded-self-description promises.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Particular metamodel semantic self-instantiation

`req~formalcd-metamodel-self-instance~1`

Prove the restricted realization hypotheses for Metamodel.diagram's actual
effective declaration set. Establish declaration-value injectivity and complete
indexed arities, then construct a model satisfying all thirty declarations under
the canonical context. Check exactly thirty formula objects and forty-six args
links and specialize exact reconstruction. State the bounded, context-dependent
DP semantics explicitly; claim no universe fixed point, universal every-CD
realizability, general primitive-domain theorem or unrestricted compilation proof.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Canonical realization acceptance boundaries

`req~formalcd-realization-boundaries~1`

Kernel check whole-model acceptance for empty declarations and for a supported
singleton formula with repeated argument images and an isolated arity vertex.
Check preservation of repeated names, distinct parallel maps, and unrealized
reserved registry entries. Prove the repeated args span is not set-valued.
Reject a declared zero-arrow formula and two supported formulas with equal
symbol/argument bags but different isolated vertex assignments. Demonstrate
exact reconstruction even for a rejected encoding. Retain the existing ordered
binding, zero-arrow, literal-key and full-binding witnesses and independent
public imports. Run the full validation, kernel, axiom and layer checks.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Complete Figure 21b example

`req~formalcd-figure21-example~1`

Construct Figure 21b / §6.1.1–3 with exactly Comp, ECU, Display, Int and five
arrow identities: i1:ECU→Comp, i2:Display→Comp, server:Display→ECU,
display:ECU→Display, version:Comp→Int. Both inclusions are named isA.
Register Int as a primitive with canonical name Int; do not require Sing or
other optional predefined entries. Preserve existing naming and map modes.
Use the compatible vocabulary extension for VC and full graph bindings.

The effective declaration set has exactly the twelve distinct formulas on PDF p.21:
disjoint(i1,i2), cover(i1,i2), inverse(server,display), inclusion(i1), inclusion(i2),
0..5(display), 1..1(version), 0..1(server), VC(server,i1,i2,version), and
setValued(version), setValued(server), setValued(display). Multiplicities count
outgoing links. Explain total/single-valued notation via these bounds, retaining
[Q8](sources.md#predicate-contracts-and-the-accepted-q8-correction) common-target disjointness and existing span inverse meanings. Prove inventory,
incidence, declaration membership/distinctness, naming/default obligations and
syntactic well-formedness in the same CDOver family as the metamodel.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Corrected guarded VC semantics

`req~formalcd-vc-semantics~1`

Adopt [Q7](sources.md#figure-21b-and-the-accepted-q7-correction): display.version ≥ server.version, with equality allowed and an absent
server satisfying VC vacuously. Sources: Figure 8 line 9 and its accompanying
§4.2.3 discussion (PDF p.10; §4.3 supplies configuration context on PDF pp.10–11), Figure 21a
OCL / §6.1.2, and Appendix 6; retain the discrepancy with the adjacent reversed
prose in the source map.

VC's arity has exactly the
server, i1, i2 and version arrows and all endpoints. Interpret its actual typed
formula through `DPGraph.Interpretation` over the existing bounded subset/span
graph, with an explicit integer realization/decoding and universe parameters.
Keep built-in meanings unchanged. Under inclusion and version 1..1 declarations,
prove correspondence with the guarded integer comparison. No True placeholder,
unconnected Boolean test, server-totality assumption, global primitive framework,
finiteness restriction or change to the generic predicate catalogue is allowed.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Figure 21b semantic witnesses

`req~formalcd-vc-witnesses~1`

Provide a concrete nonempty model satisfying all twelve effective declarations,
including inverse, cover/disjointness, multiplicities, defaults and VC, with
all integers explicitly realized. Kernel-check actual interpreted VC satisfaction
for a served display with a strictly greater version, equal versions, a strictly
lower version (failure), and an unserved display (success). Prove the eleven
other declarations still hold in the lower-version counterexample, isolating VC.
Show the unserved case satisfies 0..1 without falsely requiring totality.
Keep examples separate from public imports and distinguish whole Figure 21b
satisfaction from syntactic well-formedness and metamodel-instance claims.
Preserve all existing validation, trace coverage and dependency/toolchain pins.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Resolved 2014 Clafer syntax

`req~clafer-resolved-syntax~1`

Implement directly constructible deep containment syntax for the selected 2014
constructs in §5.3.1–5, §5.4–5, §6.2.2/Figure 22 and Appendix 3/Figure 27.
Keep resolved declaration IDs separate from source/display names, preserving
identity when names repeat. Distinguish the synthetic root, selected predefined
primitive-domain declarations (int, string, bool), and user declarations. Include
basic/reference-set/reference-bag forms, optional super IDs, abstractness and
both clafer and group multiplicities, with natural lower bounds and finite or
unbounded upper bounds. Input is already resolved and defaulted: retain authored
values separately, validate explicit overrides, default 1..1 clafer bounds,
keyword-induced optional children, and default 0..* or inherited group bounds.
Retain inherited keyword provenance. No parser, name resolver or elaboration
correctness theorem is promised.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Selected Clafer input well-formedness

`req~clafer-input-wellformedness~1`

State and check Clafer-local conditions from §5.3.4–5, §5.4–5 and §6.2.2:
unique resolved IDs, a distinguished parentless basic synthetic root with no
super, resolved parent/target/super edges, parentless non-root declarations
abstract, and nested abstractness confined to abstract containment. Primitive
domains are unique predefined basic declarations parented by the root, with
canonical names and no super. Require valid effective intervals and consistency
of authored/defaulted values. Enforce §5.5's kind restrictions and equal parents
when the super has a parent. Rule out containment and inheritance cycles using
the deep containment representation and explicit depth/rank conditions. These
conditions do not strengthen `FormalCD` or `DPGraph`. Supply a well-formed mixed
model with basic, set, bag, top-level abstract basic/reference and nested abstract
cases, plus rejected malformed or uninhabitable witnesses for important boundaries.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Constraint and binder input boundary

`req~clafer-constraint-boundary~1`

Expose a resolved declaration context and a finite indexed bag of referenced
scope occurrences for each constraint (§6.2.2/Figure 22). Preserve repeated
references in different positions; context is recorded separately. Provide
separate binder IDs, display names and resolved domain occurrences as the input
interface for [core constraint typing](spec.md#resolved-core-constraint-typing), validating known IDs and unique binder IDs per boundary.
Constraint bodies and expression typing are supplied by the separate core
constraint module below. Name resolution remains an upstream obligation; the separate
[denotation extension](constraint-denotation.md) supplies Appendix 4 equations. The context module must not depend on the expression
implementation. Check repeated-occurrence and dangling-reference examples.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Individual Clafer Shapes

`req~clafer-individual-shapes~1`

Represent Figure 16/Table 4 and §6.2.3's individual Shapes as typed role graphs
using the existing graph/CD foundations. The head class is always present;
source requires a parent and target requires a reference kind. Give head
(source→head), parent (head→source), dereference (head→target) and target
(source→target) maps exactly when their endpoints exist. Supply finite,
kind-indexed role inventories and incidence proofs. When a super is selected,
head inclusion is required and source/target inclusions exist exactly for shared
endpoints; absent supers supply no inclusion family.

Apply the accepted [top-level abstract correction](sources.md#resolved-2014-clafer-and-individual-shapes): §5.3.4 (PDF p.15) incorrectly excludes the
head of a top-level abstract clafer, contrary to §6.2.3 (PDF p.22) and Figure 23's
total head role. Retain the head and omit source/parent-dependent maps. An
abstract reference retains target and dereference. Read Table 7's basic-source
statement with this exception. Preserve publication and historical snapshots.

Use existing predicates for local inverse, triangle, effective multiplicities,
ordinary set defaults and the set-reference projection key when its endpoints
exist. Bag target maps have bag mode. Expose local diagrams as well-formed
FormalCDs without claiming model existence, full MCS invariants, global cojoining
or gluing. Include positive basic/set/bag/abstract examples and impossible
incidence/absent-role cases.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Finite syntax and compilation termination basis

`req~clafer-finite-traversal~1`

Keep finiteness local to the Clafer input and role presentation. Provide a finite
indexing of all traversed declarations and a structural fold on containment,
with a decreasing child measure and well-founded resolved parent traversal.
Reference IDs are not recursive children; cyclic references must not prevent
finite traversal. Prove finite class/map-role carriers. This is a basis for
the terminating structural Compile below; this traversal requirement alone
does not assert compiler correctness or a full MCS theorem. Preserve independent generic `DPGraph` imports.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## MCS metamodel and ownership

`req~clafer-mcs-metamodel~1`

Encode SoSyM §6.2.3/Figure 23 with the existing graph/formula and `FormalCD` APIs:
Role, ClassRole, MapRole, InclRole, String, PredefStr, Formula, Signature and the
Clafer owner; the cover/disjoint partition; labels, endpoints, slots and formulas.
Preserve the accepted correction from source `1` to `0..1` on the four ordinary-map
and three inclusion-role associations, meaning unique ownership within each
association's image. Shape guards require exactly the applicable slots. Retain
literal head-class source `1` and formula source `1`. Distinguish local slots,
role-graph identities, resolved class/map referents and displayed names. Do not
identify parent/dref/isA arrows by repeated strings. Keep the head of every clafer,
including top-level abstracts. The gluing requirements below use resolved
referent equality without changing role-level cojoining or ownership.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

<a id="complete-appendix-e-structural-discipline"></a>

## Complete Appendix 5 structural discipline

`req~clafer-mcs-disciplines~1`

Implement the complete applicable Tables 5–8 inventory and accepted [Q2](mcs-invariants.md#appendix-e-inventory) expansion
in [the MCS inventory](mcs-invariants.md). Use typed incidence and exact existing
Shape presence guards; express cojoining at role-graph vertex identity. Include
both endpoints of all four ordinary roles and three guarded super roles, root,
every supported primitive domain, basic/set/bag and parentless abstract cases.
Missing source/target endpoints forbid the corresponding inclusion slot.

Enforce
head/parent/dref/target and inclusion naming, both directions of Sing and all
primitive naming equivalences, and the target-name equation derived via the head
map. Bundle each discipline once as a proposition, without inconsistent duplicate
invariant fields. Preserve resolved hierarchy/kind restrictions at the structural
family boundary. Supply nonempty composed shapes with proved obligations,
including inherited roles, absent roles and distinct same-name arrows.
This is a structural MCS representation, not an AST compiler or model-existence
claim; [structural Compile](compile.md) provides conversion from the already resolved AST and formula generation.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## MCS formula bindings and literal constraints

`req~clafer-mcs-formulas~1`

Formula objects have one owner, a symbol and a complete well-typed graph binding,
retaining isolated vertices and repeated argument occurrences. Preserve the
literal bag key on `(args,pred)` separately from full binding identity and from
total args. Bag equality may permute occurrences; it is not indexed equality.
Zero-arrow arities remain legal in the generic formula API but cannot occur in
an MCS formula bank satisfying the printed total-args condition. Demonstrate
accepted repeated occurrences and rejection of duplicate-key formula objects.
Expose a DP-graph declaration set and transport existing local Shape declarations
without inventing a constraint language or asserting compiler completeness.
Keep those later obligations separate from structural validity.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Resolved core constraint typing

`req~clafer-core-typing~1`

Provide deep, intrinsically typed resolved expressions for the selected core of
SoSyM D.1/Figure 28 and D.3.1–2: Boolean conjunction/negation, same-sort equality,
integer comparison/addition/subtraction, collection cardinality, unary-set and
binary-relation union/difference/intersection and Boolean subsetting, unary–binary
image and binary–binary join. Both joins require matching middle classes. Include
Boolean/integer literals and explicit no/one/lone/some helpers for resolved input.
Follow the [Q3 source disposition](sources.md#appendix-d-rule-dispositions-q3):
intersection is ordinary common-element intersection, already printed as ∩;
D.4.1 identifies E and S on set expressions. This increment supplies syntax and
typing, not semantic equations or interpretation theorems.

Support inheritance-compatible expressions through explicit widening of object
classes or either relation endpoint to a chosen common type. Widening must follow
equal resolved IDs or actual super edges; arbitrary unrelated type coercions are
not permitted. Name resolution and selection/insertion of coercions remain caller
obligations. Integer operations are the implemented primitive fragment; other
primitive operations, higher-arity relations, tuple quantification and full
surface syntax remain implementation limits, not restrictions attributed to the
paper. The separate integer-extraction extension below supplies the partial
primitive bridge; it is not an evaluator for this core. No solver or substitution
is required.
Include accepted/rejected operand and join examples, including successful inherited
navigation, composition and a relation union with an inherited endpoint.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Lexical scope and typed constraint input

`req~clafer-core-binding~1`

Keep source names, resolved declaration/binder IDs and occurrence positions
separate. Universal quantification has a unary collection domain and a Boolean
body under a fresh binder ID; a variable has its domain's element class and is
interpreted as a singleton by the separate denotation extension. Check the domain
outside the new binder's scope. Preserve nested name shadowing and reject
out-of-scope variables, repeated active IDs, relation domains and non-Boolean
bodies. Prove that a typed variable indexes an existing local of the stated class.

Tie `this` to the enclosing class. State compiler input assumptions explicitly:
existing AST well-formedness, resolved map incidence, resolved boundary context
and occurrence bags, matching external binder IDs/names, and domains typed in the
outer lexical environment. Boundary binders are outermost first; the typed context
is nearest first. Preserve repeated scope/domain occurrences by indexed mappings
into the support graph; do not assert automatic extraction of minimal support or
correctness of textual resolution. Provide a complete input witness over an
existing well-formed AST and positive/negative quantification examples.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Constraint graph support and semantic boundary

`req~clafer-core-support~1`

Provide a finite graph of class/map occurrences for a constraint (§6.2.2/Figure
22). Map roles include head, parent, dereference, target and inheritance inclusion;
validate their endpoints against resolved declarations. Graph arrows and navigation
paths retain endpoint evidence. Widening paths must imply the reflexive/transitive
closure of actual inheritance edges. Preserve isolated vertices and repeated
resolved identities, with source names as metadata. Expose a `DPGraph` signature
whose predicate arities are these complete support graphs, and accept full graph
bindings for later formula construction. Check endpoint rejection and preservation
of repeated occurrences and full bindings.

Keep source-to-predicate translation separate from the new independent
[denotation extension](constraint-denotation.md), which supplies environments,
finite cardinality and explicit relational reduction of spans. Integer singleton conversion is supplied by
the separate extension below; this structural requirement does not assert it.
An abstract symbol/arity is not a proof of any constraint's meaning. Neither
expression satisfaction nor compilation preservation is asserted; independent semantic review remains necessary.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Integer extraction from primitive navigation

`req~clafer-integer-extraction~1`

Provide the selected D.3–D.4 unary collection-to-integer bridge as an explicitly
typed operation. A support annotation identifies an integer vertex, and resolved
input checks that its exact declaration ID has primitive integer origin. Names,
reference object classes and inheritance widening do not substitute for this
check. Preserve the complete graph support, binder context and existing widening.
A semantic binding respects equal resolved IDs and actual inclusion edges, and
identifies the annotated object's domain with an explicit integer realization.

Reuse `FormalCD.IntegerRealization`, independently of the Figure 21 extension: its injective encoding and
left-inverse decoder give a correspondence between its domain and all mathematical
`Int` values. The partial extraction result is `some n` exactly when the navigation
set is the singleton containing the encoded `n`. Prove unique results and the
necessary and sufficient hypotheses: one object, and that object belongs to the
integer domain. Empty, multiple-object and noninteger results return `none`;
never select an arbitrary object or use the decoder's off-domain value. Typing
alone gives no runtime singleton guarantee. Relational navigation results are
sets of objects; equal targets of multiple links denote one set element, without
changing the underlying link-sensitive multiplicity predicates.

Supply named proofs of correspondence, successful extraction, rejection boundaries,
resolved-ID rejection and inheritance preservation. Preserve arbitrary negative
and positive integers without overflow or finite-bitwidth arithmetic. Document
that this is an operation interface consumed by the independent [expression denotation](constraint-denotation.md),
not a general primitive-domain framework, parser or a reuse of VC as an evaluator.
See [the conversion contract](integer-extraction.md).

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof, itest

<a id="appendix-f-version-operand-well-definedness"></a>

## Appendix 6 version operand well-definedness

`req~clafer-version-navigation~1`

Represent the actual Appendix 6 PDF p.34 fragment's `version >= server.version` in
the typed core, following comp inheritance, version/server reference objects,
head maps and dereferences to the resolved integer class. Retain accepted [Q7](sources.md#figure-21b-and-the-accepted-q7-correction)'s
display >= server direction. Derive both operands' singleton/domain hypotheses
from the selected default 1..1 version/server multiplicities, functional total
dereferences, and actual inheritance inclusions. Do not assume the final operands
are singletons or that the comparison holds. Supply a resolved well-formed AST
fragment and a complete typed constraint input witness.

Give a partial interpretation of this selected comparison and concrete navigation
examples for greater, equal and lower values, plus empty/multiple/wrong-domain
boundaries. Appendix 6 has a mandatory server and an unguarded comparison;
Figure 21's 0..1 server and nonempty-server guard remain a distinct contract.
The theorem is conditional on the selected structural semantics, not a proof
that structural Compile establishes those semantics or a whole Appendix 6 model.
The separate inherited realization and constraint denotation extensions supply
inherited structures and other expressions (including `server = parent`);
this fragment requirement does not assert their combined model result. Document [Q3](sources.md#appendix-d-rule-dispositions-q3) limits and
the full mathematical integer realization separately from finite object examples.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Structural Compile input contract

`req~clafer-compile-contract~1`

Define Compile on the finite resolved AST of §6.2.4 with an explicit input
contract. Require `AST.WellFormed`, canonical `Sing` naming, and rejection of
registry-reserved user names; primitive origins retain their canonical names.
Require a typed constraint body satisfying the existing `Constraint.Input`
interface for every attached boundary occurrence. Occurrences are indexed by
owner and position, so repeated boundary numbers or equal bodies do not omit
attachments. Require `0 < support.mapCount` for accepted constraints, solely
at the Compile boundary. Keep generic `Constraint.Input` and `DPGraph` formulas
unchanged, including their zero-arrow cases.

Resolution, default elaboration, binder environments, explicit inheritance
widening and nonminimal support remain caller obligations. Compile must not
assume an output MCS, output validity or a supplied graph binding. Unsupported
surface/primitive forms remain those of the typed core; this increment adds no
expression interpretation or full semantic-preservation claim. The separate
augmented group output below extends generated declarations without changing this
input contract or asserting general abstract/inherited-family realization. Follow the [Compile contract](compile.md).

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Structural Compile construction and preservation

`req~clafer-compile-structure~1`

Implement a total Lean transformation from accepted resolved ASTs to MCS values,
following §6.2.4 and Tables 5–8 (see Appendix 5) with the accepted presence/ownership
corrections. Traverse finite containment and resolve edges by terminating finite
lookup; never recursively follow reference edges. Allocate class identities by
preorder occurrence and map identities by owner and role. Allocation must be
deterministic for the same ordered input and independent of display-name equality;
no stability across insertion or reordering is promised.

Derive all structural MCS obligations from the input contract: exact guarded
roles, incidence, parent/child and target cojoining, inheritance, effective bounds,
root/domain classification and naming. Preserve source DeclId referents separately
from generated identities and display names. Shared identity means repeated
references to one uniquely declared DeclId; no distinct-head aliasing is inferred.
Prove freshness and naming preservation. Check nested repeated names, inherited
and cyclic/repeated reference inputs, shared targets with distinct heads/dref
maps, and explicit predefined classification with reserved-user-name rejection.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Compile formula generation and full bindings

`req~clafer-compile-formulas~1`

Generate every existing local Shape declaration and every guarded inclusion
predicate, preserving the built-in signature via its existing disjoint-extension
interface. Attach every typed source constraint through the established
occurrence-indexed syntax-only signature. Construct its complete graph binding
from resolved class/map incidence, preserving isolated vertices and repeated
support occurrences. Prove context/owner and incidence preservation, local and
source declaration completeness, and well-formedness of the resulting MCS bank.

Prove positive argument support and the literal bag key, allowing occurrence
permutations rather than replacing bag equality with indexed equality. Local
formula identity is determined by its generating role and predicate; constraint
symbols retain their attached source occurrence, consistent with the existing
constraint signature. Check repeated occurrences of one resolved map and equal
source boundaries at distinct positions. These declarations provide syntax and
structural validity; neither typed bodies nor fresh predicate symbols establish
constraint meanings or semantic preservation.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Compile group data and direct-child maps

`req~clafer-compile-group-data~1`

Preserve each resolved declaration's complete `GroupMultiplicity` in the
compiled family, including authored/effective values and keyword provenance
(Appendix 3 PDF p.32). Derive validity of its effective bounds from the accepted
AST; do not run default elaboration again or change keyword child defaults.
Derive the direct-child inventory exactly from resolved parent identity. Each
entry supplies the typed head map from that parent's head to the child's head,
including reference children; different child entries retain different map
identities. This inventory is finite because the accepted AST is finite.

Retain empty inventories and abstract declarations as structural input. Check
preservation of an empty xor group's metadata and reference-child head incidence.
These data guarantees support the interpreted extension below; metadata
preservation alone does not establish group satisfaction.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Interpreted group compilation and augmented gluing

`req~clafer-compile-groups~1`

Generate one interpreted group declaration for every concrete context using its
resolved effective bound and the union of own and super-hierarchy child heads.
Abstract groups supply inheritable bounds without a separate original-child
invariant. Preserve Appendix 3 provenance/defaults/overrides and ordinary explicit
constraints on abstract contexts. Follow the accepted [group-inheritance contract](group-compilation.md)
and its pinned source citations, including the explicit discrepancy with the
compiler's empty-inventory skip.

Retain complete arities, context vertices, owner identities, head and inheritance
maps and incidence-preserving bindings. Count distinct ambient child-head objects
per parent object, including distinct reference occurrences sharing one target;
multiple paths to the same object count once. Empty inventories count zero:
zero-containing bounds pass, and positive lower bounds force empty context extents.
Do not replace this meaning with a declaration count, target count or sum of fibers.

Expose an augmented Compile result with a separate generated declaration component
for zero-arrow supports. Forgetting it must recover the existing structural MCS.
Keep the old bank's full bindings, literal bag key, nonempty args and user input
contract unchanged; do not claim the complete bank satisfies MCS total args.
The complete diagram must contain the exact union of both components, and gluing
must preserve its exact translated image, naming, incidence, metadata and complete
effective defaults. Prove that complete satisfaction accounts for both components
and that each generated group is equivalent to the selected child-count bounds
under explicit typed-relation and finite-count assumptions. Reuse the shared
DPGraph finite-range bridge and [structural representation APIs](structural-checker.md);
group mathematics must not import the finite checker or extend its guarded fragment.
Keep the [inherited field realization and map restriction](inherited-realization.md)
obligations explicit;
selection alone cannot establish those laws.

Check actual compiled/glued positive and negative xor (one passes, zero/two fail
while individual optional bounds hold), inherited extension and effective override,
numeric bounds, or/mux/opt, repeated reference targets, overlapping inherited
head visibility, multiple instances of one declaration, and empty-child bounds
in empty and inhabited contexts, including zero-arrow support.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof, itest

## MCS gluing identity and incidence

`req~clafer-gluing-identity~1`

Construct the graph of used class/map referents from the delivered MCS roles
and labels (SoSyM §6.2.5), with the identity rule approved in the
[resolved-referent gluing issue](https://github.com/kbak/clafer-semantics/issues/23). Identify class roles if and
only if their classReferent values agree, and map roles if and only if their
mapReferent values agree. Equal map referents must have equal source and target
class referents. Require class/map names, optional predefined registry identities
(and hence kinds), and map modes to agree on identified roles. Conflicts are
invalid input; neither strings nor common endpoints generate identifications.
Prove incidence before transporting declarations. Preserve parallel maps with
different referents and allow intentional noninjective class/map labeling.
Use the existing Quiv/Prefunctor API and small MCS universes; no global pushout
existence or universal property is required.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Exact gluing declarations and DP labeling

`req~clafer-gluing-declarations~1`

The glued declaration set is exactly the image of the source formula bank under
postcomposition with labeling, at the same signature. Prove label is a graph
morphism and a declaration-preserving `DPGraph.Hom` (B.4 Definition 10). Preserve
the complete typed binding, including isolated vertices and repeated argument
occurrences. Do not add target defaults to this exact image. The source literal
bag key and total-args obligations remain separate: a valid source bank does not
imply that translated formulas are injective or that a target formula bank
satisfies that key. No constraint interpretation or compiler generation theorem
is asserted.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## FormalCD validity after gluing

`req~clafer-gluing-formalcd~1`

Descend class/map names, predefined annotations and map modes to used referents
with preservation theorems. Derive predefined classification from semantic
origins through a shared registry, using the existing Sing/int/string/bool names
and singleton/primitive kinds; spelling alone must not create a registry identity.
Prove `FormalCD.RawOver.WellFormed` separately from DP preservation, with explicit
naming, registry uniqueness, metadata consistency and effective-default
completeness hypotheses. For valid MCS values, derive canonical naming and
registry uniqueness from the structural disciplines and origin annotations.
Ordinary setValued and inclusion defaults must already be supplied by the source
bank under the vocabulary embedding. Bag mode imposes no additional default.
MCS.Valid alone is insufficient for this completeness condition. Support the
existing small compatible vocabularies, without a new interpretation or claim
of semantic satisfaction, model existence or metamodel self-instantiation.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Gluing acceptance witnesses

`req~clafer-gluing-examples~1`

Kernel check a nonempty valid MCS with distinct class and map roles intentionally
merged, plus parallel same-name maps with different referents that remain
distinct after gluing. Repeated parent and isA names at unrelated endpoints must
not identify maps. Reject source/target, class/map name, predefined identity/kind
and mode conflicts. Exercise canonical predefined naming and bag behavior,
complete binding transport with repeated arguments and isolated vertices, and
failure of translated-formula injectivity despite the source literal key.
Exhibit DP preservation together with failure of `FormalCD` validity when defaults
are missing, including a nonempty valid source bank; also prove a positive
`FormalCD` validity result with sufficient defaults. Keep examples separate from
public imports and preserve [guarded Appendix 5 clauses (Q2)](mcs-invariants.md#appendix-e-inventory) and [source ownership bounds (Q9)](mcs-invariants.md#figure-23-source-multiplicity-correction), the existing validation gates and OFT IDs.
[Compile-to-gluing integration](representative-models.md) and general constraint semantics remain
separate.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Effective structural core and supported fragment

`req~clafer-effective-core~1`

Provide the accepted [effective-core interface](structural-checker.md) in the Clafer layer, retaining
resolved identities, display names, parent/super/reference edges, root/origin,
abstractness and effective local/group bounds without fabricated authored/default
provenance. State well-formedness separately from the guarded S fragment in
[the comparison contract](resolved-ir-comparison.md). Preserve all existing syntax,
Compile, gluing, [span composition (Q1)](sources.md#span-composition-q1-research-for-4), [common-target disjointness (Q8)](sources.md#predicate-contracts-and-the-accepted-q8-correction) and top-level abstract corrections. Reject excluded and
pending combinations, including primitive values, user expressions, nested
abstract bodies, reference inheritance and nontrivial abstract groups. Abstract
inheritance chains remain available. Raw candidates may contain unrelated class
overlap; satisfying configurations must meet declaration disjointness.

Prove effective erasure correspondence for valid supported constraint-free ASTs
and the selected compiled structural interpretation, with complete declaration
and metadata hypotheses explicit. Equal erasure must give equal structural
satisfaction. The construction must not require importing a convenient authored
AST or assuming a caller-supplied equivalence theorem. Keep core data and independent
structural meanings importable without Compile or Verification; the erasure adapter
belongs to Compile.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof, itest

## Whole-model structural satisfaction and interpretation

`req~clafer-structural-satisfaction~1`

Define independent global structural satisfaction for the accepted fragment from
SoSyM §§5.3–5.5, 6.1–6.2, B.1–B.5, Table 3/A.1 and Appendix 5. Cover singleton
fresh root, used-object coverage and containment reachability, per-declaration
parent ownership, shared-object inheritance, abstract cover and common-target
sibling disjointness, reference totality, set keys, local multiplicities and
concrete own-child group bounds. Groups count the union of child head objects;
references count occurrences, including distinct heads with equal parent/target.

Require an independent declaration-disjointness obligation: for distinct resolved
declarations d and e, their head extents are disjoint whenever neither is reachable
from the other through super edges. This applies to nested declarations and separate
inheritance trees. Containment ancestry, equal names and shared reference targets
do not establish comparability. Preserve the same object along its super chain;
inherited context views restrict existing field objects and links and are not
fresh declarations. This is the [declaration-disjointness clarification](sources.md#declaration-disjointness-clarification),
not a theorem that the paper uniquely determines the global rule.

Construct the subset/span interpretation and prove the correspondence to the
selected complete compiled/glued structural diagram, explicitly accounting for
global obligations absent from local Shapes. Prove the required ordinary-map
representation, link/fiber count and key correspondences, object/link renaming
invariance and completeness of the declared finite representation domain. Keep
`DPGraph` independently importable and unrestricted. Do not claim global SetMap,
user-expression semantics or full compiler/optimizer/source preservation.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Finite structural checker and input protocol

`req~clafer-finite-checker~1`

Provide finite shared-object carriers, class memberships, containment and
occurrence-preserving reference data and a terminating executable checker under
`Clafer/Verification/`. The deterministic protocol distinguishes malformed or
unsupported input from well-formed candidates that violate structural constraints.
Duplicate object/link/ordinary-tuple identities and dangling/ill-typed endpoints
are malformed; absent/multiple parents or dereference values are semantic
violations. Unrelated declaration overlap is also a semantic violation, never
malformed or unsupported solely because of the overlap. Keep empty classes and
failing candidates in the representation.

Prove both directions of `check m c = true ↔ StructuralSatisfies m (realize c)`
under explicit validity and fragment hypotheses, plus malformed-input rejection.
The specification must be independent of checker output. Count finite fibers
using the existing embedding-based cardinal predicates; unbounded upper limits
impose no finite cap. The checker theorem is kernel checked, while an ordinary
native run is not a fresh kernel proof of the individual verdict. No per-instance
certificate is claimed without a separate construction and verification theorem.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof, utest

## Structural checker boundary and mutation witnesses

`req~clafer-checker-witnesses~1`

Supply positive and negative whole-model kernel-checked witnesses and executable
tests for empty classes, zero/optional/exact/bounded/unbounded finite counts,
groups, nesting, admitted inheritance and abstract cover/disjointness, malformed
identities/endpoints, and repeated-target set/bag behavior. Exercise reference
cycles without recursive target traversal. Reject unrelated declaration overlap,
including nested declarations and distinct inheritance trees, while accepting
distinct objects, same-object super chains and permitted shared reference targets.
Preserve typed overlap candidates, union counting and inherited-view identity.
Detect deliberate duplicate-collapse and omitted-bound mutations with the
corresponding assertions. Keep all existing validation and coverage policy;
record full pinned validation, theorem-axiom inspection, source-matched evidence
and independent semantic review before acceptance. Candidate enumeration,
production generation and solver integration remain outside this checker contract.

Covers:
- `intent~formalization-foundation~1`
- `intent~traceable-contributions~1`

Needs: impl, proof, utest

## Selected inherited field and explicit abstract realization

`req~clafer-inherited-realization~1`

Extend the Clafer whole-model interpretation for the accepted Appendix 6
nested-abstractness, inheritance and group combinations in
[the scoped source contract](inherited-realization.md).
Preserve the [finite checker](structural-checker.md)'s guarded fragment; enforce
the [declaration-disjointness rule](sources.md#declaration-disjointness-clarification) in both
the checker and this extended satisfaction relation. Read authored abstractness
from retained AST metadata; do not reconstruct it from the erased effective flag.
Keep the existing equal-parent declaration rule. Support the listed seven super
edges to parentless explicit basic abstracts and ordinary nested field templates;
general nested explicit abstract/refinement combinations remain unsupported.

Use the same ambient objects and existing containment/dereference links. A field
view at a context contains exactly its existing objects whose unique parent is in
that context. Prove restrictions, shared occurrence identity along super chains,
unique ownership, and context coverage derived from actual parent/type coverage.
Disjoint parent alternatives yield disjoint owned fibers; ancestor views may
intersect. Explicit abstract types are covered by direct explicit subtype heads
with common-target sibling disjointness, even when covering heads are field
templates. An explicit abstract leaf is empty; an ordinary effective-abstract
field is not emptied by absence of an explicit subtype. When both classifications
apply, enforce both. Exclude ungrounded recursive realization islands and derive
root reachability from the selected finite rank and whole-model conditions.

Count the [union of own and inherited child heads](group-compilation.md) once per
ambient object, retaining
distinct reference occurrences at equal targets. Enforce effective group bounds
at realized ordinary fields, particularly options.size; preserve the group contract's
explicit abstract-template override and empty-inventory policy. Transport ordinary owner
constraints to subtype and context-view objects parametrically, without claiming
a general expression evaluator. Preserve [Q1](sources.md#span-composition-q1-research-for-4), [Q8](sources.md#predicate-contracts-and-the-accepted-q8-correction), top-level abstract heads and the
absence of parentless local-fiber/global-cardinality inventions. Prove explicit
compatibility with [finite structural satisfaction](structural-checker.md) and therefore its supported checker results.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Generated inherited realization and structural correspondence

`req~clafer-compile-realization~1`

Generate or derive the structural obligations of `req~clafer-inherited-realization~1`
in the actual compiled/glued representation. Generate cover/disjointness for every
explicit abstract family, including empty families, and effective groups for
realized ordinary fields omitted by the effective-abstract guard. Preserve all [generated group
declarations](group-compilation.md) and source constraints. Construct full bindings and prove actual
declaration completeness and exact gluing images. Establish semantic correspondence
from the constructed interpretation, not a caller-supplied equivalence assumption.
Derive inherited map restrictions and link-preserving commutation from the same
interpreted maps. Keep ordinary constraint meaning an explicit parameter
for [constraint denotation](constraint-denotation.md) and
[preservation](constraint-preservation.md) and retain every occurrence's original binding.

Forgetting the extension recovers the existing augmented Compile and its valid
structural MCS. Preserve role/referent/name separation, incidence and metadata
compatibility, effective-default completeness, input positive support and the
original bank's total-args/key discipline. Do not assert that the larger raw bank
satisfies Figure 23 total args. Provide whole-model equivalence with explicit
root/typedness and declaration-disjointness conditions and structural scope
transport for later interpretation. Declaration disjointness is an explicit global
condition on the configuration; local Shapes and generated abstract-family predicates
alone do not establish it.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

<a id="appendix-f-inherited-structural-witnesses"></a>

## Appendix 6 inherited structural witnesses

`req~clafer-inherited-witnesses~1`

Provide kernel-checked positive witnesses for inherited comp.version across
ECU/plaECU/ECU1/ECU2 and display/plaDisplay, display.options and nested xor,
and plaECU.plaDisplay in both ECU1 and ECU2. Check compiled/generated and glued
predicates on the actual constructed structural fixture. Reject inconsistent
inherited containment/dereference values, uncovered explicit abstracts, forbidden
explicit sibling overlap and inheritance-incomparable declaration overlap, shared
owned occurrences at distinct parents and inappropriate duplicate occurrences. Reject an xor violation at realized
options.size. Retain the source-ID mapping and the separate twelve-conjunct scope
inventory; these structural witnesses do not establish the
[complete expression-bearing fixture or its satisfaction theorem](telematics.md).

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Explicit constraint model environments

`req~clafer-constraint-environments~1`

Interpret the resolved typed core over explicit shared-object model environments
(Appendix D.1–D.4). Record `this`, resolved maps, singleton bound variables and
lexical scope. Preserve actual inheritance inclusions and shared object identity;
repeated resolved map occurrences preserve link identities and endpoints. Global
navigation can select parentless abstract extents. Keep local finiteness
obligations separate from the complete integer domain. Preserve the [guarded finite
checker](structural-checker.md) and the [inherited realization interface](inherited-realization.md).

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Independent core denotation

`req~clafer-constraint-denotation~1`

Give independent mathematical meanings and constructor equations for all supported
Boolean, integer, unary-set and binary-relation constructors, both joins,
quantification, cardinality and no/one/lone/some helpers. Apply [Q3](sources.md#appendix-d-rule-dispositions-q3) ordinary
intersection. Make span reduction explicit; retain original links and count
reference heads separately from dereferenced targets. Integrate the [partial singleton
extraction bridge](integer-extraction.md), deriving Appendix 6 numeric operand definedness from structural
map bounds, reference functionality and inheritance. Undefined is distinct from
false. Do not define truth by evaluator success or silently assume final operand
singletons. No executable evaluator is required; one would require a separate
agreement proof on its stated finite domain.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Constraint invariance and boundary witnesses

`req~clafer-constraint-semantic-laws~1`

Prove constructor equations and relevant environment, renaming and support
invariance. Exercise empty domains, nested shadowing, repeated map occurrences,
set versus link/reference-head counts, finite-cardinality boundaries and integer
extraction failure. Positive and negative witnesses must distinguish incorrect
intersection, join, comparison and quantifier interpretations. Keep original
span identities and all source typing/binding obligations.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

<a id="appendix-f-resolved-expression-inventory"></a>

## Appendix 6 resolved expression inventory

`req~clafer-appendix-f-expressions~1`

Supply all manual c01–c12 expansions from the accepted inherited inventory,
retaining implicit some, implication/equivalence, >=, repeated names,
relative/global/inherited navigation, no cache, server = parent and display-head
counts. Preserve [Q7](sources.md#figure-21b-and-the-accepted-q7-correction)'s display >= server direction without Figure 21's guard.
Exercise implication vacuity and actual operator combinations with positive and
negative witnesses. Check the resolved supports against the complete inherited
AST. General textual resolution remains separate. The extension requirement
for preservation, `req~clafer-constraint-preservation~1`, supplies the selected Compile/gluing bridge;
the complete combined fixture is specified separately by
requirement `req~clafer-appendix-f-complete~1`. See the
[denotation contract](constraint-denotation.md).

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Derived source-constraint predicate meanings

`req~clafer-constraint-predicates~1`

For the resolved typed core of Appendix D.4, derive each source occurrence's
predicate meaning from its body, complete support graph, explicit external-binder
domains and a fixed integer realization. Evaluate at every object of its context
class. Introduce external binders in lexical order, checking each domain before
its binder enters scope; do not choose a domain from a mere existence proof.
Preserve empty-domain vacuity and distinguish undefined operations from defined
false bodies. Require shared resolved class identity, coherent original map links,
literal inheritance inclusions and actual integer-domain realization. Retain
local finiteness and singleton extraction obligations. Callers must not supply
arbitrary predicate meanings or assume the desired truth equivalence.

Prove correspondence between this meaning and independent source denotation on
admissible complete arity diagrams, including explicit closed-body specialization.
See the [preservation contract](constraint-preservation.md).

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Selected Compile and gluing constraint correspondence

`req~clafer-constraint-preservation~1`

Prove the full arity-binding and source/formula satisfaction correspondence for
actual generated Compile bindings. Derive context ownership, repeated resolved
class and map identities, and preservation of original links; retain isolated
vertices and every support occurrence. A literal argument bag is not full binding
identity. Derive inclusion admissibility from generated local declarations while
keeping primitive-domain realization explicit.

Transport the interpreted source formula along the actual labeling morphism and
prove its membership in the exact declaration image. Compose with the generated
local/group/inheritance/abstract bank and its selected shared-object realization
to prove both directions of whole-model satisfaction correspondence. State
selected-core, primitive, typing/root, declaration-disjointness and
canonical-candidate assumptions
explicitly. Derive generation/completeness from actual construction; no client
supplies a complete semantic bridge. Generic model reduct does not imply
unrestricted reflection for arbitrary targets. Preserve effective-default
completeness, the original MCS total-args/key proof and positive-map input contract.
This extends the structural promises without reinterpreting them as earlier
expression-preservation results or claiming textual compiler correctness.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

<a id="constraint-preservation-sensitivity-and-appendix-f-support"></a>

## Constraint preservation sensitivity and Appendix 6 support

`req~clafer-constraint-preservation-witnesses~1`

Audit all twelve Appendix 6 bodies against positive-map Compile support and
preserve their complete resolved bindings. Check that each uses actual source
navigation; do not add dummy maps or weaken total args. Retain the full integer
domain and record any mismatch with finite primitive placeholders separately from
the actual `1..1` version/server operand bounds. The complete selected-model fixture is specified separately by
requirement `req~clafer-appendix-f-complete~1`; this interface supplies its semantic correspondence.

Provide predicate-satisfaction witnesses sensitive to version order, display-head
count, server/parent navigation, context/binding identity and changes to interpreted
bodies. Check explicit external domains and show that structural compilation
success does not discharge source truth. Preserve scalar-conversion failures and
the existing positive/negative core denotation examples.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Representative compilation and gluing

`req~clafer-representative-integration~1`

Apply the delivered Compile/gluing correctness interfaces to concrete resolved
models (SoSyM §6.2.4–5, selected Figures 16, 18, 21–23 and Appendix 6), proving
expected nesting, inheritance, shared-reference identity, multiplicity and typed
constraint-attachment relationships. Establish MCS validity, `FormalCD` validity
with complete effective defaults, and exact translated declaration preservation
for the selected concrete banks. Keep role identities, referents and names
separate; retain full support bindings and repeated constraint occurrences.

Check actual generated group predicates after both compilation and gluing. A
compiled/glued xor must accept one selected child object and reject zero and two,
with all individual optional child-head multiplicity formulas satisfied in each
case. Reuse the delivered group/structural semantics, including inherited fields;
AST group metadata alone does not meet this obligation. Reuse the complete
Appendix 6 declaration projection and its nonempty structural realization.

Compile and glue the selected Appendix 6 c02 typed attachment, preserving the
mandatory server and unguarded display-version >= server-version direction.
Derive the delivered integer-navigation bound/inclusion hypotheses from the
actual emitted local predicates under interpretation; keep the integer-domain
assumption explicit. Reuse the selected partial comparison and its defined
true/false and invalid-operand witnesses. Distinguish structural attachment,
operand definedness, interpreted predicate satisfaction and whole-model
satisfaction. Do not substitute Figure 21's optional guarded VC or assert general
expression preservation as part of this structural promise. The separate
denotation and preservation requirements state those semantic obligations.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Representative paper coverage accounting

`req~clafer-representative-coverage~1`

Maintain a concise [feature/source and completion matrix](representative-models.md)
linking every advertised feature to a checked example and actual theorem. Account
for all Appendix 6 d01–d26 declarations and c01–c12 conjuncts from the accepted
[inventory](inherited-realization.md), including every omission from each selected
fixture. Separate required results, proved statements, assumptions and unfinished
questions. Preserve the distinct source IDs of each representation; do not combine
separate fixtures into an unsupported full-model claim.

The structural projection includes all printed declarations; the separately
compiled c02 fragment is a supported subset, not full Appendix 6 completion.
Full interpretation of all printed constraints, final selections and a nonempty
satisfying full model have the separate contract `req~clafer-appendix-f-complete~1`. [Constraint preservation](constraint-preservation.md) depends on this structural milestone and
is not a prerequisite for its narrower result. Preserve independent public imports
for `DPGraph`, `FormalCD` and Clafer under the existing layer checks. Close the representative-integration issue only after its deliverables are
accepted and the implementing PR is merged.

Covers:
- `intent~formalization-foundation~1`
- `intent~traceable-contributions~1`

Needs: impl, proof

## Pinned resolved compiler import

`req~clafer-resolved-import~1`

Implement the authorized [resolved importer](resolved-import.md) under `Clafer/Verification/`, reusing the
accepted [effective core, candidate interface and guarded structural semantics](structural-checker.md). Import
only analyzed JSON from `gsdlab/clafer@6750e6f591b2131549122c13dee94d3d2257eaea` (0.5.4)
under the versioned [import protocol](resolved-import.md). Preserve compiler UIDs
separately from display names, parent/super/reference identities, effective local
and group bounds, the exact `-1` unbounded sentinel and set/bag mode. Do not
fabricate authored/default provenance or enlarge the comparison fragment.
Validate nullable source spans as metadata, keeping the single-file library
capture distinct from CLI file-qualified JSON. Preserve apostrophe display names
and escaped, collision-distinct UIDs. Reject older compiler/export identities.

Reject duplicate JSON keys, unknown fields/tags, duplicate/reserved/dangling IDs,
inconsistent nesting/bindings/type hierarchies, prohibited cycles, missing or
invalid cards, excluded modifiers and unsupported combinations. Preserve reference
cycles and repeated names. Reject expressions, assertions, objectives, primitives,
temporal forms, expression targets and backend escapes; no silent dropping.
Validate finite UID indexing, bounds, rank and unused-abstract certificates in Lean
before checking. Preserve candidate object/head occurrence identities and keep
malformed/unsupported input distinct from semantic violations.

State a fieldwise imported-data representation relation. Prove normalized identity,
edge/bound/mode preservation and structural-satisfaction correspondence for accepted
inputs, deriving well-formedness/support from admission. Compose with the existing
checker correctness and selected interpretation; roundtrips alone do not suffice.
Keep JSON/parser/capture and runtime assumptions explicit. Supply kernel/native
witnesses and actual pinned export tests, including repeated names, repeated-target
bag/set heads, inheritance, nesting/groups, unused abstracts and malformed versions.
Exercise 0.5.4 keyword/numeric defaults and unreachable concrete-group rejection
without adopting them as new Lean semantics; retain the documented differences.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof, utest

## Same-generation compiler capture

`req~clafer-compiler-capture~1`

Provide external capture/protocol scripts under `scripts/verification/` and
fixtures under `tests/`. Pin compiler source, resolver/dependencies, build tools,
export schema and effective options. Capture JSON and static Alloy in one analyzed
compiler invocation, retaining original bytes, common manifest and SHA-256 hashes,
pre/post-string-pass IR, empty string maps, the actual consumed UID map/fixed
registry and output symbol/field ownership with backend cardinality processing.
Reject absent/inconsistent receipts, unsupported options and source forms erased
by analysis, including enums/initializers/escapes/directives. Require no-string
input. Validate explicit bounds/root conventions; global cards and inferred scopes
are not source semantics. Do not claim independently generated outputs are paired.

Use deterministic error categories and replay, actual pinned-compiler execution
in validation, upstream MIT attribution where material is copied, source matching,
full pinned Lean/kernel/axiom/layer/import checks and IntentBond with independent
semantic review before acceptance. Parser/type/optimizer correctness upstream and
the separately scoped [bounded comparison harness](bounded-comparison.md) solver/search/pin/decode integration remain outside this claim.

Covers:
- `intent~formalization-foundation~1`
- `intent~traceable-contributions~1`

Needs: impl, utest

## Exact bounded candidate comparison

`req~clafer-bounded-comparison~1`

Implement the accepted [bounded comparison harness](bounded-comparison.md) under `scripts/verification/`, tests/fixtures
under `tests/` and any Lean additions under `Clafer/Verification/`. Reuse the [strict same-generation capture/import](resolved-import.md)
and [effective core, finite candidates, semantic bridges and verified checker](structural-checker.md). Preserve S/X/D guards, distinct
UIDs/names/referents, occurrence identities and raw unrelated-class overlap. Apply
the [declaration-disjointness rule](sources.md#declaration-disjointness-clarification) in satisfaction without filtering admission or
enumeration. Preserve existing public roots, package
and dependency directions and all checker/compile promises.

For each supported core, explicit manual bound vector and well-formed candidate,
compare the checker with the same candidate in actual pinned generated Alloy.
Report both discrepancy directions, agreement, unsupported/malformed input,
adapter/decoder failure and inconclusive execution separately. Typed missing or
multiple endpoints, root/cover/key/bound violations remain negative checker
inputs; malformed bytes/endpoints retain their diagnostics. Every SAT result must
decode faithfully before it can count as a match or semantic discrepancy. Support
the unpinned witness-to-checker direction without calling it reverse completeness.

Use the pinned compiler and accepted Alloy 6.2.0/SAT4J/Java 17 profile in
[the contract](resolved-ir-comparison.md). Preserve generated facts; record only
the generated command replacement and added pin/manual-bound predicate. Validate
resolved command AST, every signature bound/exactness flag (including abstract
bounds), fixed options, runtime/build and wall/heap/address-space limits. Justify
integer range independently over generated and added formulas, including relation
tuple counts/unions; inadequate arithmetic or execution failure cannot be UNSAT
agreement. No fallback, inferred-scope adequacy or optimizer correctness claim.

Acceptance of changes to this harness includes actual compiler/backend runs, the
complete pinned Lean/kernel/axiom/layer/import validation, IntentBond source matching and independent semantic
review of all eight [bounded comparison harness](bounded-comparison.md) criteria. Required CI must fail unresolved harness errors;
no missing-tool skips, scope weakening or substitution of documentation checks
for executable acceptance applies.

Covers:
- `intent~formalization-foundation~1`
- `intent~traceable-contributions~1`

Needs: impl, utest

## Candidate and Alloy representation fidelity

`req~clafer-alloy-representation~1`

Specify and independently review the [candidate/Alloy relation](bounded-comparison.md).
Equality-pin complete signature extents and every complete binary field, including
empty relations, using receipt-declared symbols/owners/arities and distinct
quantified variables rather than added subtype signatures. Preserve shared
inherited objects and each reference-head occurrence. Justify the virtual root,
top-level containment, used objects and every classified auxiliary; unknown
auxiliaries are unsupported. Decode under only reviewed object/link bijections
and validate witnesses against the original candidate, not endpoint-reduced data.
Keep the stable unrelated-overlap candidate and require `agree_violates` under the [declaration-disjointness clarification](sources.md#declaration-disjointness-clarification),
without changing its exact pin or representation. Distinguish intrinsic
generated-model restrictions from adapter/domain/bitwidth
failures before reporting a discrepancy. State the external trust assumptions;
serialization roundtrips and trace links alone do not establish this relation.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, utest

## Bounded search and deterministic counterexample replay

`req~clafer-comparison-replay~1`

Supply the contract's E1–E14 boundary cases, first repeated-target sets/bags, then
nesting, empty/zero/optional/exact/bounded/unbounded finite counts, groups and
selected inheritance/abstract cases. Run a small fully enumerated finite domain
and seeded candidates; document generator validity/distribution, precise domain,
renaming, coverage and shrinking. Exhaustiveness requires all specified membership
subsets/typed tables or a justified complete symmetry reduction and all cases
completed. Keep requested/admitted/completed denominators, interruptions, unsupported
inputs and execution failures. Neither SAT-witness enumeration nor sampled success
establishes both-direction completeness or unbounded correctness.

Detect three controlled injected defects: omitted set uniqueness, collapsed
duplicate bag occurrences and changed/dropped cardinality. Retain minimal
deterministic replays and identify these as mutations, not compiler allegations.

Use strict `clafer-structural-comparison/v1` artifacts with duplicate-key/version
rejection, raw source/IR/Alloy/core/candidate/pin/command/witness hashes, exact
bounds/options/versions/seeds, observed verdicts, null stages not run, diagnostics,
limits/completeness and replay commands. Manifest references are acyclic; results
and outputs cannot change input identity. Save execution evidence externally;
keep licensed stable regression fixtures in tests and no diaries in living docs.

Replay requires no LLM and validates its inputs/source and runtime identities.
Record the actual checkout commit in `lean_commit`, or `null` when the source
root has no `.git` metadata. Never substitute a parent repository's commit.
Absent Git metadata does not waive complete `source.json` byte hashes, manifest
input hashes or replay source/runtime checks; corrupt metadata and Git execution
failures remain execution errors. No automated upstream issue or comment posting
is part of the harness.

Covers:
- `intent~formalization-foundation~1`
- `intent~traceable-contributions~1`

Needs: impl, utest

<a id="complete-resolved-appendix-f-integration"></a>

## Complete resolved Appendix 6 integration

`req~clafer-appendix-f-complete~1`

Represent every printed declaration and c01–c12 conjunct of SoSyM Appendix 6
PDF p.34 in one resolved/defaulted input, including the final dual, extraDisplay
and large selections. Organize the case study under `Clafer.Examples.Telematics`
with module names describing their roles. Distinguish the full model from its
structural projection, expression environments and `FormalCD.Telematics`'s
Figure 21 model; appendix numbering belongs in source citations.
Reconcile the visually checked source inventory with
actual owner/position attachments, repeated size identities, all seven super
edges, five abstract families and three xor groups. Reuse the accepted source
elaboration, accepted source corrections and inherited-field/group decisions
without replacing or omitting a body.
Prove the input contract, real positive-map support, generated structural MCS
validity, gluing incidence/metadata/default obligations and final `FormalCD` validity.
Keep the structural MCS distinct from the augmented zero-arrow bank.

Construct a concrete nonempty satisfying configuration with two ECUs and two
displays per ECU, correct server/parent and master relationships, no cache and
all final selections. Realize the primitive integer head as all mathematical
integers with unrestricted 0..* bounds and actual root containment; retain
mandatory 1..1 version/server fields and finite counted nonprimitive collections.
Derive numeric definedness from actual navigation and bounds. Discharge all
hypotheses of `Compile.ConstraintMeaning.whole_model` for this same configuration
and its canonical descent into the exact generated/glued diagram. Neither a
source-truth-only theorem nor an assumed correspondence meets this requirement.

Document remaining elaboration assumptions and finite-evaluation boundaries
in [the full-model contract](telematics.md). This requirement extends the selected
interfaces above; it does not rename representative/subset proofs into full-model
acceptance, claim a finite entire interpretation or broaden the [finite structural checker](structural-checker.md).

Covers:
- `intent~formalization-foundation~1`
- `intent~traceable-contributions~1`

Needs: impl, proof

<a id="complete-appendix-f-rejection-witnesses"></a>

## Complete Appendix 6 rejection witnesses

`req~clafer-appendix-f-rejections~1`

Supply focused negative witnesses for zero/two xor selections, wrong display
count, forbidden cache, wrong server/parent relationship and lower display
version. Identify the violated obligations of the complete resolved model and
connect failures to actual attachments/generated predicates. Coupled failures
are permitted; independent isolation requires its own proof. Preserve sensitive
operator witnesses for c01/c05/c07/c08/c09, including implication vacuity even
where the positive final selection makes a branch vacuous.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Reusable span and navigation laws

`req~reusable-span-laws~1`

Expose the span-only representation and navigation laws in DPGraph, independently
of FormalCD and Clafer. Derive exact-one link multiplicity from totality and
single-valuedness, identity-inclusion normalization, functional composite-fiber
multiplicity preservation and two-component functional keys. Retain arbitrary
object/link universes in the general span lemmas. Ambient navigation and join
must explicitly reduce original spans, preserving the underlying link carriers;
set images do not count parallel links twice. Singleton-image conclusions require
the stated link hypotheses. Finite count comparison must agree with embedding-based
InRange under a local Fintype assumption, including empty fibers and unbounded
upper limits, without imposing finite carriers on generic models.

These are derived laws of SoSyM Appendix 2 mappings/composition, Table 3 and
Appendix 1, reused by Appendix 4 constraint meanings.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Exact declaration-image semantics

`req~dpgraph-declaration-image~1`

Provide model-satisfaction equivalence when the target declarations are exactly
the translated image of the source declarations under a graph map. Support
indexed banks with repeated formulas and collisions after translation; retain full
graph bindings, including isolated vertices. The theorem must require the exact
image hypothesis, not merely declaration preservation. Reuse the general law in
Clafer group and inherited-realization gluing proofs. Keep independent semantic
universes and preserve the counterexample to reflection with extra target
obligations. This is a derived Appendix 2 satisfaction law (legacy B.5).

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Reusable referent graph construction

`req~dpgraph-referent-image~1`

Construct the graph of used vertex and arrow referents through Quiv/Prefunctor,
from endpoint-indexed occurrences with explicit referent assignments. Equal arrow
referents must have equal endpoint referents. Identification uses referent equality,
not names or common endpoints; permit noninjective vertex labeling and preserve
distinct parallel-arrow referents. Transport an indexed formula bank to its exact
declaration image and supply a declaration-preserving labeling morphism. Impose
no naming, finite-carrier or default policy and claim no global pushout existence.
Clafer MCS gluing must reuse this construction while retaining its own role and
resolved-identity obligations. Source: Appendix 2 Definitions 6–10 and §6.2.5.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Reusable FormalCD metadata descent

`req~formalcd-referent-descent~1`

Descend names, predefined annotations and map modes along a referent graph only
when they are constant on its identification fibers. Derive RawOver.WellFormed
from explicit naming, referent-level predefined uniqueness and source-bank
completeness of ordinary and inclusion defaults. Preserve the exact declaration
image: insert no defaults and derive no model-existence claim. Support the existing
small compatible vocabularies and registry without importing Clafer. Clafer must
supply its metadata/origin adapter and reuse the generic validity proof.
Source: SoSyM §§6.1.1–3 and 6.2.5.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof

## Reusable explicit integer realization

`req~formalcd-integer-realization~1`

Provide explicit integer interpretation data in FormalCD independently of the
Figure 21 example and Clafer syntax: an injective Int encoding into an ambient
object type, a decoder inverse on that encoding, and its image domain. Partial
extraction succeeds exactly for an encoded singleton; empty, multiple-object and
off-domain sets are undefined. Prove uniqueness, success/failure equivalences and
correspondence between the complete domain and mathematical Int. Reuse these
definitions in the guarded VC extension and Clafer IntegerBinding; preserve
compatibility names. Neither registry annotations nor extraction impose a finite
integer domain, and a general primitive-domain framework remains outside scope.
Source: SoSyM §6.1/Figure 21 and the selected Appendix 4 primitive bridge.

Covers:
- `intent~formalization-foundation~1`

Needs: impl, proof
