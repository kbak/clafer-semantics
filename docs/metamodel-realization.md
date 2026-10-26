# Metamodel realization contract

`impl~metamodel-realization-assessment~1`

The [realization investigation](https://github.com/kbak/clafer-semantics/issues/100)
implements a canonical encoding of CD **syntax**, an exact restricted
whole-metamodel satisfaction theorem, reconstruction, and the particular
metamodel's semantic self-instance. This does not prove that the represented
source CD has a model or establish general source-language compilation. The
[source assessment](sources.md#metamodel-realization-and-translational-semantics)
records historical translation identities and unresolved differences.

Covers:
- `req~supporting-source-research~1`

<a id="proposed-statement"></a>

## Statement

Fix a compatible `Vocabulary V`, registry `R`, and `D : CDOver V R`.
Write `G = D.carrier`, `σ = V.signature`, and
`F_D = {φ : DPGraph.Formula σ G // φ ∈ D.declarations}`.
These are the **effective declarations**, including required defaults, with
one object per formula value; duplicate authored occurrences are not extra
objects. Let `E(H) = Σ a b : H, (a ⟶ b)` and, for each formula `φ`, define

```text
Aφ = E(σ.arity φ.symbol)
bφ(a) = (φ.binding.obj a.source, φ.binding.obj a.target, φ.binding.map a.arrow)
```

The following hypotheses concern source syntax only:

```text
Supported(D) := ∀ φ ∈ D.declarations, Nonempty Aφ

Separated(D) := ∀ φ ψ, φ ∈ D.declarations → ψ ∈ D.declarations →
  φ.symbol = ψ.symbol →
  (∃ e : Aφ ≃ Aψ, ∀ a, bφ(a) = bψ(e(a))) → φ = ψ
```

The quantification in `Separated` ranges over two declared formulas. Its
equivalence compares **bags**, including repeated arrow values; it need not
preserve argument positions. The conclusion is equality of full formulas,
including every vertex assignment. Neither finiteness nor absence of isolated
vertices is required. The hypotheses apply only to declared formulas, not every
symbol in `σ` or every possible binding. An empty declaration set is admissible.

`encode D` and `context D` below are constructed without either hypothesis.
`Realization.model_iff` proves the following characterization, with
`Metamodel.interpretation` and all built-in meanings unchanged:

```text
(Metamodel.interpretation (context D)).IsModel
    Metamodel.diagram.toDPGraph (encode D)
  ↔ Supported(D) ∧ Separated(D)
```

Its forward direction is a necessity check for this exact encoding; its reverse
direction is the restricted realization theorem. Reconstruction holds even
when the two hypotheses fail. Neither target `IsModel`, `NameDiscipline` nor
`ArityDiscipline` is an input. `D.wellFormed` supplies naming/default facts;
the additional two hypotheses supply exactly total `args` and the literal key.

The semantic target here is the existing `DPGraph.Interpretation.IsModel` of
`Metamodel.diagram.toDPGraph`. As [FormalCD semantics](../FormalCD/Semantics.lean)
states, this does not itself enforce concrete primitive/singleton domains from
registry metadata. Nor does it interpret the represented diagram's predicates
as truths about its objects: those predicates are represented as syntax tokens.
A stronger predefined-domain or source-satisfiability theorem needs a different
explicit statement.

## Canonical encoding and external data

`Ambient D` is an inductive tagged sum of `G`, `E(G)`, `F_D`, `σ.Symbol`,
and `String`, in the maximum of the input vertex, arrow, symbol, arity and
registry universes. Its subset and link types fit that same universe.
No type of all types, equality of universes, or resizing axiom is needed.
Tags separate classes, maps, formulas, symbols and strings. Subclass membership
reuses the same ambient object; it never retags that object.

| Metamodel node | Exact extent in `U_D` |
| --- | --- |
| Class | All tagged vertices of `G` |
| Map | All tagged total arrows `E(G)`, keeping endpoints and arrow identity |
| Classifier | Union of Class and Map |
| Incl | Map objects whose source metadata mode is `.inclusion` |
| Predef | Class objects with `D.predefined c = some i` |
| SING / Dom | Those Predef objects whose identifier has singleton / primitive kind |
| String | All tagged strings |
| PredefStr | Tagged `R.name i` for **all** registry identifiers, including unrealized ones |
| Formula | Exactly tagged `F_D` |
| Signature | All tagged symbols of `σ`, including unused ones |

The seven inclusions use the canonical identity-valued span from the
indicated subset. `name`, `predefName`, `so`, `ta`, and `pred` use function
spans with one link per source object, returning the source name, canonical
predefined name, source endpoint, target endpoint, and formula symbol
respectively. The two name arrows remain different arrow identities.

For `args`, `arguments D` is an indexed family over the Formula extent;
its index at `f` is `Aφ` for `φ = (formulas D).symm f`. Its span link type is
therefore canonically equivalent to `Σ φ : F_D, Aφ`. The target is tagged
`bφ(a)`. `argumentIndex` proves the exact fiber equivalence and
`argumentIndex_target` proves its agreement with the span. Repeated images have
distinct links; no deduplication or support arrows are introduced.

`names D` builds `NameContext` from the tagged string embedding, source class/map names,
and `D.predefined` on class objects. Its functions have arbitrary fixed values
off the relevant tags. Registry names need not be injective; predefined
**identifier** uniqueness is the existing source obligation.
`arities D` builds `ArityContext` from the tagged symbol/vertex/arrow embeddings. At the
canonical arity diagram, the descriptor returns `Candidate.ofFormula φ` and
the canonical args-fiber index. This records every arity vertex, including
isolated vertices, as well as every indexed arrow.

`context D` also defines `Context.describe` on arbitrary arity diagrams. It
noncomputably tests equality with the canonical arity diagram,
transports its descriptor on equality, and returns `ArityDescriptor.missing`
otherwise. This uses ordinary classical choice/equality, not an assumed model
proof. `context_describe` proves reduction to the canonical descriptor.
The encoded map is constructed first, independently of the context, so this
definition is not recursive through satisfaction. A more reusable descriptor
decoder is possible but is not needed for the first theorem.

The bare Figure 21c graph omits the registry identifier assignment, full vertex
bindings, occurrence-to-position labels and ordinary-versus-bag metadata.
`ArityDescriptor`, `NameContext` and `ModeData` retain these fields explicitly.
`modes D` retains the full `MapMode` function externally; Incl membership alone cannot
recover it, since a bag arrow can also have an explicit setValued declaration.
It does not retain the whole original `D` as an unexplained reconstruction field.

## Faithfulness and all effective declarations

`vertices`, `arrows`, `formulas` and `symbols` give bijections between source
values and the Class/Map/Formula/Signature extents; `name_discipline` and
`arity_discipline` check the endpoint, name and pred maps. Decoding a represented formula through its descriptor and
[`Candidate.formulaEquiv`](../FormalCD/Metamodel/Binding.lean) returns that exact
full formula. Consequently the decoded declaration set is exactly
`D.declarations`, not a subset, closure, or bag quotient. With the explicit
identifier and mode data, reconstruction recovers the source `RawOver` on the
fixed carrier, including its effective defaults. `decodeRaw` takes only the
encoded map, context and mode data; `decode_encode` proves equality to the source.
`candidate_roundtrip` and `decoded_declarations` prove the formula/set claims. Proof fields are not extra data.
No recovery from an arbitrary bare metamodel graph is claimed.

The obligation inventory is the actual
[`Declaration`](../FormalCD/Metamodel/Basic.lean) enumeration, not just the drawn
key and ad fragment:

| Cases | Count | Checked derivation |
| --- | ---: | --- |
| `predefStrIn`, `classIn`, `mapIn`, `predefIn`, `singIn`, `domIn`, `inclIn` | 7 | Source projection is bijective and target preserves ambient identity in each inclusion span |
| `nameSet`, `predefNameSet`, `soSet`, `taSet`, `predSet` | 5 | Function-span link endpoint pairs are jointly injective |
| `nameTotal`, `predefNameTotal`, `soTotal`, `taTotal`, `predTotal` | 5 | One link for every source object |
| `nameSingle`, `predefNameSingle`, `soSingle`, `taSingle`, `predSingle` | 5 | Source projection of each function span is injective |
| `argsTotal` | 1 | Canonical fiber equivalence gives precisely `Supported(D)` |
| `classifiersCover`, `classifiersDisjoint` | 2 | Classifier is the disjoint tagged union of Class and Map; use the accepted common-target disjointness meaning |
| `predefinedCover`, `predefinedDisjoint` | 2 | Each realized identifier has exactly one of the two `PredefinedKind` constructors |
| `key` | 1 | Singleton pred fibers recover symbol equality; args bag equivalences recover precisely the equivalence in `Separated(D)` |
| `nd` | 1 | Source naming, unique identifiers and inclusion names from `D.wellFormed`; extent equations by construction; explicit span isomorphism for the name restriction square |
| `ad` | 1 | Exact class/map/symbol extents, incidence from typed arrows, `Candidate.ofFormula_valid`, and complete args indexing with singleton pred fibers |

These sum to 30. The name-square isomorphism must preserve links along
`predefIn ; classIn ; name` and `predefName ; predefStrIn`, not just compare target
strings. The other 28 cases do not depend on `Supported` or `Separated`.
The source's required inclusion/set defaults are encoded as formula objects;
this is distinct from proving the target metamodel's own seven/five defaults.
Neither step proves that those source formulas hold in a model of `D`.

## Assessment for the particular metamodel

For `D = Metamodel.diagram`, [Self.lean](../FormalCD/Metamodel/Realization/Self.lean)
checks the following inventory and applies `model_iff`.

| Source formula group | Formula count | Argument arrows per formula | Separation within the same symbol |
| --- | ---: | ---: | --- |
| inclusion | 7 | 1 | Seven different inclusion arrow identities |
| setValued | 5 | 1 | Five different ordinary arrow identities |
| total | 6 | 1 | Six different arrows, including args |
| singleValued | 5 | 1 | Five different arrows |
| cover 2 | 2 | 2 | `{classIn,mapIn}` differs from `{singIn,domIn}` |
| disjoint 2 | 2 | 2 | The same two distinct bags, now under the disjoint symbol |
| key 2 | 1 | 2 | Only the `(args,pred)` binding is declared |
| nd | 1 | 9 | Only `nameBinding` is declared |
| ad | 1 | 4 | Only `arityBinding` is declared |

`arityEdges_complete` and `arityEdges_nodup` check all indexed arrows.
`fingerprint_injective` checks that symbol plus arrow support distinguishes
these particular labels; `fingerprint_eq` shows every bag equivalence preserves
that coarser fingerprint. This proves `metamodel_separated` without changing the
generic bag semantics. `metamodel_supported` supplies a concrete arrow for each
declared formula. `declaration_injective`, `thirty_formula_objects` and
`forty_six_argument_links` certify 30 distinct formula values and 46 args links. Although
the vocabulary contains zero-arrow arities such as `cover 0`, none is declared
here. The theorem must not impose positive support on the whole vocabulary.

Class and Map have 11 and 13 objects, Classifier 24, Incl 7, Predef and SING one
each, and Dom none. The SING object represents the source vertex `Node.sing`;
it is neither that metaclass nor a universe of singleton types. Signature and
String remain the complete chosen domains, so this is not a wholly finite
metamodel instance merely because its declaration inventory is finite.

`self_instantiation` and `selfModel` give a model of
`Metamodel.diagram.toDPGraph` under
`interpretation (context Metamodel.diagram)`. This is bounded, context-dependent
self-instantiation in the existing DP semantics. It is not a universe fixed
point or an interpretation of arbitrary metamodels in one universal context.

## Source-to-obligation comparison

The [source identities and historical audit](sources.md#historical-translation-evidence)
separate the early reports, July 2011 snapshot, and audited 0.5.3 compiler.
The [current 0.5.4 capture assessment](resolved-ir-comparison.md#compiler-054-compatibility)
does not extend these metamodel or expression claims.
The [Diskin assessment](sources.md#generalized-sketches-and-model-reduct-coherence)
retains the limits of inspected browser statements and missing source pages.

| Evidence | Obligation it informs | Limit or unresolved difference |
| --- | --- | --- |
| SoSyM §6.1.3/Figure 21c, PDF pp.19–21; B.4 Definition 8, p.31 | Exact declaration objects, full bindings, indexed args, naming, key and totality | Argument indexing in ad does not strengthen the literal bag key; arrow shorthand omits isolated vertices |
| Historical CS846 §4.3–4.4/Figures 12–13, PDF pp.5–7 | Resolved context, ownership, inherited membership and explicit generated facts must enter any language-preservation theorem | It does not encode the generic DP-graph formula metamodel or establish its key |
| July 2011 `Alloy.hs`: `genClafer`, `genRelations`, `genParentConst`, `genGroupConst`, `genLExp`, `genDecl` | Distinguish relation-valued reference optimization, parent constraints, ordered expressions and scoped quantification | Optimization and intended meaning need comparison; a code path is not a preservation proof |
| Audited 0.5.3 `Intclafer.hs`, `ResolverName.hs`, `Alloy.hs` at `15adb221…` | Separate declaration UIDs, expression occurrence IDs, operands, lexical binding and context paths | No existing expression-comparison harness coverage; occurrence IDs are not DP formula identity |
| Wolter–Diskin 2007 §3 Definitions 6–7/Remark 4; §4 Definition 11/Proposition 3 | Ordinary signatures and restriction by precomposition fit the delivered API | Dependency-category structure is explicitly set aside there |
| 2007 §5 Definition 14/Remark 8/Theorem 2 | Strongly persistent extension needs a section of restriction; pushout extension uses agreement on the overlap | Noninjective identifications cannot extend models that distinguish identified elements |
| 2007 §7 Definitions 18–19/Proposition 5; Diskin–Wolter 2008 §4.2–4.3 | Typed-instance pullbacks require isomorphism-closed meanings and coherence | This construction stays with maps into the bounded semantic graph; it supplies no indexed/fibred equivalence |
| 2008 Definitions 4.1/4.5/4.7; Example 4.8 | Dependency closure and interpretation consistency would need explicit proofs | Its functional key requires total single-valued legs; args is intentionally multivalued here |
| Existing `satisfies_translate`, `Pushout.modelEquiv`, `ConstraintMeaning.whole_model` | Reuse formula transport and the selected preservation bridge under their actual hypotheses | None constructs this reification or proves unrestricted source-expression preservation |

In particular, dependencies from key to total/singleValued legs cannot be
imported from the functional-key example into the generic bag key. Their
semantic consistency would have to be proved; the retained repeated-argument
witness already rules out singleValued args as a general consequence.

For gluing `q : S → T`, a model `m` of `S` descends only if a map `n` can be
constructed with `q ; n = m`. An exact translated declaration image then lets
`satisfies_translate` establish the target model. Agreement is on semantic
objects **and arrows** (spans, with the necessary endpoint transports), not
just names or related objects. If `q` identifies two vertices whose model
extents differ, factorization is impossible. Arbitrary isomorphic spans do not
supply the strict equality needed by the existing API without a further
coherence construction. A supplied pushout and compatible models already have
`modelEquiv`; do not assume concrete Clafer gluing is that pushout.

## Implementation and remaining scope

The restricted theorem covers the particular metamodel. An enriched metamodel
remains a separately scoped option for universal realization: it would need to
represent vertex assignments and argument positions and accommodate empty arrow
arities. Neither dummy arrows nor a quotient by bags repairs the stated contract.
Adding dependency closure alone repairs neither obstruction.

| Module | Responsibility |
| --- | --- |
| [Encoding](../FormalCD/Metamodel/Realization/Encoding.lean) | Tagged extents, exact spans, source-only `Supported`, `SameArguments`, `Separated` |
| [Context](../FormalCD/Metamodel/Realization/Context.lean) | Full candidates, args indexing, arbitrary-diagram fallback, nd/ad proofs |
| [Correctness](../FormalCD/Metamodel/Realization/Correctness.lean) | Bag/fiber correspondences, all thirty cases, `model_iff` and `model` |
| [Reconstruction](../FormalCD/Metamodel/Realization/Reconstruction.lean) | Explicit `ModeData`, independent `decodeRaw`, candidate/declaration/raw roundtrips |
| [Self](../FormalCD/Metamodel/Realization/Self.lean) | Complete arity inventory, support/separation, counts, self-instance and reconstruction |
| [Examples](../FormalCD/Metamodel/Realization/Examples.lean) | Whole-model positive, empty, zero-arrow and isolated-binding collision cases; repeated-link and metadata boundaries |

The [proof index](formalcd-trace.md#restricted-realization-and-reconstruction-proofs)
links the distinct requirements for realization, self-instantiation and boundary
witnesses. Existing shape, discipline, formula-identity and bounded syntactic
self-description promises remain unchanged. Validation uses the full pinned
[workflow](../CONTRIBUTING.md#setup-and-checks), including kernel replay,
axiom/layer audits and independent imports. Passing automation does not replace
semantic review of the precise theorem and source correspondence.

A global-context or typed-instance bridge, predefined-domain realization,
enriched metamodel and unrestricted Compile/gluing/expression preservation each
need their own explicit contract. Historical translation differences remain
source questions; this implementation selects no changed language meaning.
