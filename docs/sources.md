# Sources and open decisions

For a concise reading companion, see [SoSyM paper corrections and clarifications](sosym-errata.md).

This map connects the Lean formalization to exact paper passages, accepted
corrections and supplementary evidence. Its claims are bounded by the inspected
sources; it is not a complete literature audit. The
[architecture](architecture.md#roadmap-and-validation-accounting) explains the
implemented results and their proof limits.

Browse the source map by topic:

- **Editions and evidence:** [primary source](#primary-source),
  [locator crosswalk](#published-locators-and-legacy-aliases),
  [supporting sources and licenses](#supporting-sources-and-licenses) and
  [open decisions](#question-dispositions-and-validation-tasks).
- **DPGraph:** [span composition](#span-composition-and-relational-reduction),
  [predicate contracts](#predicate-contracts-and-the-accepted-q8-correction) and
  [generalized sketches](#generalized-sketches-and-model-reduct-coherence).
- **FormalCD:** [structure](#formalcd-structure-and-selected-morphisms),
  [Figure 21c](#figure-21c-metamodel),
  [realization](#metamodel-realization-and-translational-semantics) and
  [Figure 21b](#figure-21b-and-the-accepted-q7-correction).
- **Clafer structure:** [syntax and Shapes](#resolved-2014-clafer-and-individual-shapes),
  [MCS](#figure-23-and-appendix-5-mcs-discipline),
  [Compile](#structural-compile-contract), [gluing](#mcs-gluing-and-the-approved-q4-rule)
  and [declaration disjointness](#declaration-disjointness-clarification).
- **Constraint meaning and models:** [integer extraction](#integer-extraction-and-appendix-6-version-operands),
  [inherited realization](#appendix-6-inherited-realization-clarification),
  [denotation](#independent-constraint-meaning-and-appendix-6-elaboration),
  [preservation](#selected-constraint-preservation),
  [representative models](#representative-compilation-and-gluing) and
  [complete telematics](#complete-appendix-6-model).
- **Verification and reuse:** [compiler audit](#pinned-compiler-compatibility-audit),
  [finite semantics](#finite-structural-candidate-semantics),
  [importer](#pinned-resolved-importer) and
  [shared foundations](#reusable-semantic-foundations).

The decision history is retained in the
[formalization roadmap issue](https://github.com/kbak/clafer-semantics/issues/2) and
[source-audit review PR](https://github.com/kbak/clafer-semantics/pull/40), the
[supporting-source issue](https://github.com/kbak/clafer-semantics/issues/41) and
[assessment PR](https://github.com/kbak/clafer-semantics/pull/43), and the
[graph representation issue](https://github.com/kbak/clafer-semantics/issues/13) and
[design review PR](https://github.com/kbak/clafer-semantics/pull/39).
The [self-description and telematics PR](https://github.com/kbak/clafer-semantics/pull/38)
records the bounded metamodel and Figure 21b implementation. Further source
acquisition remains conditional on a necessary claim lacking adequate evidence.

## Primary source

Kacper Bąk, Zinovy Diskin, Michał Antkiewicz, Krzysztof Czarnecki and Andrzej
Wąsowski, *Clafer: unifying class and feature modeling*, **Software & Systems
Modeling 15, 811–845 (2016)**,
[DOI 10.1007/s10270-014-0441-1](https://doi.org/10.1007/s10270-014-0441-1).
The [publisher record](https://link.springer.com/article/10.1007/s10270-014-0441-1)
dates online publication to 13 December 2014. References to the 2014 language
continue to mean that publication's language, not later compiler extensions.

The primary inspected source is the publisher's personal e-offprint, **37 PDF
pages**, SHA-256
`653fc7868637680c44b6176d8ff643ec20149534fe1681ea4fc4ce636db76f2d`.
Its first two pages are cover/copyright sheets; the article begins on PDF page 3.
It has no printed journal pagination. **PDF page numbers below and in maintained
citations are one-based positions in this exact e-offprint**, including both
cover sheets. The bibliographic range 811–845 is publisher metadata, not the
page numbering displayed in the supplied copy. No per-page journal offset is
asserted without inspecting an issue-paginated PDF. The personal copy remains
outside the repository and is not redistributed.

The [freely accessible author preprint](https://gsd.uwaterloo.ca/sites/default/files/2014-Bak-Clafer-Unifying-Class-Feature-Modeling%28SOSYM%29.pdf)
is an access alternative and the historical source of earlier audits: 34 pages,
SHA-256 `56b1c18e74807fb7646c0e89cb2fc306f4178affb41fee52fcebde09b031b2fb`.
Its printed pages equal its PDF positions. Frozen records keep that identity.
The bounded comparison format `52-S/v1` also retains its original `paper_sha256`
pin: it identifies that historical contract, not the current preferred citation;
changing it would reject existing replay artifacts.

### Published locators and legacy aliases

Main sections and subsections, Figures 1–28, Tables 1–8, Definitions 1–10 and
Theorems 1–3 retain their numbers. Appendices A–F become **1–6**. Appendix
subheadings lose their numbers: there is no printed published “B.4” or “D.4.2”.
For compact existing trace links and source comments, dotted labels such as
`A.1`, `B.4` and `D.4.2` remain **legacy aliases** for the named published
headings below. They do not select the preprint as semantic authority.
Requirement IDs and legacy heading anchors retain their spelling. Model-based
module names are independent of appendix numbering: `Clafer.Examples.Telematics`
formalizes the full model in Appendix 6, while `FormalCD.Telematics` formalizes
Figure 21. The [telematics guide](telematics.md) distinguishes the full model from
its structural projection and expression environments. New citations use
numbered appendices.

| Legacy locator | Published appendix and heading | E-offprint PDF pages |
| --- | --- | --- |
| A; A.1; A.2 | 1, Notation and terminology; Mappings; Shapes and fonts | 28 |
| B | 2, Semantics and syntax of DP-graphs (formal CDs) | 28–31 |
| B.1 | Semantic universe: mappings | 28–30 |
| B.1.1 / Definitions 1–2 | Multi-relations or spans | 28–29; definitions 29 |
| B.1.2 / Definitions 3–5 | Multi-valued functions | 29 |
| B.1.3 / Theorem 1 | Spans and functions together: mappings | 29–30; theorem 30 |
| B.1.4 / Theorem 2 | Set-valued mappings | 30 |
| B.2; B.2.1; B.2.2 | Semantic universe: operations on mappings; (Sequential) Mapping composition; Inversion | 30 |
| B.3 | Semantic universe: configurations of mappings and their properties | 30; predicate catalogue in Table 3 on 13 |
| B.4; B.4.1; B.4.2 | Syntax: DP-graphs; Graphs; DP-graphs | 30–31; Definitions 6–10 on 31 |
| B.5 / Theorem 3 | Syntax and semantics together | 31 |
| C | 3, Clafer concrete syntax | 31–32 |
| D; D.1 | 4, Clafer constraint language; Grammar | 32 |
| D.2 | Name resolution rules | 32–33 |
| D.3; D.3.1; D.3.2 | Type rules; Expressions; Set expressions | 33 |
| D.4 | Semantics | 33–34 |
| D.4.1; D.4.2 | Semantics of expressions; Semantics of set expressions | 34 |
| E | 5, MCS constraints | 34; Tables 5–6 on 22 and 7–8 on 23 |
| F | 6, Full telematics model | 34 |

Tables 5–8 are physically in §6.2.3, despite the published prose still saying
they are in Appendix 5. Cite their table numbers and PDF pages, using Appendix 5
for the short statement that all four constraint families apply. References move
after Appendix 6 (PDF pp.35–37); author biographies are added on PDF pp.36–37.

| Item number(s), unchanged | Preprint page(s), respectively | E-offprint PDF page(s), respectively |
| --- | --- | --- |
| 1, 2, 3–5 | 3, 4, 5 | 5, 6, 7 |
| 6, 7, 8, 9 | 7, 7, 8, 9 | 8, 9, 10, 10 |
| 10–12, 13, 14 | 9, 10, 11 | 11, 11, 12 |
| 15, 16, 17, 18 | 12, 13, 15, 14 | 14, 14, 16, 17 |
| 19, 20, 21, 22, 23 | 16, 16, 17, 20, 21 | 17, 18, 19, 21, 22 |
| 24, 25, 26, 27–28 | 22, 23, 30, 31 | 24, 26, 31, 32 |
| Table 1, 2, 3, 4 | 8, 11, 12, 13 | 10, 13, 13, 15 |
| Tables 5–6, 7–8 | 33, 33 | 22, 23 |

The following spans locate the listed passages; enclosing section numbers mark
their opening text, with later subsections listed separately.

| Section opening / subsection(s), unchanged | E-offprint PDF pages |
| --- | --- |
| 1; 2; 3 / 3.1 / 3.1.1; 3.1.2 | 3–5; 5–6; 6–7; 7–8 |
| 3.2–3.3; 4 / 4.1; 4.2 / 4.2.1–2; 4.2.3; 4.3 | 8; 8–9; 9; 10; 10–11 |
| 5; 5.1; 5.2; 5.3 / 5.3.1; 5.3.2–5 | 11; 12–14; 14; 14; 15 |
| 5.4–5.5; 5.6; 6 / 6.1 / 6.1.1 | 17; 17–18; 18–19 |
| 6.1.2; 6.1.3; 6.2 / 6.2.1; 6.2.2 | 19–20; 20–21; 21; 21–22 |
| 6.2.3; 6.2.4–5; 6.3; 7; 8; 9 | 22–23; 23; 24; 24–26; 26–27; 27–28 |

### Edition comparison and semantic disposition

Comparison of the complete extracted texts, the numbered-item inventory and
visual checks of the formalization's diagrams, tables, rules and full telematics
model found **no substantive correction requiring a change to the current Lean
semantics**. Text extraction alone is not reliable for mathematical glyphs or
embedded figure contents. The checked formal material includes Tables 2–8,
Figures 8, 16, 18, 21–23, 27–28, Definitions 1–10, Theorems 1–3, the constraint
rules and the Appendix 6 declaration/constraint inventory. This is an edition
comparison, not a new proof of every mathematical claim in either paper.

The publisher corrects spelling (including “moprhisms” in Definition 6) and the
duplicated “from” in the universal-quantification explanation, with no change to
the associated definitions or equation. The accepted span-composition, common-target
disjointness, abstract-head, guarded-version and seven-association ownership
corrections all remain necessary. The version prose error is now on PDF p.18,
while Figure 21a is on PDF p.19. The intersection symbol in Appendix 4 remains
`∩`; the mixed evaluator subscripts and arithmetic-rule notation also remain.
The [reader companion](sosym-errata.md) gives the corrected readings and their
implementation links. Existing clarification decisions retain their status.

### Foundation correspondence

Appendix B.1 Definitions 1–5 and Theorems 1–2, B.2.1–2 (with the adopted
correction below), B.4 Definitions 6–10 and the abstract restriction argument of
B.5 Theorem 3 ground this slice:

| Source | Lean correspondence |
| --- | --- |
| B.1 Definitions 1–5, mappings and equivalences | `Span`, `Span.Iso`, `IndexedFamily`, `IndexedFamily.Equivalence`, `Span.toFamily`, `IndexedFamily.toSpan`, `Span.red`, `Span.ofRelation` |
| B.1 Theorem 1, relation correspondence | `Span.red_toFamily`, `IndexedFamily.red_toSpan`, `Span.red_ofRelation` |
| B.1 Theorem 2, set-valuedness | `Span.jointlyInjective_iff_fiberwise`, `Span.jointlyInjective_iff_iso_relation` |
| B.2.1–2, mapping operations | `Span.comp`, `IndexedFamily.comp`, `Span.leftUnit`, `Span.rightUnit`, `Span.associator`, `Span.inverse`; corrected comparison is detailed below |
| Definition 6, graphs and graph morphisms | Mathlib `Quiver`, `Quiv`, `Prefunctor`; [representation decision and dependency tradeoff](architecture.md#dp-graph-representation-decision) |
| Definition 7, signature | `DPGraph.Signature` |
| Definition 8, formula | `DPGraph.Formula` |
| Definition 9, DP-graph | `DPGraph` |
| Definition 10, DP morphism | `Formula.translate`, `Hom`, `Hom.id`, `Hom.comp`, their laws and `DPGraph.category` |
| B.5, satisfaction and Theorem 3 | `Interpretation.Satisfies`, `IsModel`, `isModel_reduct`, `Model`, `reduct` and its laws |

The finite arrow-list notation is shorthand, not a generic finiteness restriction.
Formula arguments are graph maps. The structural examples introduce syntax-only
names; `SemanticsExamples` separately supplies an illustrative interpretation.

The abstract interface for B.5 takes each symbol's meaning to be a set of its
arity diagrams in a fixed semantic graph. A formula holds when its binding
composed with a candidate model belongs to that set. A target model restricts along `F : S → T` because `F` sends every
source declaration to a target declaration; graph-map associativity identifies
the two evaluations. This proves the abstract reduct direction of Theorem 3,
without extra closure or invariance assumptions on predicate meanings.

Concrete
span predicates use the selected contracts below in a bounded graph of subsets
and spans; no all-universes SetMap is asserted. The formula-level
satisfaction equivalence does not assert whole-model reflection.
[Trace artifacts](dpgraph-trace.md) name the actual declarations and proofs.

## Supporting sources and licenses

Mathlib is pinned to [56a005855ea17e0b0958f73ec801ae140b0a1679](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679)
(v4.35.0), with the same Lean v4.35.0 pin. Inspected APIs:
[Quiver.Basic](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Combinatorics/Quiver/Basic.lean),
[Quiver.Prefunctor](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Combinatorics/Quiver/Prefunctor.lean),
[Category.Basic](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Category/Basic.lean),
[Category.Quiv](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Category/Quiv.lean),
and [Equiv.Basic](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Logic/Equiv/Basic.lean).
Mathlib's Apache-2.0 license was checked; it is consumed as a pinned dependency,
without vendoring its source. Paper definitions are independently formalized with
citations; publication text and figures are not reproduced.

The supporting comparison uses the inspected author-uploaded Diskin & Wolter (2008),
[DOI 10.1016/j.entcs.2008.10.041](https://doi.org/10.1016/j.entcs.2008.10.041),
[full-text rendering](https://www.researchgate.net/publication/220368840_A_Diagrammatic_Logic_for_Object-Oriented_Visual_Modeling).
The upload is headed ACCAT 2006; use its numbered statements rather than
assuming the journal's pagination. The comparison below identifies the relevant
syntax and semantics separately. A downloaded PDF identity for this upload has
not been established; browser section excerpts are distinct from a complete file.
The inspected Diskin, Easterbrook & Dingel (2008) §3 formal-CD/mapping discussion
and §5 association examples support retaining link identity and distinguishing
extensional and navigational views; the full-text identity is recorded below.

The audit limits for the other requested sources are specific:

| Source | Available evidence | Remaining audit |
| --- | --- | --- |
| Diskin & Kadish (2003), *Variable set semantics for keyed generalized sketches*, [DOI 10.1016/S0169-023X(03)00047-8](https://doi.org/10.1016/S0169-023X(03)00047-8), pp. 1–59 | Bibliographic record, abstract and publisher section snippets; inspected scholarly indexes supplied no downloadable copy | Full text not obtained; technical object-identity definitions remain unaudited. The criticality assessment below defers further acquisition unless an active claim needs them and no inspected primary alternative establishes it. The abstract does not select Clafer label identity. |
| Diskin, Kadish, Piessens & Johnson (2000), [Universal Arrow Foundations for Visual Modeling](https://researchers.mq.edu.au/en/publications/universal-arrow-foundations-for-visual-modeling/), pp. 345–360, [DOI 10.1007/3-540-44590-0_30](https://doi.org/10.1007/3-540-44590-0_30) | User-recovered Google Books previews: pp. 345–348, 350, 352–357 and 359, as a two-page PDF and ten page images. Page 345 identifies the title, authors and Diagrams 2000 / LNAI 1889 publication. | Partial source acquired: pp. 349, 351, 358 and 360 are missing. Only the recovered passages are assessed. Further acquisition is conditional on a necessary claim, as recorded below; this is not a complete-paper audit. |

The [bounded library assessment](#lean-library-assessment) identifies reusable
foundations, without establishing a ready-made generalized-sketch dependency or
proving that none exists. The maintained Haskell
compiler does not select the formalization's semantics; supplementary use must pin a commit,
check licensing and distinguish post-2014 constructs. Acquired publications
remain outside the repository.

### Universal Arrow Foundations: partial-source assessment

Google Books previews provided a partial copy of *Universal Arrow Foundations
for Visual Modeling* after author links and other full-text searches did not
yield a complete copy. The available material covers pp. 345–348, 350, 352–357
and 359; pp. 349, 351, 358 and 360 remain unavailable.

The inspected passages inform the comparisons of keys, names and marked arities
below. Detailed provenance and file identities are retained with the research
evidence tracked by the [supporting-source assessment issue](https://github.com/kbak/clafer-semantics/issues/41).

| Inspected locator | Finding and applicability boundary |
| --- | --- |
| §2.1, p. 348 | The separating-family example uses an injective tuple map of ordinary functions. It motivates the derived `key_ofFunction_iff` and `key_total_singleValued_iff` in [FunctionalKey.lean](../DPGraph/Predicates/FunctionalKey.lean), whose span formulation explicitly assumes totality and single-valuedness. It does not identify the 2000 set-valued notation with unrestricted SoSyM bags. Table 1 is not among the recovered pages. |
| Predicate-declaration discussion, p. 350 | Bindings are incidence-preserving graph maps. Arity shapes may themselves carry predicate markers, and bindings must preserve them. This supports the [hierarchical-arity alternative (A2)](architecture.md#design-a2); it is not an identification with the 2008 predicate/dependency category or the delivered ordinary graph arities. |
| §3.1–3.2, pp. 352–353 | Class structure is expressed by outgoing arrows and constraints. Optional/multivalued references use pm-functions with separate single-valuedness and totality markers. The set-valued notation does not provide the multiplicity-bearing links of SoSyM B.1; these examples do not replace the span interpretation. |
| §3.3, pp. 353–354, Figure 1; §3.5, p. 356 | Repeated marriages motivate a key on `(wife, husb, mdate)` rather than the spouses alone. [Examples/FunctionalKey.lean](../DPGraph/Predicates/Examples/FunctionalKey.lean) checks two marriages with equal spouse values and distinct dates: `Remarriage.spouses_not_key` and `Remarriage.spouseDate_key`. This is a finite witness, not an unrestricted marriage identity theorem. Page 354 distinguishes unconstraining names from semantic markers for predefined domains, without choosing Clafer's same-label congruence ([Q4](sources.md#mcs-gluing-and-the-approved-q4-rule)). |
| §3.4, pp. 354–355, Figure 2; §3.5, pp. 356–357 | Association-class and qualification visualizations abbreviate explicit sketch structures. This supports preserving underlying bindings rather than inferring identity from a drawing; no general endpoint-based link identification follows. |

The missing pages interrupt Table 1 and the category-theory discussion in §2.3,
and omit part of the conclusion and references. The recovered material does not
complete a universal-arrow foundation or pullback-coherence audit. The broad
expressiveness discussion in §4, p. 357, is not a theorem delivered by this library.

### Additional Diskin sources and applicability

Accessible alternatives support particular questions; they do not establish the
unread 2003 definitions or missing 2000 passages, or settle Clafer's label congruence ([Q4](sources.md#mcs-gluing-and-the-approved-q4-rule)).

| Inspected source | Applicable statements and limits |
| --- | --- |
| Wolter & Diskin, *From Indexed to Fibred Semantics — The Generalized Sketch File*, Bergen report 361 (2007), [author-uploaded full-text rendering](https://www.researchgate.net/publication/264922657_From_Indexed_to_Fibred_Semantics_--_The_Generalized_Sketch_File) | §3 Definitions 6–7 use an ordinary signature; Remark 4 explicitly sets aside the dependency-category extension. §4 Definition 11 / Proposition 3 give models into a semantic universe and precomposition reduction. §7 Definitions 18–19 / Proposition 5 give isomorphism-closed meanings and pullback reduction, with canonical coherence at the section opening. §6 treats the graph semantic universe; Remark 13 flags additional identity loops in that construction. This is relevant background for [signatures and arities (A2)](architecture.md#design-a2), not a proved bridge for the delivered bounded span semantics. Browser-rendered statements were inspected; no complete PDF hash is claimed. |
| Diskin, Dingel & Liang, *Scenario Integration via Higher-Order Graphs*, Queen's report 2006-517, [PDF](https://research.cs.queensu.ca/TechReports/Reports/2006-517.pdf) | §3.1–3.3, printed pp. 9–13, separate names from denotations, specify correspondences by spans, merge by generated equivalence, and lift the construction to graphs. Correspondence discovery is an input, not a derived identity rule. The closing sketch/constraint caveat prevents treating graph merge alone as constrained-model integration. Useful for formulating [Q4](sources.md#mcs-gluing-and-the-approved-q4-rule)'s alternatives, without selecting a Clafer congruence. Acquired 23-page PDF SHA-256: `7da666e6016f5c1c4d2b261922990ac009bce090d4bff10243e41402b2d704c7`. |
| Diskin, *Mappings, maps, atlases and tables: a formal semantics for associations in UML 2*, [Toronto report CSRG-566](https://ftp.cs.toronto.edu/pub/reports/csrg/566/TR-566-umlAssons.pdf) | The acquired 48-page version credits Diskin alone. Definition 5.1, p. 34, distinguishes role labels from class names and permits repeated classes in a context. Construction 5.2 fixes one common state; Definition 5.4, pp. 35–36, separates mapping schemas from their concrete names. Construction 5.6 separates duplicate elimination from the original mapping. These support explicit role/context data; they do not determine Clafer's gluing congruence or supply general dynamic identity semantics. SHA-256: `837e177f6fd7e7ce8dcdf6565edbe7c7bd9dd670391ddf89311c23030a33391b`. |
| Diskin, Easterbrook & Dingel, *Engineering Associations* (2008), and Diskin's *Model Synchronization* tutorial (2011) | The [Q1 source comparison](#span-composition-q1-research-for-4) records their PDF hashes and locators. They support link identity, association views and span composition; neither selects Clafer's label congruence. Both full PDFs were acquired and their recorded hashes verified. |

## Generalized sketches and model-reduct coherence

`impl~supporting-source-assessment~1`

The [partial-source assessment](#universal-arrow-foundations-partial-source-assessment) and
comparison below support the [research requirement](spec.md#supporting-source-and-coherence-research).
The missing 2003 full text and 2000 page gaps remain unaudited; the bounded
disposition below states when further acquisition is needed.
No mathematical implementation or new theorem is delivered by this comparison.

Covers:
- `req~supporting-source-research~1`

| Concern | SoSyM B.4–B.5 and the delivered API | Diskin & Wolter author upload |
| --- | --- | --- |
| Signature and consequences | Definition 7 / `Signature`: symbols with graph arities; Definition 9 / `DPGraph`: a declaration set without inference closure. | §4.1 Definition 4.1 uses a predicate/dependency category and an arity functor. Definition 4.5 (Inf) closes declarations: a dependency `r : Q → P` carries `P(d)` to `Q(α(r) ; d)`. |
| Models and satisfaction | A map from the carrier to fixed `Ω`; `Interpretation.meaning` selects satisfying arity maps. | §4.2 Definitions 4.7/4.9 use instances typed into a carrier and satisfaction by pullback. Meanings are isomorphism-closed and consistent with dependency pullbacks. |
| Restriction and its laws | B.5 Theorem 3 / `isModel_reduct` restricts by precomposition. `reduct_id` and `reduct_comp` prove equalities of model values. | §4.3 Lemma 4.13, Proposition 4.14 and Corollary 4.15 use chosen pullbacks, coherent natural isomorphisms and isomorphism-closed meanings. Theorem 4.19 packages the sketch instance pseudofunctor. |

The comparison does not identify these two model representations. A future
typed-instance bridge needs an explicit construction and correspondence theorem
with its size and semantic hypotheses. The existing precomposition laws require
neither pullback choices nor extra axioms on meanings; they do not establish
strict equality for arbitrary chosen pullback reducts. For a dependency-enriched
extension, separately specify dependency direction, arity functoriality,
declaration closure, interpretation consistency and the intended coherence laws.
That extension and its proofs require a new authorized scope.
The 2007 report above supplies an ordinary-signature comparison; generalized
sketch references do not all assume the 2008 dependency-enriched signature.

### Arity alternatives and semantic compatibility

| Representation | Obligations and present need |
| --- | --- |
| Ordinary graph arities | Delivered `Signature.arity` and `Formula.binding` retain incidence, isolated vertices and repeated arguments. `Hom.preserves` preserves declared formulas. This suffices for the selected SoSyM vocabulary and existing `FormalCD` construction; its explicit disciplines remain separate. |
| Marker-bearing arities, recovered 2000 p. 350 | A binding must preserve marks on the arity as well as its graph. A possible design keeps the ordinary signature and separately specifies prerequisite formulas on each arity, with translated prerequisites required in the carrier's declarations. Translation stability, closure and sound interpretation of those prerequisites would need proofs. No such extension is currently required or implemented. |
| Predicate/dependency category, 2008 §4.1–3 | Also specify dependency composition, an arity functor, inference closure and interpretation consistency. Typed pullback instances add isomorphism closure and coherence. This is a possible future framework, not an equivalence already established for the other two presentations. |

In the possible prerequisite design, let `Req(p)` be formulas on `arity p`.
For `P(d)` declared in `S`, require `ψ.translate d` in `S.declarations` for
each `ψ ∈ Req(P)`. Soundness would additionally require every
`d ∈ I.meaning P` to satisfy those `ψ`. Merely adding declarations does not
establish that entailment. This is a proposed encoding obligation, not a new
Lean declaration or a correspondence theorem attributed to the papers.

There is a concrete compatibility boundary: the 2008 author's Example 4.8
requires total single-valued legs for its binary key. Our `Key` permits bags;
`bagKey_key` and `bagKey_not_setValued`, together with
`singleValued_setValued`, rule out importing that prerequisite for every key
argument. The [ordinary-function special case](spec.md#ordinary-key-correspondence-and-repeated-marriages)
preserves that meaning and states the additional hypotheses explicitly.
Precomposition reduct laws remain as
proved; any future inferred declarations need their own soundness argument.

### Metamodel realization and translational semantics

The [realization investigation](https://github.com/kbak/clafer-semantics/issues/100)
separates faithful encoding of CD syntax, semantic self-instantiation of the
particular metamodel, and source-language preservation through Compile/gluing.
The [restricted theorem](metamodel-realization.md) constructs the exact syntax
encoding, characterizes satisfaction by two source hypotheses, and proves
reconstruction and the particular metamodel's self-instance. These are derived
Lean results under the existing meanings, not verbatim paper theorems. The
[literal-key and total-args counterexamples](#literal-key-total-args-and-the-19-obligation)
continue to obstruct unrestricted realizability.

Clafer's original formal semantics was defined through translation to Alloy;
the early [CS886 report](https://gsd.uwaterloo.ca/sites/default/files/cs886report.pdf),
§4, PDF p.8, states this explicitly. That historical translation is semantic
evidence for the language. The [historical recovery below](#historical-translation-evidence)
identifies printed rules separately from a pinned July 2011 implementation;
the exact implementation accompanying the earliest reports remains unidentified.
The original
[compiler comparison](resolved-ir-comparison.md#source-identities-and-audit-boundary)
pins `15adb2216909421bcb5022174d2d84ef2b42307c`; it does not identify the original
translation. Compare generated constraints and their relational meaning
separately from bounded Analyzer search. A disagreement can expose a Lean
omission, a paper ambiguity, language evolution or a compiler defect; choosing a
correction requires evidence and review. SoSyM remains this repository's selected
semantic reference, with its accepted corrections.

At that compiler pin, `Intermediate/Intclafer.hs` retains ordered operands in
`IFunExp`, typed expression containers and global/local bindings.
[`Intermediate/ResolverName.hs`](https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Intermediate/ResolverName.hs)
supplies constraint context and lexical resolution; `Generator/Alloy.hs`
generates expressions using the resolved path and environment. These static
observations guide checks of repeated/swapped operands, binder domains,
inherited navigation and constraints without navigation. They neither identify
an expression operand list with a DP-graph argument bag nor establish runtime
compiler correctness. The existing finite comparison fragment excludes user
expressions; extending it needs its own contract.

For the theoretical comparison, the inspected 2007 Wolter–Diskin report's
§5 Definition 14 and Remark 8 distinguish persistent model extension from
restriction and explain why noninjective identifications need semantic
agreement. The [2008 comparison above](#generalized-sketches-and-model-reduct-coherence)
supplies dependency consistency and typed-instance coherence obligations;
Example 4.8's total single-valued key remains a restricted comparison with our
bag-sensitive key. These statements inform the restricted hypotheses, without
proving an adapter between the model representations or changing Figure 21c.
The historical PDFs below have acquired file identities and bounded inspected
sections. The Diskin browser renderings remain inspected locators without a
complete PDF hash or full-paper audit.

### Historical translation evidence

These sources recover actual early encoding choices, not just the statement that
Clafer translated to Alloy. Acquired files remain external; no publication text,
figures or historical compiler code is incorporated into the repository.

| Source identity | Inspected evidence and boundary |
| --- | --- |
| Bąk–Lotufo, [CS886 report](https://gsd.uwaterloo.ca/sites/default/files/cs886report.pdf), 25 pages; SHA-256 `1ead8b06659ca8f190519dac6987226dfa76b23f30cf9f3dbc32e4a4d1d9d561` | §4, PDF p.8 identifies translation as formal semantics. PDF creation metadata says 2010-04-27; this is an artifact date, not an authenticated translator release. |
| Bąk, [CS846 report](https://gsd.uwaterloo.ca/sites/default/files/cs846report.pdf), 9 pages; SHA-256 `7f7c4d7c41264f233e469bfa816c876508bb1a6951ee2ab05eff319f0849b474` | §4.2–4.4/Figures 11–13, PDF pp.5–7: common clafer supertype, parent relations, abstract exclusions, resolved `this` navigation, references, groups and primitive wrappers. Creation metadata says 2010-06-29. The printed generated model is recovered evidence; no matching source commit is established. |
| Bąk, [CS744 report](https://gsd.uwaterloo.ca/sites/default/files/cs744report.pdf), dated 2011/7/26, 10 pages; SHA-256 `6b170250a8fdf59d9ff4a2875eb55a0f3aeca2dcd3766db96cb467acc6ce0ad6` | §2.3, pp.3–4 separates encoding from scope-bounded search. §3.1–3.7, pp.4–8 compares name resolution, inheritance, ownership, cardinality, primitive and reference optimizations. §4.4, p.9 explicitly leaves possible configuration-semantics changes as a validity concern. It supplies no general optimization-preservation proof. |

The [June 2010 translator announcement](https://gsd.uwaterloo.ca/node/225.html)
links the [original source directory](http://gsd.uwaterloo.ca/clafer/src);
its HTTPS route returns 404. The inspected GitHub default-branch history query yielded no commit before
2010-06-09. These routes do not identify that original implementation; this is
an acquisition gap, not evidence that the code never existed.

The [July 2011 release announcement](https://gsd.uwaterloo.ca/node/378.html)
links the optimization report and GitHub. A contemporaneous source snapshot is
[`gsdlab/clafer@18ce83101afdc1cb98bf1288fa0ed5d69ecafd88`](https://github.com/gsdlab/clafer/tree/18ce83101afdc1cb98bf1288fa0ed5d69ecafd88),
committed 2011-07-26; acquired archive SHA-256
`1c26168f0875c1a4f020a248c217e1237314fbb0b6b1ef25dcd2479b6f76ab1f`.
This is an independently pinned historical implementation, not a proven match
to the April/June 2010 translator or to every report example. The inspected
source headers license it under **LGPL-3.0-or-later**; the current audited
`15adb221…` pin is MIT. Do not apply the later license to the earlier code.

The following are static observations, not executed expression comparisons.
The existing full validation separately exercises the current compiler's guarded
structural fragment; it does not execute these historical or expression cases:

| Historical source at `18ce831…` | Observation relevant to a proof contract |
| --- | --- |
| [`src/Generator/Alloy.hs`](https://github.com/gsdlab/clafer/blob/18ce83101afdc1cb98bf1288fa0ed5d69ecafd88/src/Generator/Alloy.hs), `genClafer`, `claferDecl`, `genRelations`, `isRef` | Non-overlapping super relations generate `extends`. Nested leaf references can become direct fields with no separate occurrence signature; other reference clafers retain a ref relation. |
| Same file, `genConstraints`, `genParentConst`, `genOptParentConst`, `genGroupConst` | User, parent, group and reference-path constraints are explicit generators. Parent cases depend on global cardinality; an empty child inventory skips group generation. |
| Same file, `genLExp`, `genCmpExp`, `genNumExp`, `genDecl`, `genAExp` | Operand order, integer literals and quantified domains survive structurally. Mixed set/arithmetic comparison has special cases; the source itself flags complex expressions as problematic. This warrants a regression investigation, not a general correctness claim. |
| [`src/Intermediate/ResolverName.hs`](https://github.com/gsdlab/clafer/blob/18ce83101afdc1cb98bf1288fa0ed5d69ecafd88/src/Intermediate/ResolverName.hs), `resolveTerm`, `processDecl`, `resolveBind` | Domains resolve before a binding is pushed; sequential declarations extend the environment; newest matching local binding is selected first. Context and namespace identity are not recovered from an argument bag. |
| [`src/Intermediate/Intclafer.hs`](https://github.com/gsdlab/clafer/blob/18ce83101afdc1cb98bf1288fa0ed5d69ecafd88/src/Intermediate/Intclafer.hs) | Distinct constructors carry ordered comparison/arithmetic operands, declarations and relational navigation. This predates the later `PExp` representation. |

### Named comparisons and unresolved differences

These are source-derived examples and proposed comparison cases, not executed
Alloy witnesses. They inform the [proof obligations](metamodel-realization.md#source-to-obligation-comparison)
without extending the existing finite comparison harness to expressions.

| Case | Historical/current evidence versus the Lean contract | Disposition |
| --- | --- | --- |
| `P(a,b)` and `P(b,a)`, same symbol, unequal full bindings | Historical ordered AST constructors and current `IFunExp` retain positions. SoSyM B.4 Definition 8 retains the binding; Figure 21c's accepted bag key forgets positions. | Paper-level representation ambiguity/limitation, already exposed by `ordered_literal_key_fails`; require separation among declared formulas. Operand order alone does not prove an expression-to-DP encoding. |
| `[1 = 1]` without navigation | Historical `IEInt`/`genAExp` and current `IInt`/`genPExp'` impose no generator requirement for a navigation edge. Generic DP formulas permit zero arrows; Figure 21c total args and structural Compile's positive support do not. | Deliberate restriction in Lean's current bridges, not a language-wide prohibition. Whole-pipeline acceptance of this source text was not run. |
| Equal arrow bags, different isolated vertex bindings | B.4's full definition retains vertices; its arrow shorthand has extra hypotheses. Neither translator's expression syntax establishes injectivity of this projection. | Existing formalization preserves the distinction; `Separated` rejects the conflicting declared pair even when another arity arrow makes args total. |
| Two reference occurrences at the same target | The 2011 leaf-reference optimization uses a binary relation; current reified references and `genSetUniquenessConstraint` distinguish occurrences from set-reference uniqueness. Lean counts occurrence heads and keeps bag links. | Representation/feature evolution to investigate by fragment and mode; direct relational storage cannot retain duplicate identical tuples. Never infer bag identity from an optimized field. |
| Nested binder reuses a name; a later domain refers to an earlier binder | Both inspected resolver versions push bindings after resolving their domains. Current `SEnv`, `processDecl`, `resolveBind` and `genDecl` retain lexical context. Lean uses explicit typed binders. | Static alignment of mechanism, not an alpha-equivalence or shadowing correctness theorem. Fresh executable witnesses need a separate expression relation. |
| Inherited context and an explicit replacement group bound | CS846 §4.3 describes replacement of inherited group bounds. The selected [group contract](group-compilation.md) retains its own inherited/effective policy; current `findHierarchy`/`genGroupConst` supply separate evidence. | Possible language evolution or early-report ambiguity; do not infer one policy from another version. Review a concrete differing-bound example before changing the contract. |
| Positive group lower bound with no children | Both inspected generators skip empty groups; the adopted Lean contract counts literal zero. | Retained deliberate departure, already recorded in the group contract; unrelated to repairing total args. |
| Two component versions required to differ | CS846 Figure 13 uses one integer wrapper shared through version fields. CS744 §3.6 shows changed primitive storage; current code uses Int/ref paths, while Lean's selected contract uses mathematical Int and explicit singleton extraction. | The printed early encoding cannot supply two independent version values through that wrapper. Possible early limitation/report or compiler defect plus later evolution; no unbounded-integer equivalence follows from Analyzer results. |

For current expression handling, immutable loci are
[`Intclafer.hs`](https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Intermediate/Intclafer.hs#L175-L228),
[`ResolverName.hs`](https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Intermediate/ResolverName.hs#L143-L169),
and [`Alloy.hs`](https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Generator/Alloy.hs#L425-L562).
`_pid` identifies an expression occurrence where supplied, not its denotation;
`ClaferBinding` distinguishes global UID, local name and unresolved data.
`adjustPExp`/`genDecl` route navigation with the active path; this inspection does
not certify every inherited binder-domain adjustment. Repeated operands such
as `x + x`, swapped subtraction operands and shadowed names must remain distinct
test obligations if a future executable comparison is authorized.

The recovered material is sufficient to formulate the restricted syntax theorem;
it does not settle historical source-language equivalence. The original source
snapshot, historical integer/overflow settings, and executed expression witnesses
remain explicitly unestablished. No disagreement above authorizes a semantic
change to Lean, a key reinterpretation, or a new predicate dependency.

### Project-critical source disposition

Research follows the claims needed by an increment, using accessible primary
alternatives when they establish the exact point. Further recovery of the
2003 paper and missing 2000 pages is deferred unless such a claim cannot be
supported otherwise. These texts are not treated as read or as replaced in full.

| Needed claim or decision | Evidence and remaining owner |
| --- | --- |
| Ordinary-key correspondence | SoSyM B.1 and the delivered `Key` supply the semantics of the derived [ordinary-key correspondence](spec.md#ordinary-key-correspondence-and-repeated-marriages); the recovered p. 348 example and the restricted 2008 key explain the comparison. Its proof and finite marriage witness need no further acquisition. |
| Resolved identities versus repeated names | SoSyM §6.2.4 explicitly adds indices for uniqueness; recovered p. 354 and CSRG-566 Definition 5.1 support separating names and roles. The [resolved syntax](#resolved-2014-clafer-and-individual-shapes) and [Compile contract](compile.md) use this identity distinction. No general theory of object persistence is needed for that contract. |
| Which MCS roles denote one class or map | SoSyM §6.2.5 requires a graph/DP morphism. The [MCS representation](mcs-invariants.md) preserves independent role identities, resolved class/map referents and displayed names; repeated strings do not identify arrows. The approved [Q4](sources.md#mcs-gluing-and-the-approved-q4-rule) resolved-referent congruence and its incidence/declaration-preservation proofs are in [MCS gluing](#mcs-gluing-and-the-approved-q4-rule). This is a design decision, not a requirement to obtain one particular paper. |
| Closure or typed-instance coherence | The 2007 report and inspected 2008 definitions establish the relevant alternative frameworks. The present ordinary API needs neither extension. Reopen this design only for a concrete increment requiring marked arities or a typed-instance bridge, with size and interpretation hypotheses stated. |

The research assessment can be reviewed without completing the bibliography.
Revisit a deferred source when a named active claim depends on an unaudited
definition; record that claim, attempted alternatives and its issue owner.

### Lean library assessment

The bounded search inspected the full `Mathlib/` tree at the pin above for
`sketch`, `generalized/generalised sketch` and `institution`, followed relevant
category-theory modules, and checked GitHub repository queries
`sketch language:Lean` and `"generalized sketches"`, web/Reservoir discovery,
and the candidate README/manifests below. Keyword hits included proof outlines
and *Sketches of an Elephant* citations; they did not identify a sketch API.
Search results and compatibility are separate: none of the external candidates
was built against this project's Lean/Mathlib pins or added as a dependency.

| Inspected source | Relevant content and suitability limit |
| --- | --- |
| [Pinned Mathlib](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679) | `CategoryTheory/Limits/Shapes/Pullback/`, `FiberedCategory/`, `Grothendieck.lean` and `Bicategory/Functor/Pseudofunctor.lean` provide foundations. They do not supply the selected predicate/dependency signature, closure and satisfaction package together; those obligations remain to be specified. |
| [sinhp/LeanFibredCategories at a58604a](https://github.com/sinhp/LeanFibredCategories/tree/a58604a389544523aa171daf890386fb8317568b) | Fibers, Cartesian lifts and Grothendieck examples; README describes upstreaming foundations to Mathlib. Manifest pins Lean v4.4.0-rc1. Relevant background, without the required generalized-sketch layer. |
| [jacobneu/GeneralizedAlgebra at d2f4029](https://github.com/jacobneu/GeneralizedAlgebra/tree/d2f402944052f7d93d2f600ab1131c13d92d4351) | Generalized algebraic-theory signatures and generated algebra descriptions; Lean v4.13.0. A different specification language, without an inspected DP-sketch interpretation/reduct adapter. |
| [b-mehta/topos at c9032b1](https://github.com/b-mehta/topos/tree/c9032b11789e36038bc841a1e2b486972421b983) | Topos/pullback foundations; `leanpkg.toml` pins Lean 3.24.0. This is not a directly compatible Lean 4 dependency or a delivered diagram-predicate package. |

Retain the existing Mathlib dependency and ordinary `DPGraph` signature. Before
adopting an external library, check its license, exact API, maintained toolchain
compatibility and a compiling adapter with meaningful satisfaction/closure laws.
The scoped negative search cannot rule out other libraries or later versions.

<a id="span-composition-q1-research-for-4"></a>

## Span composition and relational reduction

The [span-library issue](https://github.com/kbak/clafer-semantics/issues/4) covers SoSyM B.1 Definitions
1–5, Theorems 1–2 and B.2.1–2. Its accepted implementation scope adopts the
correction below. The [span library](../DPGraph/Span.lean) implements that law and
its exact stronger-isomorphism criterion. This is a selected correction, not a
verbatim paper theorem. The abstract B.4/B.5 interpretation interface remains
independent of concrete predicate meanings.

### Source comparison

SoSyM B.1 distinguishes link identity, span isomorphism and relation reduction.
B.2.1, PDF p.30, first defines set-valued composition by union, then defines
span composition by a pullback of links. Its assertion that these coincide up to
isomorphism for relational inputs conflicts with its immediately following
two-path example. B.2.2 defines inversion by swapping legs.

Supporting full texts inspected for this question:

- Bąk, *Modeling and Analysis of Software Product Line Variability in Clafer*
  (2013), [Waterloo record](https://hdl.handle.net/10012/8039),
  [PDF](https://uwspace.uwaterloo.ca/bitstreams/fe498b08-4ee2-4247-9f2e-c1b3fc67d0ee/download),
  Appendix A.2.2, printed pp. 120–121 (PDF pp. 134–135). It repeats both the
  coincidence assertion and counterexample; it supplies no correction.
  SHA-256: `c623e685481a777b3387b8feb5aff9f9f62f431936318fba1830a75b3105b689`.
- Diskin, Easterbrook & Dingel, *Engineering Associations: From Models to Code
  and Back through Semantics* (2008),
  [author-hosted PDF](https://www.cs.toronto.edu/~sme/papers/2008/zTOOLS-08.pdf),
  §3.2–3.4, printed pp. 7–8. Labeled links retain repeated endpoint pairs;
  set-valuedness is a constraint. Inverse association ends have isomorphic
  extensions. This supports preserving links but does not establish the disputed
  composition claim.
  SHA-256: `34ed4bf6c4014e58445605392f03c5e638950dac6be07f3f0e7d485215b0d4cd`.
- Diskin, *Model Synchronization, Mappings, Tile Algebra, and Categories* (2011),
  [author-hosted manuscript](https://gsd.uwaterloo.ca/sites/default/files/zGttse11_0.pdf),
  Appendix B, manuscript pp. 61–63, Figure 32. It composes spans by pullback and
  explains associativity up to canonical isomorphism, or on isomorphism classes.
  Its application restricts both legs to injections. That restriction is stronger
  than jointly injective endpoint pairs and must not be imported into general
  Clafer mappings. §7.1, manuscript p. 45, also warns that a relational treatment
  loses structure carried by matching links.
  SHA-256: `0fdfb6cd9b6ff5006c9f6726ea6f105ea975079b5ef5a70c15f6581c6608153c`.

These texts are cited and independently analyzed; no publication text, figures
or third-party implementation are incorporated. SoSyM remains the primary
authority. The older thesis and the synchronization tutorial do not override it.

### Adopted correction and exact assumptions

Write `q ⋆ r` for **span composition** in source-to-target order, and `R ; S` for
**relational composition**. For spans `q : A ↛ B` and `r : B ↛ C`, let

```text
P = { (l, m) : Lq × Lr | tq(l) = sr(m) }
e(l, m) = (sq(l), tr(m))
red(q)(a, b) ↔ ∃ l : Lq, sq(l) = a ∧ tq(l) = b.
```

The adopted compatibility theorem, proved as `Span.red_comp` for arbitrary spans, is

```text
red(q ⋆ r) = red(q) ; red(r).
```

Proof: a composable link pair supplies the intermediate object `tq(l) = sr(m)`.
Conversely, an intermediate object and witnesses for the two reduced relations
supply a composable pair. This equates endpoint membership, not link types.
It requires no finiteness, decidable equality or injectivity assumptions.

The map from `P` onto the head of the relation span for the right-hand side sends
`(l,m)` to `e(l,m)`. It is surjective by the same argument. It is a bijection
exactly when `e` is injective, equivalently when for every `(a,c)` there is at
most one composable **link pair** with those endpoints. This is also necessary
and sufficient for the composite span to be isomorphic to that relation span.

When both inputs are relations (their endpoint pairings are injective), this
condition simplifies to at most one intermediate `b` for each `(a,c)` satisfying
`red(q)(a,b) ∧ red(r)(b,c)`. Sufficient special cases are that `q` is single-valued
or that the converse of `r` is single-valued; neither needs totality. For arbitrary
spans, uniqueness of `b` alone is insufficient because parallel input links can
still yield several link pairs.

For the counterexample, take `A={a}`, `B={b₁,b₂}` with `b₁≠b₂`, `C={c}`,
`q={(a,b₁),(a,b₂)}`, `r={(b₁,c),(b₂,c)}`. The pullback head has two elements,
while the relational composite has one. There is no bijection and hence no span
isomorphism. Both inputs are relations; `r` is even a total single-valued function.
Relational inputs therefore do not suffice, nor does single-valuedness of the
second input. The adopted correction preserves this example and replaces the
unqualified coincidence assertion with equality after reduction.

### Delivered implementation boundary and proof references

The operations and equivalences are independently available through `import DPGraph`.
Names below are relative to `DPGraph`; the [trace artifacts](dpgraph-trace.md)
link their requirement and proof obligations.

| Construct | Implementation and proof references |
| --- | --- |
| Spans and isomorphisms | [Basic.lean](../DPGraph/Span/Basic.lean): `Span`, `Span.Iso`, `Span.Iso.refl`, `.symm`, `.trans`, `.red_eq` |
| Indexed families and conversions | [IndexedFamily.lean](../DPGraph/Span/IndexedFamily.lean): `IndexedFamily`, `.Equivalence`, `.toSpan`, `Span.toFamily`, `Span.familySpanIso`, `IndexedFamily.spanFamilyEquivalence` |
| Relation membership (Theorem 1) | [IndexedFamily.lean](../DPGraph/Span/IndexedFamily.lean): `Span.red_toFamily`, `IndexedFamily.red_toSpan`; [Relation.lean](../DPGraph/Span/Relation.lean): `Span.red_ofRelation` |
| Set-valuedness (Theorem 2) | [Relation.lean](../DPGraph/Span/Relation.lean): `Span.jointlyInjective_iff_fiberwise`, `.jointlyInjective_iff_iso_relation`, `.relationIso` |
| Composition and laws | [Composition.lean](../DPGraph/Span/Composition.lean): `Span.comp`, `.identity`, `.leftUnit`, `.rightUnit`, `.associator`, `IndexedFamily.compSpanIso`, `Span.compFamilyEquivalence` |
| Inversion | [Basic.lean](../DPGraph/Span/Basic.lean): `Span.inverse`, `.inverse_inverse`, `.red_inverse` |
| Adopted reduction law and exact criterion | [Relation.lean](../DPGraph/Span/Relation.lean): `Span.red_comp`, `.compToRelation_surjective`, `.comp_iso_relation_iff`, `.comp_jointlyInjective_iff_uniqueIntermediate`, `.relations_comp_jointlyInjective_iff` |
| Sufficient conditions, without totality | [Relation.lean](../DPGraph/Span/Relation.lean): `Span.relations_comp_injective_of_first_singleValued`, `.relations_comp_injective_of_converse_second_singleValued` |
| Counterexamples | [Examples.lean](../DPGraph/Span/Examples.lean): `Span.Examples.twoPaths`, `.oneReducedPair`, `.second_singleValued_not_sufficient`, `.parallel_uniqueIntermediate`, `.parallel_composite_not_iso` |

Universe bounds remain compatible with the category and model-restriction
contract recorded in the [semantics issue](https://github.com/kbak/clafer-semantics/issues/15):
the family-to-span head lies in the maximum of source and index universes, and
the relation head in the maximum of the endpoint universes. A roundtrip need not
return a head in the original syntactic universe. Explicit joins and the mixed-universe
examples track these bounds without imposing one global universe or a resizing axiom.

The span library requires no bicategory, quotient of all spans, global finiteness
or executable object generation. The predicate contracts below, accepted in the
[concrete-predicates issue](https://github.com/kbak/clafer-semantics/issues/16),
interpret Table 3 commutation and inverse using link-preserving isomorphism;
equality of reduced relations alone does not establish these predicates.

## Audit coverage and remaining decisions

`impl~formalization-roadmap-sources~1`

The table extends the exact `DPGraph` mapping above through the two upper layers.
Future representations and obligations are proposals for their owning increments,
not additional promises of implemented mathematics. Detailed delivered
declarations remain in [DPGraph trace artifacts](dpgraph-trace.md) and
[FormalCD trace artifacts](formalcd-trace.md).
The [supporting-source audit limits](#supporting-sources-and-licenses) and
[Q1–Q8 dispositions](#question-dispositions-and-validation-tasks) supply the
remaining research obligations for this source-map artifact.

Covers:
- `req~formalization-roadmap~1`

| Construct and exact SoSyM locator | Representation and obligations | Implemented result and decision history |
| --- | --- | --- |
| Predicate catalogue: B.3 Table 3, §6.1.1–2, A.1 Table 2 | Separate typed arities and span meanings; invariance, multiplicity and empty/repeated-family boundaries; [common-target disjointness correction (Q8)](sources.md#predicate-contracts-and-the-accepted-q8-correction) | Selected vocabulary is proved; the [predicate implementation PR](https://github.com/kbak/clafer-semantics/pull/34) records delivery. Unsupported predicates remain deferred. |
| Formal CD: §6.1.1–3, Figure 21a–b | Raw/bundled CD, registry, naming and effective defaults; name-preserving morphisms are an explicit library specialization | Structure and morphisms are implemented in the [formal-CD PR](https://github.com/kbak/clafer-semantics/pull/35); whole Figure 21b models and guarded version comparison are implemented in the [telematics PR](https://github.com/kbak/clafer-semantics/pull/38). |
| Metamodel: §6.1.3, Figure 21c | Compatible vocabulary, nd/ad disciplines, full graph bindings; separate syntactic self-description from semantic instantiation | The [metamodel PR](https://github.com/kbak/clafer-semantics/pull/36) implements these disciplines. [Bounded self-description](architecture.md#bounded-self-description-and-figure-21b) retains the literal-key and argument-totality limits below. |
| Syntax and individual Shapes: §5.2 Figure 16, §6.2.2 Figure 22, Appendix 3 | Resolved deep AST and individual Shapes; IDs, containment, inheritance, references, abstractness, root/domains and finite traversal | [resolved syntax and Shapes issue](https://github.com/kbak/clafer-semantics/issues/3), [implementation and proofs](clafer-trace.md) |
| MCS: §6.2.3 Figure 23, Tables 5–8 (see Appendix 5) | Accepted guarded incidence/naming and analogous expansion, preserving exact Shape presence rules and distinct identity levels; see the [inventory](mcs-invariants.md). The accepted [Q9](mcs-invariants.md#figure-23-source-multiplicity-correction) correction applies source `0..1` to the four ordinary-map and three inclusion-role associations, retaining exact Shape presence. | The [MCS disciplines issue](https://github.com/kbak/clafer-semantics/issues/20) records accepted guards and ownership bounds; role/referent/name separation is retained. |
| Constraints: Appendix D.1–D.4 | Resolved typed core, lexical binders, both joins, explicit inheritance widening and finite graph support; meaning remains distinct from syntax | The [core-typing issue](https://github.com/kbak/clafer-semantics/issues/21) records delivery; Appendix 4 notation decisions appear below. |
| Compile: §6.2.4 | [Structural Compile](compile.md): finite resolved-AST-to-MCS construction; derived termination, freshness, incidence, cojoining and kind/name preservation under explicit input well-formedness | The [Compile issue](https://github.com/kbak/clafer-semantics/issues/22) records delivery. Its construction depends on resolved syntax, MCS disciplines and typed constraint support. |
| Gluing: §6.2.5 and B.4 Definition 10 | Used-referent graph with approved [Q4](sources.md#mcs-gluing-and-the-approved-q4-rule) incidence/metadata consistency, exact declaration image and DP labeling; separate CD validity under naming/default completeness | [resolved-referent gluing issue](https://github.com/kbak/clafer-semantics/issues/23), [construction and proofs](#mcs-gluing-and-the-approved-q4-rule); no global pushout existence |
| Integration: Appendix 6 and selected earlier figures | [Representative examples](representative-models.md) exercise Compile/gluing with explicit coverage limits; the [complete Appendix 6 model](telematics.md) separately satisfies all twelve bodies | [representative integration issue](https://github.com/kbak/clafer-semantics/issues/24) and [complete Appendix 6 model issue](https://github.com/kbak/clafer-semantics/issues/64), delivered under their distinct contracts |

### Question dispositions and validation tasks

Q1–Q9 name the source questions in this table; [A1–A9](architecture.md#nine-architectural-decision-areas)
name design areas; [D1–D8](resolved-ir-comparison.md#decisions-accepted-locations-and-dependency-boundaries)
name compiler-comparison decisions. These project IDs are separate from the
paper's section numbering.
An accepted correction is a bounded decision, not permission to fill unrelated
source gaps. Keep the original issue discussions as the decision history.

| Question | Disposition and alternatives | Validation and owner |
| --- | --- | --- |
| Q1 — B.2.1 composition | Accepted: retain pullback links and prove equality after reduction. The unqualified relational-span isomorphism is false. | The [span implementation PR](https://github.com/kbak/clafer-semantics/pull/32) supplies `Span.red_comp`, the exact endpoint-injectivity criterion and two-path/parallel-link counterexamples; [source comparison](#span-composition-q1-research-for-4). |
| Q2 — Appendix 5 analogous clauses | Accepted: incidence/naming equations apply only to present roles; existing Shape rules separately require or forbid each role. The analogous expansion includes Sing/root, every supported primitive domain, the accepted parentless exception and both directions of canonical naming equivalences. | The [complete Table 5–8 inventory](mcs-invariants.md#appendix-e-inventory) enumerates the guards. The inventory links definitions and positive/negative witnesses; the accepted Figure 23 multiplicity correction is [Q9](mcs-invariants.md#figure-23-source-multiplicity-correction). |
| Q3 — Appendix 4 notation | Resolved for the selected core: ordinary common-element intersection is already printed as ∩ in D.4.2. D.4.1 equates E and S on set expressions, reconciling the mixed subscripts. D.1–D.3 govern typing; the implementation boundary is enumerated below. | [Core constraint typing](spec.md#resolved-core-constraint-typing) supplies typed syntax and explicit inheritance paths. The [denotation extension](constraint-denotation.md) supplies independent core meanings, local finite cardinality and the [singleton-extraction bridge](integer-extraction.md); no compiler-preservation theorem follows from a signature. |
| Q4 — labels and identity | Accepted MCS representation: preserve role identities separately from resolved class/map referents and displayed names, and state the identity level of cojoining equalities. Repeated parent/dref/isA strings do not identify arrows. Approved [Q4](sources.md#mcs-gluing-and-the-approved-q4-rule): identify exactly equal class/map referents; equal map referents require equal endpoint class referents, and identified roles require equal names, predefined identities/kinds and modes. Reject conflicts. | The [MCS representation](mcs-invariants.md) retains the data needed for intended identifications and repeated-name witnesses; [resolved-referent gluing](architecture.md#mcs-gluing) implements this congruence and proves endpoint/declaration preservation, then separate CD validity under explicit default assumptions. [Structural Compile](compile.md) retains generated identities. Existing `FormalCD` names remain metadata. |
| Q5 — self-description | Bounded syntactic representation and a separate restricted semantic self-instance are delivered. Universal every-CD realizability and a universe fixpoint remain outside scope. | The [bounded self-description proof](formalcd-trace.md#bounded-syntactic-self-description-proof) establishes representation/well-formedness in explicit `CDOver` parameters. Preserve the ordered/isolated/repeated binding witnesses and literal key/total-args limits below. The [realization contract](metamodel-realization.md) supplies explicit source support/separation and proves the particular self-instance without changing those limits. |
| Q6 — acquisition and visual completeness | Partial audit: 2003 full text missing; twelve recovered 2000 pages inspected with four page gaps. The criticality assessment above records alternate evidence and conditional acquisition. Visual inspection alone does not replace a construct-by-construct inventory. | The [supporting-source assessment issue](https://github.com/kbak/clafer-semantics/issues/41) records the bounded assessment and reviewed source disposition. The [syntax correspondence](#resolved-2014-clafer-and-individual-shapes), [MCS inventory](mcs-invariants.md) and [representative coverage](representative-models.md) pair Figures 16/22/23 and Appendix 6 with text, labels, incidence and examples. Reopen acquisition for a named necessary claim lacking adequate primary evidence; never mark unread definitions audited. |
| Q7 — VC order and guard | Accepted: display.version ≥ server.version, guarded by a nonempty server fiber. Contrary adjacent PDF p.18 prose is the discrepancy. | The [guarded correspondence and whole-model proofs](#figure-21b-and-the-accepted-q7-correction) establish these cases: greater/equal pass, lower fails VC, absent server passes. No remaining implementation task for this correction. |
| Q8 — disjointness shape | Accepted: §6.1.2/Figure 21 common-target maps with nonoverlapping images; Table 3's common-source shape is erroneous. | The [predicate proofs](dpgraph-trace.md#corrected-disjointness-proofs) establish typed arity, interpretation and overlap/repeated-nonempty-binding failures. [Contract below](#predicate-contracts-and-the-accepted-q8-correction); no second predicate or source-object inequality. |
| Q9 — Figure 23 source multiplicities | Accepted source correction: source `0..1` on the four ordinary-map and three inclusion-role associations means unique ownership within each image. The printed lower bounds force every MapRole into both parent_map and dref_map images, contradicting their distinct Table 8 names. | Shape/inheritance guards still require or forbid roles exactly. Head-class and formula source `1` are unchanged. The [correction and proof map](mcs-invariants.md#figure-23-source-multiplicity-correction) link the typed representation and nonempty witnesses. |

The accepted source/design cross-check and bounded supporting-source assessment
leave the named source gaps unaudited and further acquisition conditional.
The [architecture](architecture.md#roadmap-and-validation-accounting) records the
design rationale and proof-status boundaries separately from ticket completion.

<a id="appendix-d-rule-dispositions-q3"></a>

### Appendix 4 rule dispositions (Q3)

The published article identified above places D.1/Figure 28 on PDF p.32,
D.2 on PDF pp.32–33,
and D.3–D.4 on PDF pp.33–34. The [core constraint typing issue](https://github.com/kbak/clafer-semantics/issues/21)
disposition follows D.1–D.3 for typing and the maintainer's Alloy-inspired
relational set reading. Alloy is supplementary guidance, not a replacement
specification. No compiler implementation or third-party code is incorporated.

**Intersection and evaluator notation.** Visual inspection of D.4.2 confirms
that the intersection equation prints **∩**. Text extraction of this PDF
misidentifies the glyph. Ordinary
common-element intersection is the intended operation. D.4.1 explicitly identifies
E(SetExp, env) with S(SetExp, env), so the E subscript on right operands of
D.4.2's union, difference and intersection is reconciled by that equation. It is
not necessary to invent a conversion or change the meaning of either operand.
For example, intersection of {a,b} and {b,c} is {b}, while their difference is
{a}; intersection with the empty set is empty. The denotation witnesses check these ordinary intersection boundaries in the
actual typed core.

| Locator | Source contract | Delivered typing boundary |
| --- | --- | --- |
| D.1/Figure 28; D.3.1 | Universal quantification, conjunction, negation, comparison, arithmetic, cardinality, and embedded set expressions | `Expr` has Boolean/integer terms and class-indexed unary/binary collections. Boolean literals and integer literals are resolved core conveniences. `all` has a unary domain and a Boolean body; its variable has the element class and is intended to denote a singleton. Tuple quantification is not implemented. |
| D.3.1, Comparison / Arithmetic operator | Comparison requires a common type; arithmetic lists addition and subtraction although the conclusion displays only addition | Equality accepts any common core sort; less-than, addition and subtraction currently support integers. The integer-extraction extension supplies a partial singleton bridge with explicit domain evidence; string/other primitive operations remain implementation limits, not paper prohibitions. Cardinality yields an integer for either collection shape; no finiteness or evaluator theorem is asserted. |
| D.3.2, Set operators / Subsetting | Equal operand types; union, difference, intersection; Boolean subsetting | Both unary sets and binary relations have distinct union/difference/intersection constructors with a common shape, and Boolean subsetting. Explicit widening can first move inheritance-compatible operands to a chosen common class or endpoint pair. |
| D.3.2, Relational join | Binary–binary composition and unary–binary image, with matching middle type | Both joins are supported; `Path.navigate` builds endpoint-checked unary navigation. Widening is available before a join, so inherited members are not excluded. Reversed or unrelated endpoints require valid evidence and cannot be silently equated. |
| D.2, Descendants; §5.5 inheritance | Lookup takes inherited clafers into account | Widening records equal resolved identities or paths of actual super edges in the support graph. Both relation endpoints may be widened. The caller selects the common type; no least-common-supertype algorithm or name resolver is claimed. |
| Appendix 4 introductory prose; D.4.1, Set expression | Bare navigation defaults to `some`; no/one/lone/some test cardinality | Explicit typed syntax helpers express these tests using cardinality and integer comparison. A resolved input inserts the default helper; a collection is not itself a Boolean term. The denotation extension proves the helper equations and manually elaborates c01–c12; general textual desugaring correctness remains separate. |

D.2's reserved names, binder lookup and model lookup remain an upstream resolution
obligation. `this` is tied to the enclosing support vertex; head, parent,
dereference and target maps have resolved owners and checked endpoints. Display
names are metadata. Local variables use lexical positions and retain independent
binder IDs; duplicate names are allowed, while active IDs must be fresh. A domain
is outside its new binder's scope, and the body is inside it. External boundary
binders are outermost first and are reversed into the nearest-first typed context.

The finite support graph includes all maps and classes available to an expression,
including isolated/repeated occurrences and intermediate inheritance vertices.
Boundary scope and domain occurrence bags are retained separately; they are not
asserted to be an automatically extracted minimal support. A full graph binding
is required for a future predicate declaration (§6.2.2). This is an interface,
not a translation or a meaning proof.

The [independent denotation](constraint-denotation.md) now supplies `Expr`
meanings, explicit environments, local finite cardinality and explicit span
reduction. Substitution, a solver, parser, resolver and executable evaluator remain
outside this extension. In particular, `<` on arbitrary object sets is not justified by the schematic τ
in D.3.1; only the integer fragment is implemented. The interface does not settle
string ordering, automatic coercion selection, or tuple binders. The integer
extraction extension uses mathematical `Int` without overflow.
Those extensions require concrete source/semantic contracts before implementation.
The [requirements](spec.md#resolved-core-constraint-typing) and
[trace artifacts](clafer-trace.md#resolved-core-expression-constructors) state
exactly the implemented claims.

<a id="integer-extraction-and-appendix-f-version-operands"></a>

## Integer extraction and Appendix 6 version operands

The [integer-extraction contract](integer-extraction.md), accepted in the
[primitive-navigation issue](https://github.com/kbak/clafer-semantics/issues/67), extends the D.3–D.4
boundary with an explicit partial unary collection-to-integer operation. This is
a selected implementation contract for the primitive bridge, not a claim that
the paper spells out a runtime error API. Success requires an exact singleton of
a realized integer; invalid results are undefined (`none`). The integer-domain
encoding/decoder is reused from Figure 21, without using its VC predicate to
interpret general expressions. [The conversion contract](integer-extraction.md)
and [trace artifacts](clafer-trace.md#integer-extraction-interface) state its limits.

The primary PDF above was used for Appendix 6 PDF p.34, D.3–D.4 and §6.1/Figure 21.
The selected Appendix 6 declarations have these navigation consequences:

| Source fragment | Resolved/semantic consequence |
| --- | --- |
| `comp` owns `version` referring to integer | version head from comp to reference objects, followed by a total functional dereference to the integer domain |
| ECU and display extend comp | separate inclusion maps justify inherited version access, preserving ambient objects |
| display owns `server` referring to ECU | server head and dereference lead to ECU before inherited version access |
| omitted version and server multiplicities | default 1..1, unlike Figure 21's 0..1 server; singleton results are derived from link bounds |
| display comparison | display.version >= server.version, with no additional guard |
| `plaDisplay` specializes display and constrains server to parent | a further whole-model restriction; the selected operand-definedness theorem does not assume it or implement all inherited structures |

The Lean fragment retains reference objects instead of identifying head maps
with the combined Figure 21 maps. Its semantic theorem assumes the selected
multiplicity/reference/inclusion discipline and derives singleton operands;
structural Compile alone does not discharge those assumptions. The concrete
examples include five structural objects and **all** integers. No bounded Alloy
arithmetic or compiler evidence is used. The [denotation extension](constraint-denotation.md) consumes this interface
and retains these singleton obligations.

## Predicate contracts and the accepted Q8 correction

The [predicate-vocabulary issue](https://github.com/kbak/clafer-semantics/issues/16) selects Table 3
(PDF p.13), §6.1.1–2 and Figure 21 (PDF pp.18–20), Appendix A.1 (PDF p.28),
and B.1–3 (PDF pp.28–30) of the hashed published article above. The maintainer accepted
§6.1.2/Figure 21's common-target disjointness meaning: distinct family members
have nonoverlapping target images. Table 3's common-source shape and its
source-inequality condition are erroneous. In particular, two inclusions
containing the same ambient object overlap even at equal source values;
repeated nonempty bindings fail disjointness. No common-source alternative is
part of this vocabulary.

The selected interpretation of Table 3 inverse and equality uses B.1 Definition 2
link-renaming equivalence, B.2.2 leg-swapping inversion and B.2.1 pullback
composition. Equality is triangular commutation up to span isomorphism.
The [span-composition correction (Q1)](sources.md#span-composition-q1-research-for-4) continues to distinguish this from equality after reduction.
Key compares finite tuples of bags using target-preserving source-fiber
equivalences, including multiplicity; Figure 21c permits a bag-valued argument.
Cover and corrected disjointness compare reachable target values and require
no set-valuedness. Zero-member key requires a subsingleton source, cover an
empty target, and disjointness is vacuous; the central arity vertex remains.

B.1.4/Theorem 2 gives set-valuedness as joint endpoint injectivity. A.1,
Table 2 and §6.1.1 give totality and single-valuedness as source surjectivity
and injectivity respectively. Single-valuedness excludes duplicate copies.
Literal inclusion (A.1, §6.1.1) additionally fixes the underlying ambient
object and supplies exactly one link per source. An arbitrary injection,
or a permutation moving an object, is insufficient.

Table 3 mult-trg/mult-src and B.1 indexed families count actual outgoing/incoming
links. Finite bounds are embeddings to/from `Fin`; an unbounded upper limit
adds no finiteness condition. Under set-valuedness, fiber evaluation is a
bijection onto distinct reachable values. Source bounds are target bounds
of the inverse. These are bounded semantic graphs over subsets of a specified
ambient type, with an explicit link universe, not an all-universes SetMap.
No automatic set-valued default is imposed.

The generic built-in vocabulary excludes VC, arbitrary path equations beyond
the triangle, and `FormalCD`/`Clafer`-specific predicates. `FormalCD` supplies the
separate corrected VC extension described below.

| Source locator | Concrete declarations (namespace `DPGraph.Predicates`) |
| --- | --- |
| Table 3 inv/= (PDF p.13); B.1 Definition 2, B.2.1–2 (PDF pp.29–30) | `Inverse`, `Commutation`, `inverse_symmetry`, `inverse_iff`, `commutation_iff`; `Span.Iso.inverse`, `.comp` |
| Table 3 key (PDF p.13); Figure 21c (PDF p.19) | `BagEquiv`, `Key`, `BagEquiv.transport`, `key_iff`, `key_zero` |
| Derived from B.1 Definitions 1–5 / Theorems 1–2 (PDF pp.29–30), Table 3 key and Figure 21c; comparison with Diskin et al. (2000) §2.1 p.348 | `Span.ofFunction`, `bagEquiv_ofFunction_iff`, `key_ofFunction_iff`, `targetValue`, `targetValue_eq_of_source`, `red_iff_targetValue_eq`, `functionalSpanIso`, `key_total_singleValued_iff`, `tuple_injective_zero_iff` |
| Finite witness motivated by Diskin et al. (2000) §3.3 pp.353–354 / Figure 1 and §3.5 p.356 | `Examples.Remarriage.same_spouses_different_dates`, `spouses_not_key`, `spouseDate_key` |
| Table 3 cover (PDF p.13); §6.1.2 (PDF pp.19–20) | `Cover`, `cover_iff`, `cover_zero` |
| §6.1.2/Figure 21 (PDF pp.19–20), accepted [common-target disjointness correction (Q8)](sources.md#predicate-contracts-and-the-accepted-q8-correction) | `Disjoint`, `disjoint_iff`, `disjoint_zero` |
| A.1 (PDF p.28), Table 2 (PDF p.13), §6.1.1 (PDF pp.18–19), B.1.4/Theorem 2 (PDF p.30) | `SetValued`, `Total`, `SingleValued`, `Inclusion`; fiber characterizations and `inclusion_subset`, `inclusion_identity` |
| Table 3 mult-trg/mult-src (PDF p.13), B.1 indexed families (PDF pp.29–30) | `InRange`, `TargetMultiplicity`, `SourceMultiplicity`, `distinctValuesEquiv`, multiplicity invariance/duality/distinct-value theorems |
| B.4 Definitions 6–9 and B.5 (PDF p.31) | `signature`, `semanticGraph`, `interpretation`; generic `Interpretation.Satisfies` and `.reduct` |

The [trace artifacts](dpgraph-trace.md) link implementations and checked
acceptance witnesses to the current mathematical requirements. Transport and
invariance results are derived library statements for these selected contracts,
not additional claims attributed verbatim to the paper.

## FormalCD structure and selected morphisms

The [formal-CD structure issue](https://github.com/kbak/clafer-semantics/issues/17) adopts
the structural contract from the same hashed published SoSyM article, §6.1.1–3 and Figure
21b–c (PDF p.19; explanation PDF pp.20–21), over B.4 Definitions 6–10. The correspondence is:

| Source / selected contract | `FormalCD` declarations |
| --- | --- |
| §6.1.1 classes, maps, inclusion identities/names | `Raw.className`, `Raw.mapName`, `MapMode`, `RawOver.WellFormed.inclusion_name` |
| §6.1.2 typed predicates; B.4 Definitions 6–9 | Existing `DPGraph`, `Formula`, `Predicates.signature`; `arrowBinding`, `inclusionFormula`, `setValuedFormula` |
| §6.1.3 predefined naming discipline | `Registry`, `PredefinedKind`, `Raw.predefined`, `RawOver.WellFormed.predefined_name`, `.user_name`, `.unique_predefined` |
| §6.1.1–3 defaults; Figure 21c explicit bag-valued args | `Raw.mode`, `RawOver.WellFormed.inclusion_decl`, `.ordinary_decl`; `Examples.no_bag_default`, `.explicit_bag_wellFormed` |
| Adopted name/annotation/mode-preserving specialization of B.4 Definition 10 | `Hom`, `.id`, `.comp`, `.ext`, `.comp_assoc`, `.id_comp`, `.comp_id`, `.toDPHom` |
| Existing abstract B.5 reduct after forgetting | `Hom.reduct`, `.reduct_id`, `.reduct_comp`; `Examples.restrictedModel` |

The extra metadata equalities are an accepted library contract, not a verbatim
theorem about arbitrary DP morphisms. Class identities are vertices and map
identities are arrows; strings need not be globally injective. Different inclusion
arrows may both be named isA. A selected predefined identifier has one realization
at most, but no predefined entry is compulsory. Registry kinds distinguish the
singleton vocabulary from primitive domains without implementing their object sets.

WellFormed requires default membership in the authoritative effective declaration
set; it adds no generic `DPGraph` defaults or inference closure. Inclusion and bag
are separate modes. Inclusion's semantic consequences come from its already delivered
literal span meaning. User declarations are retained, including explicit bag
setValued constraints. Structural validity alone implies neither satisfaction nor
model existence; an explicit interpretation and a model proof remain necessary.
This increment reuses the supported predicate vocabulary, preserving [span composition (Q1)](sources.md#span-composition-q1-research-for-4) and [common-target disjointness (Q8)](sources.md#predicate-contracts-and-the-accepted-q8-correction).
The metamodel extension below adds nd/ad and Figure 21c construction; a general
constraint language and complete primitive/object-diagram semantics remain open.
Figure 21b supplies a bounded integer realization for its separate VC extension.

The [FormalCD trace artifacts](formalcd-trace.md) link these independently
formalized contracts and acceptance witnesses to their Lean declarations.

## Figure 21c metamodel

The metamodel implementation, specified in the
[Figure 21c issue](https://github.com/kbak/clafer-semantics/issues/18), independently formalizes
§6.1.1–3, Figure 21c on PDF p.19, the explanation on PDF p.21 and B.4 Definition 8
on PDF p.31 of the 37-page publisher e-offprint with SHA-256
`653fc7868637680c44b6176d8ff643ec20149534fe1681ea4fc4ce636db76f2d`.
The figure and prose jointly determine the following inventory; no publication
images or text are vendored. Lean names below are in `FormalCD.Metamodel`.

The eleven distinct `Node` identities are Classifier, Class, Map, Incl, Predef,
SING, Dom, String, PredefStr, Formula and Signature. `SingletonClass.sing` describes
the modeled predefined class Sing, and `SingletonObject.star` its object; neither
is the metaclass `Node.sing`. The underlined SING node is the singleton annotation
in the metamodel's own small metadata registry. Concrete assignments to String,
PredefStr and Signature belong to interpretation context. Merely naming a node
Class or Signature supplies no universal collection of Lean types or signatures.

| Edge identity | Source → target | Displayed name and effective declarations |
| --- | --- | --- |
| predefStrIn | PredefStr → String | isA; inclusion |
| classIn | Class → Classifier | isA; inclusion |
| mapIn | Map → Classifier | isA; inclusion |
| predefIn | Predef → Class | isA; inclusion |
| singIn | SING → Predef | isA; inclusion |
| domIn | Dom → Predef | isA; inclusion |
| inclIn | Incl → Map | isA; inclusion |
| name | Classifier → String | name; ordinary setValued, total, singleValued |
| predefName | Predef → PredefStr | name; ordinary setValued, total, singleValued |
| so | Map → Class | so; ordinary setValued, total, singleValued |
| ta | Map → Class | ta; ordinary setValued, total, singleValued |
| args | Formula → Map | args; explicit bag, total; no setValued default |
| pred | Formula → Signature | pred; ordinary setValued, total, singleValued |

`classifiers` binds cover/disjoint to (classIn,mapIn), and `predefinedKinds` binds
them to (singIn,domIn), with the accepted common-target [Q8](sources.md#predicate-contracts-and-the-accepted-q8-correction) meaning. `keyBinding`
binds the literal key to (args,pred). The 30 `Declaration` cases enumerate seven
inclusions, five set defaults, six total and five single-valued annotations,
four cover/disjoint annotations, and key/nd/ad. Inclusion's existing meaning
already implies a total identity-valued function, without extra synthetic tokens.

The drawing omits dashed attachments for nd/ad. The following are **inferred
bindings**, justified by the selected constraint, not claims of hidden incidence:

- `nameShape` uses the nine left-hand nodes and exactly the seven inclusions and
  two name arrows. Canonical/user naming, optional predefined identity/kinds,
  inclusion naming and restriction along Predef→Class→Classifier and
  PredefStr→String need these nodes/maps. It omits so/ta, args and pred.
- `arityShape` has Formula, Signature, Map and Class and exactly args, pred, so, ta.
  Selecting a symbol, indexing its arguments and checking both endpoints requires
  this incidence. Extra arity vertices and occurrence labels are explicitly
  supplied data; they are not invented arrows in Figure 21c.

`NameContext` decodes names/identifiers and embeds strings into a bounded U.
`NameDiscipline` checks actual name links, reserved strings, realized optional
identifiers and kinds, unique identifier realization, isA names and the commuting
name-restriction square as a span isomorphism. It permits repeated classifier
names. The generic built-in inclusion declarations separately require identity
on the underlying ambient objects.

`ArityContext` supplies an independently bounded signature σ, graph G and explicit
embeddings of symbols, vertices and total arrows into U. `ArityDescriptor` provides
optional candidates for actual formula objects and optional occurrence indices.
`ArityDiscipline` checks domain sets, so/ta endpoints, a valid complete candidate,
a bijection from each actual args fiber to all arity arrows, the argument values,
and the selected pred value. Missing/invalid descriptions are rejected. Candidate
validity itself is equivalent to the existing typed Formula representation, by
`Candidate.formulaEquiv`; it is not supplied as a validity assumption by Context.

Every arity vertex remains in the candidate, including isolated ones. The graph
alone cannot recover this descriptor; interpretation is explicitly parameterized
by it. The bounded span links use `Type (max z w)` for `U : Type z`, with semantic
arrows in `Type (max z w + 1)`; signature/carrier universes remain independent.

<a id="literal-key-total-args-and-the-19-obligation"></a>

### Literal keys, argument totality and self-description

B.4 Definition 8 defines a formula as a symbol and a **full graph morphism**.
Its arrow-list shorthand explicitly assumes finitely many arrows and no isolated
nodes. The generic library does not impose those hypotheses. The PDF p.21 prose uses
indexed families for arguments, while the accepted Table 3 key compares bags by
fiber equivalence. These are different observations of a formula. The accepted
[formal-CD metamodel](architecture.md#figure-21c-and-compatible-vocabularies) contract preserves both; it does not reinterpret the generic key as indexed
identity or quotient existing formulas. Symbol plus all vertex/arrow actions
characterizes formula equality; bag-key satisfaction is an additional condition.

| Checked witness | Literal key | Total args | Exact conclusion |
| --- | --- | --- | --- |
| `ordered` pair | fails | holds | Same symbol and equivalent arrow bags, different positions/full bindings |
| `isolated` pair | fails | fails | Same symbol and empty arrow projection, different isolated vertex images |
| `repeated` singleton formula | holds | holds | Two distinct occurrences have the same arrow value; not set-valued |
| `fragmentModel` | holds | holds | Actual extended-interpretation model of ad/key/total with repeated args |
| `nameDiagram false/true` | not a formula/key fragment | not an args fragment | nd holds for user/canonical predefined naming respectively |

The ordered/isolated span witnesses are projections of the displayed full
bindings. They are not asserted to be full Figure 21c models. `fragmentModel`
checks an explicit declaration fragment; the separate name witnesses check nd.
The metamodel `diagram` is syntactically well-formed, which does not assert its
own semantic satisfaction. The separate
[canonical realization](formalcd-trace.md#particular-semantic-self-instantiation-proofs)
proves whole-metamodel satisfaction under `context diagram`; no universal
every-CD-is-an-instance theorem is claimed.

The total bullet on args excludes an empty outgoing fiber for a realized formula.
Zero-arrow arities (with isolated vertices) remain valid generic formulas but
cannot satisfy that totality with their complete indexed argument representation.
This restriction is retained rather than erasing the figure annotation.

The bounded result in [SelfDescription.lean](../FormalCD/SelfDescription.lean)
reuses `Metamodel.diagram`, its well-formedness and inventory in the small
`CDOver` family with the concrete nd/ad vocabulary and SING registry. Its full
formula representation is the existing `Candidate.formulaEquiv`. This states
that MCD is representable as a formal CD; it claims no semantic self-instantiation,
universal realizability or self-containing universe. Literal key and total args
remain separate instance conditions, with the projection failures above intact.

## Figure 21b and the accepted Q7 correction

The [telematics issue](https://github.com/kbak/clafer-semantics/issues/19) selects the corrected
inequality **display.version ≥ server.version**. Figure 8 line 9 (PDF p.10), its
accompanying §4.2.3 discussion and Appendix 6 (PDF p.34) support this direction.
Section 4.3 (PDF pp.10–11) supplies the configuration context.
The paragraph accompanying Figure 8 describes the display's version as not lower
than the server's. Figure 21a (PDF p.19) explicitly guards the comparison by
`self.server->notEmpty()`: a display without a server satisfies VC vacuously.
Equality passes. The nearby PDF p.18 prose instead says the ECU's version is not
lower than the display's; that discrepancy is retained as a source error, not
an alternative interpretation. The rendering and original publication remain
reference inputs, not repository content.

The Figure 21b construction follows §6.1.1–3 and the exact twelve-formula list
on PDF p.21, with B.4 Definitions 7–9 supplying signature/formula/DP-graph structure:

| Identity | Incidence | Name / declarations |
| --- | --- | --- |
| i1 | ECU → Comp | isA; inclusion |
| i2 | Display → Comp | isA; inclusion |
| server | Display → ECU | server; 0..1, setValued |
| display | ECU → Display | display; 0..5, setValued |
| version | Comp → Int | version; 1..1, setValued |

Together with disjoint(i1,i2), cover(i1,i2), inverse(server,display) and
VC(server,i1,i2,version), these are twelve effective formulas, proved distinct.
Class identities are exactly Comp, ECU, Display and Int. Int has the canonical
primitive registry annotation; the example selects no Sing class. The registry
API still permits optional entries. The italic Comp label adds no separate
constraint: cover/disjointness impose the partition. The bullet/open arrowheads
on version are accounted for by 1..1; server's open head is accounted for by
0..1 and does not imply totality. Display remains a general map bounded by 0..5.

`FormalCD.Telematics.vocabulary` adds VC through the compatible extension API,
leaving `DPGraph.Predicates` and its [Q8](sources.md#predicate-contracts-and-the-accepted-q8-correction) common-target/inverse/multiplicity meanings
unchanged. VC has a real four-arrow arity with all four vertex images. Its
interpretation checks an explicit integer-domain realization and follows the
inclusion/version links for every server link. The theorem
`satisfies_vc_iff_guarded` connects actual formula satisfaction to the selected
integer comparison under inclusion and 1..1 version hypotheses.

The example models in `FormalCD.Telematics.Examples` realize all integers in
`Bool ⊕ Int`. `model_iff` characterizes all twelve declarations for arbitrary
ECU/display integers and a present/absent server link. Greater and equal cases
pass, lower fails only VC, and an absent server passes with a faithful 0..1
multiplicity. These are whole Figure 21b model claims, distinct from the bounded
syntactic self-description theorem and the Figure 21c fragment witnesses.

## Resolved 2014 Clafer and individual Shapes

The syntax and Shapes implementation, specified in the
[resolved-syntax issue](https://github.com/kbak/clafer-semantics/issues/3), covers selected
constructs from the same 37-page publisher e-offprint (SHA-256
`653fc7868637680c44b6176d8ff643ec20149534fe1681ea4fc4ce636db76f2d`).
Figures 16, 22 and 23 were visually cross-checked against their accompanying
text. The formalization is independent; no publication figures/text or compiler
implementation are vendored. The paper supplies this slice's semantic foundation;
the explicitly adopted child-default evolution below uses the pinned Haskell
compiler as supplementary implementation evidence.

| Source locator | Selected contract and Lean correspondence |
| --- | --- |
| §5.3.1–3/Table 4 (PDF pp.14–15), Figure 22 (PDF p.21) | `Reference`, `Kind`: basic, reference set and reference bag; resolved target IDs |
| §5.3.4–5 (PDF p.15)/§5.4 (PDF p.17), §6.2.2 (PDF p.21) | `Origin`, `Declaration`, `Tree`, `AST.WellFormed`: distinguished root, selected int/string/bool domains, nested and top-level abstract declarations, deep containment |
| §5.5 (PDF p.17), Figure 18 | `Kind.CanExtend`, `inheritance_kind`, `inheritance_parent`: no basic-over-reference or bag-over-set; equal parents when super is parented; local inclusion roles |
| Appendix 3/Figure 27 (PDF pp.31–32) | `Multiplicity`, `GroupCard`, `GroupMultiplicity`, `Defaults`: authored/effective intervals, unbounded upper limit, xor/or/mux/opt, explicit child overrides, inherited group provenance |
| §6.2.2/Figure 22 (PDF p.21), D.2 boundary (PDF pp.32–33) | `ConstraintBoundary`, `Binder`: resolved context, repeated scope/domain occurrences and separate binder identities; the [typed core](#appendix-d-rule-dispositions-q3) is supplied separately |
| §5.2/Figure 16/Table 4 (PDF pp.14–15), §6.2.3/Figure 23 (PDF pp.22–23) | `Roles.Class`, `Roles.Arrow`, `Shape`, local `Shape.diagram`: typed optional roles, inverse/triangle/multiplicity/set/key declarations using `FormalCD` and `DPGraph` |
| §5.5/Figure 18, Table 6's local inclusion endpoints (PDF p.22) | `Shape.SharedClass`, `Shape.Inclusions`, `Shape.OptionalInclusions`: head inclusion and source/target inclusions where both endpoints exist; global cojoining belongs to the [MCS layer](mcs-invariants.md) |
| §5.4 and §6.2.4 traversal (PDF pp.17,23) | `Tree.fold`, `Tree.child_smaller`, `AST.every_entry_indexed`, `parent_wellFounded`: derived finite representation/termination basis; no compilation correctness claim |

The resolved boundary accepts IDs, not textual resolution requests. `Defaults`
checks explicit values and the effective values supplied by an elaborator.
Clafer multiplicity sugar is already numeric at this boundary: `?` is 0..1,
`+` is 1..*, and `*` is 0..*. Authored values record whether an interval was
explicit, without preserving the original token spelling.

Group keywords retain their provenance through inheritance so their child-default
policy remains inspectable. The [current child-default policy](#current-child-default-policy)
distinguishes numeric 0..* from opt even though their group ranges agree.
Effective bounds must be valid; root/domain metadata is
separate from user defaulting. Acyclic inheritance uses an explicit rank witness
as a selected well-formed-input condition, not a theorem attributed verbatim to
Figure 22. Reference cycles are permitted and do not enter containment recursion.

### Current child-default policy

`GroupCard.childDefault` and `Defaults` adopt the numeric-group policy selected in
[the defaulting decision](https://github.com/kbak/clafer-semantics/issues/118).
An unannotated child has multiplicity `0..1` under `xor`, `or`, `mux`, `opt`,
or a numeric group other than exactly `0..*`. A numeric `0..*` group gives
`1..1`; an omitted group inherits its super's complete effective group, or uses
numeric `0..*` if there is no inherited group. Explicit child bounds override
these defaults. Keyword provenance survives inheritance: `opt` and numeric
`0..*` have the same group range but different child defaults.

This deliberately evolves Appendix 3/Figure 27 (PDF pp.31–32), whose general
`1..1` child default has an exception for keyword groups. Numeric groups followed
that general default when the SoSyM paper was completed. The
[historical SoSyM checkpoint](https://github.com/kbak/clafer-semantics/tree/sosym)
at `8a300bff11af2f458af70d56394f1899815455e9` preserves that convention together
with the accepted paper corrections. The numeric change is language evolution,
not a paper erratum or a claim about the paper's original meaning.

The supplementary implementation evidence is Haskell 0.5.4's
[`analyzeCard`, lines 221–230](https://github.com/gsdlab/clafer/blob/6750e6f591b2131549122c13dee94d3d2257eaea/src/Language/Clafer/Intermediate/ResolverInheritance.hs#L221-L230).
Its numeric exception makes choice groups usable without marking every child
optional. The adopted change concerns child defaults only: abstractness,
explicit overrides, group counting, resolved-input guards and theorem assumptions
retain their separate contracts. Matching defaults on the tested common domain
does not establish general Haskell frontend equivalence. The
[comparison audit](resolved-ir-comparison.md#compiler-054-compatibility) retains
its historical observations and current admission boundary.

**Accepted top-level abstract correction.** Section 5.3.4, PDF p.15, says
that a parentless abstract's CS excludes the *head* class. Section 6.2.3, PDF p.22,
says the head is always present, and Figure 23 gives the head-class role total
multiplicity.

The maintainer's accepted interpretation retains the head and
removes the source and parent-dependent maps. A top-level abstract reference
therefore has head, target and dereference, with no head map, parent map or
target map. The basic-source-present statement in Table 7 (PDF p.23) is read with
this top-level abstract exception (and its separate synthetic-root rule).
Source/target inclusion roles are likewise omitted when either endpoint is
absent; head inclusion remains. This is an explicit correction, not a claim that
the conflicting sentence says the same thing. The publication and historical
accepted snapshots remain unchanged.

The MCS structural implementation follows the [Q2](mcs-invariants.md#appendix-e-inventory) guards/analogous expansion,
[Q4](sources.md#mcs-gluing-and-the-approved-q4-rule) identity separation and [Q9](mcs-invariants.md#figure-23-source-multiplicity-correction) source correction in the [MCS inventory](mcs-invariants.md).
The typed constraint extension and [Q3](sources.md#appendix-d-rule-dispositions-q3) disposition are described above. The
[independent core denotation](constraint-denotation.md) supplies constraint meaning
and the Appendix 6 expansions; the [selected preservation bridge](constraint-preservation.md)
connects them to generated predicate meanings. [Structural Compile](compile.md)
and [resolved-referent gluing](#mcs-gluing-and-the-approved-q4-rule) have separate
input contracts; [representative models](representative-models.md) check their integration.

<a id="figure-23-and-appendix-e-mcs-discipline"></a>

## Figure 23 and Appendix 5 MCS discipline

The [MCS inventory](mcs-invariants.md) maps every applicable Tables 5–8 row and
analogous clause to definitions/propositions and boundary proofs. The source is
the same published article, §6.2.3/Figure 23 (PDF pp.22–23), Appendix 5 (PDF p.34), Tables 5–8 (PDF pp.22–23).
[MCS/Metamodel.lean](../Clafer/MCS/Metamodel.lean) gives a typed graph for the
nine nodes and twenty arrows, with the accepted seven-association source-bound
correction. Its nd/ad symbols explicitly attach to the whole structural context;
this binding choice makes all required data available without claiming that the
paper drew those dashed attachments. [MCS/Basic.lean](../Clafer/MCS/Basic.lean)
and [Laws.lean](../Clafer/MCS/Laws.lean) separate structural validity from
formula generation and gluing. Cojoining equates role-graph vertices. Arrow slots,
resolved referents and repeated names remain separate.

The [sample](../Clafer/MCS/Examples.lean) validates a nonempty family including
int/string/bool, basic/set/bag, parentless abstracts and guarded inheritance.
No third-party implementation or publication text is copied into these modules.

## Pinned compiler compatibility audit

The [resolved-IR comparison contract](resolved-ir-comparison.md) records the
documentation/source audit specified in the [compiler compatibility audit issue](https://github.com/kbak/clafer-semantics/issues/49),
under the [bounded semantic comparison project issue](https://github.com/kbak/clafer-semantics/issues/48), against compiler commit
[`15adb2216909421bcb5022174d2d84ef2b42307c`](https://github.com/gsdlab/clafer/tree/15adb2216909421bcb5022174d2d84ef2b42307c)
(package 0.5.3), with its MIT license inspected. Its matrix maps exact compiler
passes/fields to SoSyM §§5.3–5.5, 6.1–6.2/Figures 16/22/23, Appendices 1–3/5
and current Lean declarations. Compiler behavior is supplementary evidence,
not a replacement semantic authority. The original documentation-only audit
incorporated no compiler code or fixtures.

The audit retains the accepted [span composition (Q1)](sources.md#span-composition-q1-research-for-4), [common-target disjointness (Q8)](sources.md#predicate-contracts-and-the-accepted-q8-correction) and top-level abstract corrections. The
[comparison decisions D1–D8](resolved-ir-comparison.md#decisions-accepted-locations-and-dependency-boundaries) distinguish effective/default provenance, nested
abstractness, parentless abstract-reference keys/global cards, inheritance
refinement, hidden backend state, group interpretation, harness location and
structural prerequisites. They distinguish accepted interfaces from deferred extensions and compatibility
limits; they are not additional source corrections. Follow the contract's decision table
and example inventory before extending the supported fragment. In particular,
local Shapes and the B.5 reduct do not establish whole-model comparison;
the [structural semantics and checker bridges](structural-checker.md) supply the
separate whole-model interpretation and finite correctness results.

The current executable dependency is
[`6750e6f591b2131549122c13dee94d3d2257eaea`](https://github.com/gsdlab/clafer/tree/6750e6f591b2131549122c13dee94d3d2257eaea)
(package 0.5.4). Its MIT license is unchanged. The
[0.5.4 assessment](resolved-ir-comparison.md#compiler-054-compatibility) records
changes to the matrix's names/defaults/groups/positions/options entries while
retaining the historical audit above. The [import guide](resolved-import.md)
owns current archive/schema/build identities. The paper remains semantic authority.

## Structural Compile contract

[Compile](compile.md) implements the preorder traversal and unique-identifier
construction of SoSyM §6.2.4 (PDF p.23), with the existing Figure 23/Appendix 5
Tables 5–8 disciplines (PDF pp.22–23). It uses the accepted [guarded Appendix 5 clauses (Q2)](mcs-invariants.md#appendix-e-inventory) and [resolved-referent identity (Q4)](sources.md#mcs-gluing-and-the-approved-q4-rule) representation
and [Q9](mcs-invariants.md#figure-23-source-multiplicity-correction) presence/ownership corrections without selecting a gluing quotient.
Repeated references to one uniquely declared `DeclId` share its resolved class;
separate declaration heads retain fresh identities even when names coincide.
This sharing contract was accepted in the
[Compile issue](https://github.com/kbak/clafer-semantics/issues/22) and is consistent with §6.2.5's one class in multiple roles. The inspected
2000 p.354 passage supports the name/semantic-marker distinction but does not
settle general [Q4](sources.md#mcs-gluing-and-the-approved-q4-rule) gluing.

The accepted Compile-specific precondition `0 < support.mapCount` excludes
zero-map constraints from this transformation, preserving generic constraint
input and `DPGraph` arities and the existing MCS total-args promise. Constraint
symbols use the delivered occurrence-indexed signature, with no expression
interpretation. Generated local predicates are exactly the existing individual
Shape inventory plus guarded inclusion predicates; group/abstract semantic
translation and full constraint preservation remain outside this increment.

The [accepted group-inheritance contract](group-compilation.md) extends this structural
result through a separate generated component. Abstract groups are inheritable
bounds, applied at concrete contexts over the union of own and super-hierarchy
child heads. This follows the pinned compiler's `genGroupConst`, `analyzeGCard`,
`findHierarchy` and inheritance regressions, while empty inventories deliberately
retain literal count zero instead of the compiler's skip. The contract records
all six immutable compiler links and the comparison with §4.2.2, §6.2.2, D.4 and
Appendix 3.

The authored/effective default policy is unchanged. Vertex-only formulas use B.4
Definition 8 without claiming Figure 23 total args for the complete union.
The [finite structural semantics](structural-checker.md) supplies the selected
count/representation interface; [inherited realization](inherited-realization.md)
establishes inherited fields and commuting restrictions. Typed relation/count and exact union
gluing proofs establish the bounded correspondence, not whole-language semantics.

## MCS gluing and the approved Q4 rule

Primary source: SoSyM §6.2.5 (PDF p.23) describes labeling from class/map roles to
the classes/maps they denote and preservation of predicate declarations.
Appendix B.4 Definition 10 (PDF p.31) supplies the declaration-preserving DP-morphism
condition. The [resolved-referent gluing issue](https://github.com/kbak/clafer-semantics/issues/23)
selects the equality rule: equal classReferent/mapReferent values, with endpoint
and metadata consistency required of the input. This is an explicit adopted
interpretation of the paper's labels, not a theorem deriving identity from names.

The recovered Diskin et al. (2000) §3.3 p.354 distinction between names and
predefined semantic markers and CSRG-566 Definitions 5.1/5.4 (pp.34–36) support
keeping names, roles and semantic identities separate. Their exact provenance
and audit limits remain [recorded above](#universal-arrow-foundations-partial-source-assessment).
Neither supporting passage alone selects [Q4](sources.md#mcs-gluing-and-the-approved-q4-rule). No third-party text or code is
copied into the new modules.

| Source/decision | Lean implementation and proof |
| --- | --- |
| §6.2.5, approved [Q4](sources.md#mcs-gluing-and-the-approved-q4-rule) | [Gluing.lean](../Clafer/MCS/Gluing.lean): `Incidence`, `Compatible`, used `Class`/`Map`, `source_label`, `target_label`, `classLabel_eq_iff`, `labeledArrow_eq_iff`, `label` |
| B.4 Definitions 8–10 | `diagram`, `declared_iff`, `labelHom`, `translated_vertex`, `translated_arrow`: exact translated image and complete binding postcomposition |
| §6.1.1–3, Table 8 (see Appendix 5) | `raw_wellFormed`, `cd`; [Origins.lean](../Clafer/MCS/Gluing/Origins.lean): `originAnnotation`, `annotations_head`, `naming_of_valid`, `ofValid` |
| [Q4](sources.md#mcs-gluing-and-the-approved-q4-rule) acceptance boundaries | [Examples.lean](../Clafer/MCS/Gluing/Examples.lean) and [Boundaries.lean](../Clafer/MCS/Gluing/Boundaries.lean): intentional merges, repeated names, distinct parallel maps, conflicts, source-key/target-collision and DP/CD-default distinctions |

The input's effective defaults are explicit hypotheses, since arbitrary valid
MCS formula banks need not contain ordinary setValued or inclusion declarations.
The exact image is never silently completed. Bag mode and source key/total-args
semantics remain unchanged. No compiler integration, general constraint semantics,
model-existence theorem or global pushout claim follows.

## Finite structural candidate semantics

The accepted [structural comparison boundary](resolved-ir-comparison.md) uses the same primary
published SoSyM article and the existing [span composition (Q1)](sources.md#span-composition-q1-research-for-4), [common-target disjointness (Q8)](sources.md#predicate-contracts-and-the-accepted-q8-correction), parentless-abstract and Appendix 5
corrections. Effective input retains identity and numeric bounds without
reconstructing source/default provenance. The compiler pin remains comparison
context only; its Alloy facts do not define the Lean relation.

| Source | Structural obligation |
| --- | --- |
| §§5.3.1–3, 5.4; Table 4; A.1 | Finite supplied objects, containment/reference tables, exact parent/dereference multiplicity, local lower/upper bounds and set/bag reference occurrences |
| §5.3.4–5, §5.5; Figure 18; Appendix 5 | Root and abstract membership, shared-object subtype inclusion, abstract cover and common-target sibling disjointness; finite acyclic hierarchies establish containment reachability |
| Appendix 3; §6.2.2 | Effective own-child group bounds count the union of child head objects; inherited/abstract group extensions remain unsupported |
| B.1 Definitions 1–5/Theorems 1–2, B.2.1–2 | Ordinary relation-tuple links and link-isomorphic representation; composite target spans preserve composable occurrences under [Q1](sources.md#span-composition-q1-research-for-4) |
| §6.1–6.2, B.4 Definitions 6–10/B.5 | Interpretation into the existing bounded subset/span graph and explicit connection with the selected compiled structural declarations; global clauses supplement the local bank |

The shared ambient carrier represents unrelated overlap as well as subtype
sharing. Clafer satisfaction adds the declaration-disjointness clarification below;
generic `DPGraph`/`FormalCD` models remain unrestricted. No primitive value domain
or authored/default theorem is introduced. The [requirements](spec.md#whole-model-structural-satisfaction-and-interpretation)
and [trace map](clafer-trace.md) distinguish definitions, implementation proofs and
whole-model boundary tests.

The [small Lean walkthrough](getting-started.md) specializes this existing
contract to a manually resolved phone with an optional camera. Its
[checked declarations](../Clafer/Examples/Walkthrough.lean) exercise containment
and local cardinality with zero, one and two cameras. The displayed Clafer text
is explanatory input, not evidence of a verified parser or elaborator.

## Declaration disjointness clarification

The [declaration-disjointness issue](https://github.com/kbak/clafer-semantics/issues/87) adopts the static Alloy
translation's declaration-identity rule: distinct resolved declaration extents
are disjoint unless one declaration reaches the other through super edges.
This includes nested declarations and different inheritance trees. Containment
ancestry, equal names and reference targets do not establish comparability.
Subtype and supertype membership share the same object. Inherited context views
restrict existing field objects and links and are not fresh declarations.

The primary source correspondence has these limits:

| Passage | What it supplies; limit of the correspondence |
| --- | --- |
| §5.3.1–3/Table 4, PDF pp.14–15; §5.3.4–5, PDF p.15 and §5.4, PDF p.17 | Basic/reference declaration structure, abstract realization, root and containment. These do not state the global partition of all incomparable declaration heads. |
| §5.5/Figures 18–19, PDF p.17 | Identity-preserving inheritance, inclusion and inherited features. Super chains share objects; containment and repeated names are different relations. |
| §6.1.2/Figure 21, PDF pp.19–20; §6.2.3–5/Figure 23; Tables 6–8 (see Appendix 5), PDF pp.22–23 | Explicit inclusion and abstract-family cover/disjointness with accepted [Q8](sources.md#predicate-contracts-and-the-accepted-q8-correction). Local Shapes do not supply global disjointness between arbitrary unrelated heads. |
| B.5, PDF p.31; Appendix 6, PDF p.34 | Shared subset/span interpretation and inherited component/version/options views. Generic subset/span objects are not partitioned; a field's context restriction keeps its object/link identity. |

The paper does not uniquely determine the additional global rule. This is a
maintainer-adopted clarification, consistent with the selected translation, not a
theorem inferred from compiler agreement. Supplementary evidence is
[`Generator/Alloy.hs`](https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Generator/Alloy.hs#L144-L156)
(`claferDecl`/`genExtends`, lines 144–156), at the existing MIT-licensed
pin `15adb2216909421bcb5022174d2d84ef2b42307c`. The
[Alloy language reference, signatures](https://alloytools.org/spec.html#signatures)
specifies disjoint top-level signatures and disjoint sibling `extends` signatures;
subtypes are subsets of their parents. The accepted comparison profile remains
Alloy 6.2.0. These constraints propagate to incomparable descendants; inherited
fields remain relations over their existing signature objects.

The independent `Configuration.DeclarationDisjoint` obligation and its finite
ancestry decision implement this rule. Compile/gluing and arbitrary-span
normalization expose it as a global condition alongside the actual generated
bank. Admission, raw representation, exact pins and enumeration keep overlapping
candidates; the [bounded comparison regression](bounded-comparison.md) requires `agree_violates`. Reference
occurrences may still share targets according to the existing per-parent set/bag
rules. Group unions, inherited views, [span composition (Q1)](sources.md#span-composition-q1-research-for-4) and [common-target disjointness (Q8)](sources.md#predicate-contracts-and-the-accepted-q8-correction) retain their meanings.

<a id="appendix-f-inherited-realization-clarification"></a>

## Appendix 6 inherited realization clarification

The accepted nested-abstractness, inheritance and group combinations, together
with the Appendix 6 source inventory, are recorded in
[inherited realization](inherited-realization.md). This separate extension
preserves the finite checker's guarded domain: ordinary effective-abstract fields
are realized by their parents, explicit abstracts retain direct-subtype cover
and [Q8](sources.md#predicate-contracts-and-the-accepted-q8-correction) disjointness, and inherited maps restrict shared objects and links.
The equal-parent declaration rule remains in force; broader refinement is
unsupported. The linked contract records all 26 declarations, seven super edges,
five explicit abstract families, three xor inventories and twelve conjuncts,
with the pinned primary and supplementary source identities.

<a id="independent-constraint-meaning-and-appendix-f-elaboration"></a>

## Independent constraint meaning and Appendix 6 elaboration

The primary source is the same SHA-256-identified published SoSyM article, Appendix
D.1–D.4/Figure 28 PDF pp.32–34 and Appendix 6 PDF p.34. [Q3](sources.md#appendix-d-rule-dispositions-q3) selects ordinary
intersection; [Q7](sources.md#figure-21b-and-the-accepted-q7-correction) retains display >= server with no Appendix 6 optional-server
guard. The [denotation contract](constraint-denotation.md) describes the exact
partiality and local finite-cardinality boundary. The [inherited inventory](inherited-realization.md#constraint-scope-handoff)
records every c01–c12 expansion; `Telematics.Expressions.inventory` supplies its
typed body and checked support against that same complete structural AST.
Global abstract navigation uses a resolved extent, since a parentless abstract
has no synthetic-root head map. This is a resolved-core representation choice;
no general textual resolver or frontend correctness is asserted.

B.1/B.2 link identities remain in model spans. `ambientRelation`, `image_span`
and `join_span` make the D.4 relational reduction explicit, while head counts
retain different reference objects at equal targets. Source operations do not
justify imposing a finite universe of primitive values. The complete integer
realization and partial singleton extraction therefore have their own
[contract](integer-extraction.md). The expression environments reuse the
[inherited realization](inherited-realization.md) nonprimitive carrier; the
[selected preservation bridge](constraint-preservation.md) states the additional
primitive and admissible-model assumptions needed to compose these meanings. No supplementary compiler
claim or third-party implementation is introduced by these equations.

## Representative compilation and gluing

The [coverage matrix](representative-models.md) connects §6.2.4–5, selected
Figures 16, 18, 21–23 and Appendix 6 PDF p.34 to concrete checked examples. It reuses
the published article and the [d01–d26/c01–c12 inventory](inherited-realization.md),
without adding source interpretations or copying third-party material.
`Examples.Integration` applies Compile/gluing correctness and generated xor
predicates to concrete witnesses. `Examples.VersionCompilation` retains the
mandatory, unguarded c02 comparison and connects its navigation hypotheses to
emitted local declarations under an explicit integer-domain interpretation.
Structural attachment and operand definedness do not establish general expression
preservation or full Appendix 6 satisfaction. The independent expression meanings
are supplied by the [denotation contract](constraint-denotation.md); their compiled
bridge is supplied by the [selected preservation contract](constraint-preservation.md),
with the [complete fixture](telematics.md) supplying simultaneous satisfaction.

## Selected constraint preservation

The [preservation contract](constraint-preservation.md) connects SoSyM §6.2.2–5
and Appendix D.4 to B.4 Definition 10/B.5 using the actual generated support
bindings and label map. Predicate meanings universally evaluate typed bodies at
context objects; explicit external domains are closed by the existing universal
constructor. Original links, complete arities and [source decisions Q1–Q9](sources.md#question-dispositions-and-validation-tasks) remain unchanged. The
whole-model result composes the generated local/group/inherited/abstract bank
with these fixed meanings and retains its selected configuration assumptions.
It is not a universal source-text compiler-correctness result.

The twelve [Appendix 6 bodies](inherited-realization.md#constraint-scope-handoff)
all observe real navigation maps, so positive Compile support needs no dummy
edge. The finite structural projection's primitive `1..1` placeholder is separate
from the complete integer domain required by [integer extraction](integer-extraction.md)
and [constraint denotation](constraint-denotation.md). Section 5.3.5 PDF p.15 identifies
a primitive head with its value class; a complete integer-bearing fixture needs
an unrestricted primitive-head bound and actual root containment. The existing
resolved contract already permits those explicit fields; ordinary version/server
bounds and the [guarded finite checker](structural-checker.md) are unchanged. No combined model is inferred
by replacing only the primitive set in the old finite structural witness.

<a id="complete-appendix-f-model"></a>

## Complete Appendix 6 model

[The complete model](telematics.md) reuses the reviewed d01–d26 and c01–c12
inventory, including the manually checked PDF p.34 indentation and final selections.
It retains the accepted source corrections and inherited-field/group policies,
reference-head counts, global plaECU extents, c07's
implication vacuity and c02's unguarded display ≥ server comparison. The selected
primitive correction gives int unrestricted bounds and actual root containment;
it preserves mandatory version/server bounds and the mathematical Int domain.
No additional source interpretation or supplementary compiler claim is introduced.
The kernel-checked correspondence concerns this hand-authored resolved input;
source parsing, name resolution, default insertion and coercion elaboration
remain manually reviewed boundaries.

<a id="pinned-resolved-importer-51"></a>

## Pinned resolved importer

[The import protocol](resolved-import.md) implements the accepted effective-core
boundary from SoSyM §§5.3–5.5 and §6.2.2/Figure 22, with the selected [structural
interpretation](structural-checker.md). Appendix 3 explains the authored/default metadata gap; imported
effective values do not establish historical provenance or default correctness.

Compiler evidence is pinned to
[`gsdlab/clafer@6750e6f591b2131549122c13dee94d3d2257eaea`](https://github.com/gsdlab/clafer/tree/6750e6f591b2131549122c13dee94d3d2257eaea).
`Intermediate/Intclafer.hs` owns the serialized types; `Language/Clafer.hs`
`analyze`/`generate` fixes the paired boundary. `Common.createUidIClaferMap`,
`Optimizer.optimizeModule`/`optimizeClafer`/`makeZeroUnusedAbs`, and
`Generator/Alloy.hs` `genModule`, `genRelations`, `genOptCard`, `genParentConst`,
`genGroupConst` and `genSetUniquenessConstraint` identify the retained hidden-state
and backend-processing obligations. `Front/AbsClafer.hs` and `LexClafer.x` supply
the pre-desugaring constructor/token audit. The original lts-22.44 resolver uses
`nikomi/json-builder@fef4700b53da502f8d70d2106c9f4b65e1a69b3f` and
`gsdlab/StringMap@2ce0adb947adaa5581d347ce8555ec76db44d815`.

The compiler archive hash and extraction trust boundary are in the import guide.
The exact copied upstream fixture retains [MIT attribution](../tests/fixtures/importer/LICENSE-upstream).
The external observational generator copy retains its upstream license header.
Kernel-checked importer representation is separate from upstream parser/type/
optimization correctness and from the separate [bounded Alloy comparison](bounded-comparison.md).

## Reusable semantic foundations

The [span/navigation laws](dpgraph-trace.md#reusable-span-and-navigation-laws-proofs)
are derived from Appendix 2 mappings (legacy B.1 Definitions 1–5), composition
(Q1), Table 3 and Appendix 1. Moving these statements into DPGraph adds no
functionality, finiteness or identity hypothesis to generic spans.
The [exact-image law](dpgraph-trace.md#exact-declaration-image-semantics-proofs)
is a specialization of Appendix 2 satisfaction under translation (legacy B.5),
with explicit equality of declaration images; it is not unrestricted model reflection.

[Referent graph construction](../DPGraph/Gluing.lean) and
[metadata descent](../FormalCD/Gluing.lean) factor the existing §6.2.5 construction
and §§6.1.1–3 validity proof. Equal-referent identification remains the accepted
Q4 policy in Clafer; the generic construction takes referents as parameters and
inserts no defaults. It asserts no new global pushout or object-diagram equivalence.

[Integer realization](../FormalCD/Integer.lean) factors the explicit §6.1/Figure 21
domain and the accepted Appendix 4 partial-singleton bridge. Its extraction error
API remains a selected library contract, not a verbatim paper definition. The
Figure 21 guarded VC meaning and Clafer expression meanings retain their separate
source obligations. No source correction, supported fragment or comparison pin changes.
