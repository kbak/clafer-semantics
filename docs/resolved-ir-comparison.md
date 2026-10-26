# Resolved structural IR comparison contract

`impl~resolved-ir-comparison-contract~1`

This contract defines which effective compiler inputs and finite candidates can
be compared with the selected Lean structural semantics. The supported fragment
is deliberately guarded: it excludes the language forms marked X or D below,
user expressions, production parsing/generation/optimization and general solver
integration. Compiler behavior remains supplementary evidence for the selected
paper semantics.

Reusable whole-model semantics and representation bridges live in
`Clafer/Semantics/`; finite candidates and the verified checker live in
`Clafer/Verification/`. The [resolved importer and paired capture](resolved-import.md)
use `Clafer/Verification/` and `scripts/verification/`, with fixtures under `tests/`.
The [bounded comparison harness](bounded-comparison.md) supplies candidate pinning,
decoding, enumeration and replay under `scripts/verification/` using the solver
profile specified below.

The [compatibility-audit issue](https://github.com/kbak/clafer-semantics/issues/49) and
[contract review PR](https://github.com/kbak/clafer-semantics/pull/55) record acceptance
within the [bounded comparison project issue](https://github.com/kbak/clafer-semantics/issues/48).
The [finite structural semantics issue](https://github.com/kbak/clafer-semantics/issues/50)
records the checker and representation obligations derived from this contract.

The [decision table](#decisions-accepted-locations-and-dependency-boundaries)
defines [comparison decisions D1–D8](resolved-ir-comparison.md#decisions-accepted-locations-and-dependency-boundaries); the [compatibility matrix](#guarded-compatibility-matrix) distinguishes
supported (S), excluded (X) and decision-dependent (D) forms. Compiler agreement
is tested against the independent structural meaning; it does not define that meaning.

Covers:
- `req~resolved-ir-comparison-contract~1`

## Source identities and audit boundary

The primary reference is the [published SoSyM source](sources.md#primary-source),
37-page publisher e-offprint SHA-256 `653fc7868637680c44b6176d8ff643ec20149534fe1681ea4fc4ce636db76f2d`.
Locators below use its one-based PDF pages and the explicit legacy-subsection
[aliases](sources.md#published-locators-and-legacy-aliases). The `52-S/v1` manifest
retains its original preprint hash for replay compatibility; that historical pin
is distinct from this current citation convention. The original matrix observations use
[gsdlab/clafer at 15adb2216909421bcb5022174d2d84ef2b42307c][compiler], whose
`clafer.cabal` says 0.5.3. The comparison with existing Lean declarations starts
from planning baseline `kbak/clafer-lean` at
`e920d72281a9fd5a8c684a5c759083471f48feea` and is cross-checked against
`1d6567433e1d20af9a457b008ef8a50644412018` and
`64ebec9817c048019c744330a9a6609ba722b90c`. The cited Clafer syntax and Shapes
are unchanged across these revisions; the first cross-check also supplies the
derived functional-key correspondence identified below, and the second supplies
the typed constraint extension. Those revisions established typed syntax. The separate
[denotation extension](constraint-denotation.md) now supplies constraint meanings;
user constraints remain excluded from this comparison fragment.
Later revisions require a new matrix audit, even if a version string is unchanged.

### Compiler 0.5.4 compatibility

The executable [import profile](resolved-import.md) uses
[0.5.4 at `6750e6f591b2131549122c13dee94d3d2257eaea`](https://github.com/gsdlab/clafer/tree/6750e6f591b2131549122c13dee94d3d2257eaea),
as requested in [the dependency update](https://github.com/kbak/clafer-semantics/issues/115).
The original matrix and its immutable 0.5.3 locators remain historical evidence;
this assessment records the affected entries for the current profile. The MIT
license, source archive, resolver and build identities are checked independently.

| Affected matrix area | 0.5.4 observation and disposition |
| --- | --- |
| Names, resolved identities and bindings | `ResolverInheritance.uidIdent` escapes apostrophes as `__prime__`; `renameClafer'` counts collisions after escaping. Names stay unchanged. Import preserves emitted UIDs; spelling/collision comparison and replay exercise distinct identities. |
| Effective local/group bounds and D1 | `analyzeCard` makes omitted children optional under all keyword groups, including `opt`. `desugarGCard` sets `_isKeyword` only for keywords. Numeric groups except `0..*` make children optional. The adopted [child-default policy](sources.md#current-child-default-policy) now agrees on these group cases, deliberately evolving the paper's defaults. Effective values remain admitted without inventing authored provenance. |
| Empty/unreachable concrete groups and D6 | `Language.Clafer.unsatisfiableGroups` rejects a concrete group's lower bound above its own/inherited children's summed upper bounds. Abstract groups are exempt. Rejection is `compiler_rejected`, including optional concrete contexts; it is not a Lean unsatisfiability verdict. The positive-empty-group S exclusion and independent zero-count meaning remain. |
| IR fields and same-generation boundary | `Intclafer` serializes real spans. The single-fragment library capture leaves `inputFiles` empty, so both JSON and receipt use nullable `{start,end}` spans. The CLI's `spansInFiles` file mapping is outside the profile. Span validation preserves exact IR/map comparisons. |
| Layout, parse failures and excluded forms | `LayoutResolver` ignores leading comments for indentation; `Language.Clafer.parse` rejects multiple same-line sibling declarations. These parser changes affect accepted source text, not the resolved S contract. The pre-desugaring AST audit still rejects expressions, temporal forms, initializers, enums and escapes. |
| Options, imports and backend state | New import options stay empty/default; source directives remain rejected. No file/URL loader is invoked. `Generator/Alloy.hs`, `Common.hs`, `ResolverName.hs` and `StringAnalyzer.hs` are byte-identical to the audited pin. The optimizer change only prevents resolver skipping for apostrophe names; this profile already disables skipping. Existing ownership, cardinality, registry and no-string guards remain. |

The unchanged Alloy group generator retains the documented counting differences
outside S; these fixes do not establish general group equivalence. HTML escaping,
CLI import loading and error rendering are outside paired capture. The effective
core, independent Lean meanings, S combination guards and theorem hypotheses are
unchanged. Live capture, decoder mutation and bounded comparison tests exercise
this profile; they supply execution evidence, not source-compiler correctness.

The compiler is supplementary implementation evidence. Its [MIT license][license]
was inspected (Generative Software Development Lab, 2012–2019; Intelligent
Systems Development Lab, 2019–2023). The importer fixtures retain the upstream MIT license; the capture builder
retains the license in its external observational generator copy. The original
fixture inventory is source analysis; actual compiler executions are described
in [the import protocol](resolved-import.md). No paper figures are copied.
The relevant paper text and the existing accepted figure/correction audit were
cross-checked against the declarations listed below; this is not an audit of
every compiler feature or a fresh visual audit of the whole paper.

| Source handle | Inspected declarations/pass and purpose |
| --- | --- |
| C1: [Language/Clafer.hs][pipeline] | `analyze`, `generate`, `iExpBasedChecks`, `iClaferBasedChecks`: resolved/optimized IR, paired JSON/Alloy outputs, static/LTL dispatch |
| C2: [Intermediate/Intclafer.hs][ir] | `IModule`, `IElement`, `IClafer`, `IClaferModifiers`, `IReference`, `IGCard`, `PExp`, `IExp`, `ClaferBinding`, `IType`, JSON instances |
| C3: [Generator/Alloy.hs][alloy] | `genModule`, `genClafer`, `genOptCard`, `genRelations`, `genConstraints`, `genSetUniquenessConstraint`, `genGroupConst`, parent/reference subrelation generators |
| C4: [Common.hs][common] and [ClaferT.hs][environment] | `GEnv`, `createUidIClaferMap`, `findHierarchy`, `isProperNesting`, `isProperRefinement`, `ClaferEnv`; implicit identities and backend context |
| C5: [Resolver.hs][resolver], [ResolverInheritance.hs][inheritance], [Desugarer.hs][desugarer] | `nameClafer`, `resolveNamesModule`, `resolveNClafer`, `resolveNSuper`, `analyzeCard`, `analyzeGCard`, `desugarGCard`, `desugarModifiers` |
| C6: [Optimizer.hs][optimizer], [StringAnalyzer.hs][strings] | `optimizeModule`, `optimizeClafer`, `makeZeroUnusedAbs`, `remUnusedAbs`, `astrModule`; global-card and backend transformations |
| C7: [ClaferArgs.hs][args], [CHANGES.md][changes] | Complete option inventory; 0.5 behavioral extension, 0.5.3 fixes and Alloy 6 migration |
| C8: [set_and_bag_references.cfr][bag-fixture] and [Alloy regression][bag-regression] | Three reference-head objects; only the set version emits distinct-target uniqueness. Related `.js.reg`, `.html.reg`, `.dot.reg` are presentation/backend cross-checks, not semantics proofs. |

## Guarded compatibility matrix

Lean names in this table denote **current declarations**, except where explicitly
called missing. `Clafer` names are in [Syntax](../Clafer/Syntax.lean),
[Shape](../Clafer/Shape.lean), [Shape.Diagram](../Clafer/Shape/Diagram.lean) or
[Examples](../Clafer/Examples.lean). Predicate names are in
[DPGraph.Predicates.Meaning](../DPGraph/Predicates/Meaning.lean), with the derived
key correspondence in [FunctionalKey](../DPGraph/Predicates/FunctionalKey.lean).
Generic satisfaction and reduct names are in [DPGraph.Semantics](../DPGraph/Semantics.lean).
Their [trace artifacts](clafer-trace.md) distinguish syntax proofs from satisfaction.
S = accepted structural support subject to the stated guard; X = excluded from version 1;
D = awaiting a decision, rejected by the version-1 admission gate for now.

| IR form / behavior | SoSyM locator | Lean anchor / comparison boundary | Compiler/version observation and fragment disposition |
| --- | --- | --- | --- |
| Basic declarations, finite nesting, repeated display names | §5.3.1 PDF p.14, §5.4 PDF p.17; §6.2.2 Fig.22 PDF p.21 | `Declaration`, `Tree`, `AST`, `AST.WellFormed.unique_ids`, `parent_depth` | **S**: C2/C5 UIDs define identity; nesting agrees with `_parentUID`. Do not merge equal `_ident`. Reference cycles are permitted; containment/super cycles are rejected. |
| Effective clafer intervals and unbounded upper limits | §5.2/Table 4 PDF pp.14–15; App.3/Fig.27 PDF p.32; A.1 PDF p.28 | `Multiplicity.effective`, `ValidRange`, `Range`, `TargetMultiplicity` | **S**: analyzed `_card`, upper `-1` only for infinity. Count head/link occurrences, not distinct dereferenced targets. `_glCard` is separate backend metadata (C3/C6). |
| Effective group bounds on concrete parents | App.3 PDF p.32; §6.2.2 PDF p.21 | `GroupMultiplicity.effective`; `Configuration.Groups` in [structural semantics](structural-checker.md) | **S** for own children without inheritance overlap. C3 `genGroupConst` counts the union of child-object sets, not present child declarations. Two bag heads pointing to one target count twice. It skips abstract parents and empty child inventories; inherited/overlapping groups and positive lower bounds with no declared children are **D**, [D6](resolved-ir-comparison.md#decision-d6). |
| Authored/default group policy | App.3 PDF p.32 | `Defaults`, `GroupCard.childDefault`, `GroupMultiplicity.authored` | **D** as a source-default correspondence: C5 defaults concrete nested children of any non-`0..*` group to `0..1`; Lean makes only keyword-group children optional. C5 `opt` has `0..*`, so its concrete children default to `1..1`, unlike Lean. This is the historical 0.5.3 comparison; the [current policy](sources.md#current-child-default-policy) and 0.5.4 assessment supersede these default differences. S still uses only effective values under [D1](resolved-ir-comparison.md#decision-d1). |
| Top-level abstract basic, concrete subtypes | §5.3.4–5 PDF p.15, §5.5 PDF p.17; §6.2.3/Fig.23; Table 7 (see Appendix 5) | `Origin`, `AST.WellFormed.parentless_abstract`, `Roles.head`, `root_only_head`; `Cover`, `Disjoint` | **S** for leaf abstract basics with `_card = [0,-1]` or optimizer-forced `[0,0]`, no reference inherited by a basic subtype. Keep head, omit source/parent maps under the accepted correction. Abstract cover/disjointness is supplied by the [whole-model structural semantics](structural-checker.md); Alloy uses `abstract sig`/`extends`. |
| Top-level abstract multiplicity restrictions | Same, Table 4; no parent fiber at a parentless Shape | `Shape.declarations` applies multiplicity only where head/target maps exist | **D**, [D3](resolved-ir-comparison.md#decision-d3): C3 can emit global signature bounds for abstracts; these are not a local parent-fiber predicate. `[0,0]` is admissible only with a recorded unused-abstract condition making cover empty. |
| Nested abstractness / children of abstract declarations | §5.3.4 PDF p.15 | `Defaults` propagates abstractness; `AST.WellFormed.nested_abstract` | **D**, [D2](resolved-ir-comparison.md#decision-d2): C5 `desugarModifiers`/`resolveNClafer` retain the declared abstract flag; they do not implement Lean's containment propagation. Explicit nested abstract bodies, relocation and redefinition also require review against both the [MCS disciplines](mcs-invariants.md) and [gluing contract](architecture.md#mcs-gluing). |
| Single inheritance of basics, including a concrete nested basic extending a top-level abstract leaf | §5.5 PDF p.17/Fig.18; Table 6 (see Appendix 5) PDF p.22 | `Kind.CanExtend`, `inheritance_parent`, `inheritance_rank`, `Shape.Inclusions`; `Inclusion` | **S** with an abstract basic super, no inherited child/reference fields, no overlapping group roles. The same object inhabits subtype and supertype. C3 emits `extends`; cover/disjointness use accepted [Q8](sources.md#predicate-contracts-and-the-accepted-q8-correction). |
| Nested-parent refinement, inherited references, target narrowing or kind refinement | §5.5 PDF p.17; Tables 5–8 (see Appendix 5) | `inheritance_parent` requires equal parent IDs when the super is parented; `Shape.OptionalInclusions` is local only | **D**, [D4](resolved-ir-comparison.md#decision-d4): C4/C3 allow a child's parent to extend the super's parent, and generate parent/reference subrelations. C5 also relocates some abstracts. Set-over-bag is allowed by Lean kind checks but its whole-model bridge is missing. Bag-over-set/basic-over-reference fail the Lean kind restriction. |
| Concrete superclasses and unrelated class overlap | §5.5/Fig.18; §6.1 formal CDs; B.5 set/span models | `AST.WellFormed` does not require an abstract super; `semanticGraph` permits shared objects in different subsets | Concrete supers: **X**, C5 resolves supers among abstracts. Unrelated overlap: retained as a raw negative candidate under the [explicit relation](bounded-comparison.md), rejected by the [declaration-disjointness rule](sources.md#declaration-disjointness-clarification). The [adopted clarification](sources.md#declaration-disjointness-clarification) requires super-edge comparability for shared heads without restricting generic subset/span models. |
| Direct class-target reference set/bag on a concrete declaration | §5.3.2–3/Table 4 PDF p.15; B.1 Defs.1–5/Thm.2 PDF pp.29–30 | `Reference.set/bag`, `Roles.mode`, `Shape.keyBinding`, `Key`, `SetValued`, `TargetMultiplicity` | **S**: C2 `_isSet = true/false`; C3 has one target per reference head and emits uniqueness per parent for sets. Targets must be admitted user classes, not expressions or primitive domains. |
| Top-level abstract set/bag references | §5.3.4 corrected by §6.2.3/Fig.23; Table 7 exception | `abstract_reference_no_key`, `Roles.no_parent_maps`; head, target and dereference remain | **D**, [D3](resolved-ir-comparison.md#decision-d3): C3 globally enforces distinct targets for abstract set heads when card permits repetition. Lean's accepted parentless Shape has no parent/deref pair key. Bag lacks this uniqueness but inherited reference identity still requires a bridge. Do not invent a root parent or silently add a unary key. |
| Span multiplicity, set keys and map equality | B.1 Def.2/Thm.2; B.2.1–2; B.3 Table 3; A.1 | `Span.comp`, `Span.Iso`, `Key`, `BagEquiv`, `Commutation`, `key_total_singleValued_iff` | **S** interpretation target: retain links under accepted [Q1](sources.md#span-composition-q1-research-for-4), not endpoint reduction. Keys compare output bags; the derived tuple criterion requires total, single-valued projections. Its parent/deref specialization gives uniqueness of `(parent,target)` once those hypotheses are established. No ordinary-key replacement for the generic predicate. |
| Whole-model satisfaction and compile/glue correspondence | §6.1.1–3 PDF pp.18–21; §6.2.4–5 PDF p.23; B.4 Defs.6–10/B.5 Thm.3 PDF p.31; Tables 5–8 (see Appendix 5) | `FormalCD.CD`, `DPGraph.Interpretation.Satisfies`, `IsModel`; `structural_model_iff`, `compiled_bank_iff`, `finite_model_representable` in the [checker guide](structural-checker.md) | The selected compiled bank plus explicit global obligations has a both-direction bridge. C3's facts require the separate [import representation](resolved-import.md) and [bounded comparison relation](bounded-comparison.md); reduct alone is not reflection. |
| Synthetic root, base and predefined classes | §5.3.5 PDF p.15; §6.2.2/Fig.22; Table 7 (see Appendix 5) | `Origin.syntheticRoot`, `PrimitiveDomain`, `AST.WellFormed.root_shape` | **S** for the root convention below; compiler `clafer` is not a user class or Lean root. **X** for all runtime primitive values. C4 has `integer/int/string/double/real/boolean`; Lean has selected `int/string/bool` identities, not their value domains. No automatic alias/domain translation. |
| User constraints, assertions, goals, expressions and temporal modifiers | App.4 and post-2014 features | `ConstraintBoundary` plus the resolved typed core in [Constraints.Typing](../Clafer/Constraints/Typing.lean); [constraint meanings](constraint-denotation.md) are separate from this comparison fragment | **X** for all `IEConstraint` (both `_isHard` values), `IEGoal`, and every expression except the allowed direct ID slots. C7 0.5.0 adds behavior; C1 may switch silently to `AlloyLtl` without this gate. |
| Backend escapes, enums, initializers and scope inference | No version-1 semantic contract | No current correspondence | **X**: escapes bypass JSON; enums/initializers may disappear into desugared forms. A source feature receipt is required. C7 0.5.3 fixes group scope inference, abstract-parent navigation, retained referenced abstracts and redefinition; these release notes do not prove equivalence to 2014. |

The accepted **S** fragment combines ordinary nesting, effective multiplicities
and concrete group bounds, leaf abstract basic classes, single inheritance as
guarded above, and direct class-target set/bag references. It intentionally does
not claim closure under every combination of these features. Cases marked D
remain visible obligations, rather than examples silently omitted from statistics.
Later expansion requires its own matrix row, decision and validation examples.

Here “leaf abstract” means no containment children; it may have subtypes.
Its effective group bound must be `0..*`; nontrivial abstract groups are [D6](resolved-ir-comparison.md#decision-d6).
Reference declarations participating in inheritance are [D4](resolved-ir-comparison.md#decision-d4), including a
reference extending a basic class. A group with positive lower bound requires
a nonempty child declaration inventory for S; zero realized children remains
a normal semantic test. Empty default `0..*` groups are admitted.

## Post-analysis boundary and admission

The input is the exact `iModule` stored by `analyze`: name/inheritance/cardinality
resolution, `transModule`, then `optimizeModule` (C1/C5/C6). It is not raw syntax
or an arbitrary JSON document that resembles the IR. C1 JSON serializes
`{"iModule": ...}` and may add `objectives`; it omits the rest of the compiler
environment. Deriving `ToJSON` does not establish a stable versioned external
schema. The adapter must check the pinned constructor tags/field types and reject
duplicate JSON object keys, unknown constructors and unexpected semantic fields.

Request `[JSON, Alloy]` in one `generate` call on one analyzed environment.
The Alloy branch runs `astrModule` before `genModule`; for the allowed class-only
fragment require identical structural IR before/after and an empty string map.
Hash both representations, JSON bytes, generated Alloy bytes and the paired
generation receipt. Independently compiled JSON and Alloy are not a pair merely
because filenames or source hashes match. If one process cannot export a receipt,
the run is unsupported until the minimal export below exists.

| Field | Version-1 interpretation and validation |
| --- | --- |
| `_uid`, `_ident` | Nonempty unique resolved UID; display name retained separately. Reject duplicate UIDs, reserved-UID collisions and backend symbol collisions including generated `r_...` and `..._ref` symbols. Names may repeat. |
| `_parentUID`, `_elements`, `_mDecls` | Validate nesting and parent field together. Top concrete parent `root` becomes the synthetic root; top abstract parent `clafer` becomes no parent. Other parent UIDs must name the containing declaration. Reject empty/unresolved parents, contradictions, dangling edges and cycles. Never interpret `clafer` as an object-containing parent. |
| Implicit registry | C4 inserts `root`, `clafer`, `integer`, `int`, `string`, `double`, `real`, `boolean` into `uidClaferMap`, outside the ordinary serialized declaration list. Validate this fixed registry in the receipt, not as dangling user declarations. Reject explicit user collisions. Admit no super/reference target in this registry except the absent-super convention. |
| `_super` | `null` means compiler base `clafer`, represented by no user super edge. Otherwise exactly `PExp/IClaferId` with `GlobalBind uid`, empty `_modName`, `_sident` equal to that UID, and consistent `_isTop`/`TClafer` hierarchy. Require a known abstract user super and an acyclic chain. Do not resolve `_ident` again. |
| `_reference` | `null`, or `IReference` with Boolean `_isSet`, null `_refModifier`, and a direct `PExp/IClaferId` globally bound to an admitted user class. Validate `_sident`, type hierarchy and top-level flag against the same registry. No joins, unions, target paths, implicit dereferencing or local bindings. Absence of a local reference on an inheriting clafer does not prove it has no inherited reference; those chains are [D4](resolved-ir-comparison.md#decision-d4). |
| `_card`, `_gcard._interval` | Required analyzed intervals, integral endpoints, lower ≥ 0, upper either `-1` or ≥ lower. Reject missing cards, fractional values and other negative values. `-1` is not a finite count or an Alloy integer. No default recomputation. |
| `_gcard._isKeyword` | Preserve as compiler metadata. It is not authored keyword provenance: C5 `desugarGCard` sets it for some numeric `0..n` groups too; inheritance can retain it. It cannot determine the authored group, omission or child-default theorem. |
| `_modifiers` | Preserve `_abstract`; require `_initial = false`, `_final = false` for every user declaration. Implicit registry defaults in C4 have different flags and are not user temporal syntax. No containment-based abstractness repair. |
| `_glCard` | Required valid interval, retained/hash-bound separately from local bounds. C6 computes products of analyzed cards, and `keep_unused` can change `_card` afterward. C3 uses `_glCard` for signature multiplicity and omission/shape of parent facts. Do not replace `_card` with it, ignore it as an inferred scope, or assert optimizer correctness. |
| `_pid`, `_iType`, `_inPos`, `_cinPos`, `_mName` | Expression IDs and inferred class hierarchy are metadata to validate, not declaration identities. Positions serialize as `null` (C2); JSON cannot certify source-token provenance. `_mName` is diagnostic (desugaring may retain a source URL), not an import/module system. |

The rejection inventory is closed by constructor and option whitelists. In
addition to malformed IDs/cards and D rows, reject:

- `IEConstraint` hard constraints and assertions at every depth, `IEGoal`, and
  any nonempty `objectives` payload. Do not drop these nodes to obtain a fragment.
- `IDeclPExp`, `IFunExp` (every operator, including joins, set algebra, arithmetic,
  Boolean, navigation, temporal and transition operations), `IInt`, `IReal`,
  `IDouble`, `IStr`; `IClaferId` outside the two allowed type slots; `LocalBind`,
  `NoBind`, missing/inconsistent type information, module-qualified identifiers,
  multiple supers or non-ID supers, primitive references and supers. Allowed
  type slots carry only a consistent `TClafer` hierarchy; reject `TBoolean`,
  `TString`, `TInteger`, `TDouble`, `TReal`, `TMap` and `TUnion` there.
- `FinalRefTarget`, `FinalRef`, `FinalTarget`, all `initial`/`final`/transition
  syntax, goals, assertions, initializer/constant sugar, enums, backend escapes
  (`[alloy|...|]` and other backends), and ECore conversion. Source constructs
  erased by analysis must be rejected using the source feature receipt; a plain
  JSON-only import cannot attest their absence. Unrecognized syntax is unsupported.
- LTL or other output backends, flattening, skipped resolution, automatically
  inferred scopes, external injected facts/commands, and unsupported option values.
  Basic-over-reference, bag-over-set and the unequal-parent refinement extension
  receive explicit diagnostics; they are not coerced into accepted inheritance.

## Options and state absent from JSON

The accepted profile fixes every C7 field. Effective options include source
`//# OPTIONS` processing, not just CLI arguments; version 1 rejects such directives
in source to prevent hidden overrides. Semantic source features are checked before
desugaring; formatting/comments may remain, except escapes and directives.

| Option fields | Accepted value / treatment |
| --- | --- |
| `mode` | Exactly `[JSON, Alloy]`; receipt confirms `Generator.Alloy.genModule`, never `AlloyLtl`. |
| `flatten_inheritance`, `skip_resolver` | Both false. No flattening or resolver-skipping correctness claim. |
| `keep_unused` | True, preserving UID inventory. This still invokes `makeZeroUnusedAbs`; it is not an optimization-off switch. Record the changed cards and retained `_glCard`. |
| `scope_strategy` | `None`. Replace the generated `run show for 1` command through a recorded parsed-command transformation; never use that default as the comparison scope. |
| `validate`, `afm`, `ecore2clafer` | False. Comparison invokes its own one pinned command; no compiler validation commands, AFM restriction or conversion. |
| `check_duplicates` | False (global textual names may repeat); the contract independently validates unique UIDs and resolvable edges. |
| `no_layout`, `new_layout` | False; these parsing choices are recorded but parser correctness is outside the claim. |
| `no_stats`, `alloy_mapping`, `meta_data` | True: stable output without statistics, retained diagnostic maps. These maps alone are insufficient as the semantic export. |
| `console_output`, `self_contained`, `add_graph`, `show_references`, `add_comments` | False; no additional output transformations. |
| `trace_len`, `timeout_analysis` | 10 and 0 respectively, inert for the static fragment/analysis setting. An external analysis wall-clock limit is recorded separately; timeout is an outcome, never success. |
| `minint`, `maxint` | Null; Choco-only fields do not set Alloy bitwidth. |
| `file`, `tooldir` | Logical input name and recorded tool location; content hashes establish identity. No file path is semantic evidence and private locations are omitted from public artifacts. |

C4 `GEnv` contains `identCountMap`, `expCount`, `stable`, `sClafers` and
`uidClaferMap`. None is emitted in IR JSON. The first two are fresh-ID counters;
`stable` records expansion paths; `sClafers` is an analysis inventory. C3's
`GenEnv` consumes `uidClaferMap`, effective `ClaferArgs` and the rendered scopes.
The map is produced before later transformations and is documented as needing
recreation after IR changes. Reconstructing it from JSON without comparison to
the consumed map is unjustified.

`ClaferEnv` also retains original fragments,
AST, fragment positions, `astModuleTrace` and `otherTokens`. Tokens can inject
Alloy independently of JSON. `CompilerResult` contains scopes, stringMap and
source mappings not carried by the JSON output. `genModule` further creates
field names, inheritance facts, group-child unions and cardinality optimizations.

The required extra export, implemented by the [capture adapter](resolved-import.md), is a same-generation receipt with:

1. Exact compiler/build identity, effective options, post-analysis IR hash,
   post-`astrModule` hash, empty string-map result, scopes and output hashes.
2. Pre-desugaring feature inventory and token audit (including directives,
   escapes and erased sugar), keyed to hashed source bytes. This is extraction
   evidence to review, not a source elaboration theorem.
3. The actual backend-consumed UID-map projection: each reached UID's parent,
   super hierarchy, reference kind/target, abstract flag, child UID list and
   effective cards/groups, plus fixed implicit registry records. Compare common
   fields against JSON; unexplained differences make the run unsupported.
   Hash the complete consumed map as well. Counters/`stable`/`sClafers` need no
   semantic export under this nonflattening static profile, but remain in the
   compiler-state inventory for re-audit on profile changes.
4. UID-to-Alloy signature and field declarations with endpoints/arity, inherited
   field ownership, abstract/extends edges, emitted cardinality facts and
   `_glCard`-based omissions. Every generated user signature/field must be mapped;
   source-span maps and name suffix heuristics are insufficient.

If state cannot be shown irrelevant under this profile or included in the
receipt, reject the pair. No complete `GEnv`/authored-AST export is assumed to
exist at the compiler pin; the [capture adapter](resolved-import.md) supplies this receipt.

## Effective core and the provenance bridge

The accepted `EffectiveCore` interface consists of resolved IDs, display names,
normalized root/parent edges, abstract flags, direct reference kind/target,
optional super, and effective local/group intervals. The owning Lean declaration is `Clafer.Semantics.EffectiveCore`. Compiler metadata remains in a separate
receipt. In particular it does not fabricate `Multiplicity.authored`,
`GroupMultiplicity.authored`, `Declaration.authoredAbstract` or `Defaults` proofs.

Existing `AST.WellFormed` is stronger than the serialized information: it checks
authored/default consistency under [D1](resolved-ir-comparison.md#decision-d1).
Agreement on current group defaults does not recover missing provenance. Creating an AST with all intervals
marked authored would falsely assert provenance. The projection `EffectiveCore.erase` takes an existing `Compile.Input`; a
standalone effective-core well-formedness predicate admits effective data directly. For admitted cores require unique/resolved IDs, acyclic hierarchies,
valid bounds, kind/parent/root restrictions and the chosen structural guards;
do not include authored/default consistency in that predicate.

`erasure_correspondence` proves `SatisfiesAST ↔ StructuralSatisfies` for an
existing valid Compile input with explicit `ConstraintFree` and supported-erasure
guards. `equal_erasure_satisfaction` proves equal packed erasures have equal
structural satisfaction for configurations indexed by resolved IDs. Local role
interpretation uses the canonical cojoining, effective bounds and shared heads;
global root/abstract/group obligations are additional explicit clauses.
See the [proof and representation APIs](structural-checker.md#meaning-and-interpretation).
An imported core is checked directly; no claim that every core lifts to an
authored/defaulted AST is necessary.
No parser, name-resolution, default-elaboration, optimizer-preservation
or source-program equivalence theorem follows from either approach.

## Finite candidates, identity and counts

For a fixed admitted core `e` and manual bound vector `B`, a candidate `C` has a
finite ambient set of object IDs `U`, a distinguished fresh root object `ρ`, a
subset `H_d ⊆ U` for each user class, and finite tables for every structural map.
`H_root = {ρ}`; `ρ` belongs to no user class. Compiler base `clafer` has no
candidate carrier. No primitive value carriers are constructed in version 1.
The finite ambient type will instantiate `DPGraph.Predicates.semanticGraph`;
subset membership does not clone an object.

Ordinary containment and dereference tables are relations with no duplicate
tuples. They may be empty or nonfunctional so that semantic violations can be
tested: malformed serialization and ill-typed endpoints are rejected, while
violations of required totality, bounds, cover or uniqueness are **false
satisfaction**. General spans with parallel links in an ordinary set-valued map
are outside this candidate encoding; `SpanModel.normalize_satisfies` and `finite_model_representable` justify that
each finite satisfying model in the declared whole-model domain has a representative
in this form, deriving role isomorphisms from the local bank.

For a parented declaration `d`, containment is `Q_d ⊆ H_parent × H_d` and parent
is its converse, with tuple-indexed link tokens. A concrete top-level `d` has
`Q_d = {(ρ,h) | h ∈ H_d}`. For a reference, dereference is
`R_d ⊆ H_d × H_target`. Satisfaction requires exactly one parent for each
parented head and exactly one target for each reference head. The target map
is a span whose links are **composable pairs** `(p,h,t)` with `(p,h) ∈ Q_d` and
`(h,t) ∈ R_d`; two distinct heads give two distinct links even at equal `(p,t)`.
This supplies the [Q1](sources.md#span-composition-q1-research-for-4)-preserving triangle, rather than reducing it to a relation.
Reference heads may themselves contain children.

For set references require uniqueness of `(p,t)` among those links; for bags
allow duplicates at `(p,t)`. For example three heads pointing to one target
have multiplicity three in a bag. Counting distinct target atoms would give one
and is wrong. Head multiplicity bounds the fiber of `Q_d` at each parent;
target multiplicity bounds the links of the composite span. Under the total
functional dereference condition these counts agree. A set-reference key is
the existing two-projection `Key`, not an additional global target uniqueness
condition.

Top-level abstracts have no `Q_d` or synthetic-root parent; [D3](resolved-ir-comparison.md#decision-d3)
therefore prevents importing their compiler-wide set key as a local predicate.
The existing `DPGraph.Predicates.key_total_singleValued_iff` supplies the generic
tuple-injectivity criterion under explicit totality and single-valuedness.
`Configuration.key_local_iff` connects the candidate's projections and their
totality/single-valuedness hypotheses to the interpreted Shape key.

Inheritance is subset inclusion **of the same ambient objects**, with identity
inclusion spans. Abstract heads are the union of their direct subtype heads;
distinct direct subtype images are disjoint, including the empty-family case
(abstract leaf without subtypes is empty). This uses accepted [Q8](sources.md#predicate-contracts-and-the-accepted-q8-correction). No extra object
is allocated for a supertype membership. The accepted S guard admits only
abstract supers, so Alloy `extends` disjointness is compared with this obligation.
Shared containment/reference maps and their commutation/subrelation constraints
are additional obligations when [D4](resolved-ir-comparison.md#decision-d4) is opened; head inclusion alone is insufficient.

A concrete parent's group count is the number of distinct **child head objects**
in the union of its effective child fibers. Do not count child declarations,
dereferenced targets, or the same inherited object twice. For S, child fibers
have no inheritance overlap. The generalized union, effective inherited child
inventory and behavior of abstract groups follow the [accepted D6 group
contract](group-compilation.md). Group compilation generates interpreted
declarations; the separate [inherited realization extension](inherited-realization.md)
supplies inherited-family realization and its whole-model bridge. Neither extension
enlarges the guarded comparison domain.

User objects must occur in some user head; arbitrary unused ambient garbage is
not part of a candidate. Satisfaction must enforce the selected root/reachability
conditions through concrete containment; failing them is a semantic violation,
not an admission filter. `structural_reaches` proves reachability from the other selected conditions
and the well-formedness/support hypotheses. Similarly, keep potential
overlap between unrelated head subsets available to the checker. The adopted [declaration-disjointness
obligation](sources.md#declaration-disjointness-clarification) rejects it as a semantic violation, without
changing admission, representation or enumeration.

Renaming uses a bijection on used objects fixing `ρ`,
preserving each class membership and map endpoint, together with independent
bijections on link occurrences. Alloy atom spelling, record order and local link
IDs have no semantic force. Reference-head identity and shared inherited
membership must survive the bijection.

For finite exhaustive enumeration use canonical object IDs `0..n-1` plus `ρ`,
with `n` bounded by the sum of user signature scopes. Enumerate every membership
subset and typed relation table on that finite universe; derived links are indexed
by their finite tuples. Arbitrary fresh string/link names are not new candidates.
Deduplication by isomorphism is optional and requires a completeness argument.

## Same-candidate Alloy pinning and decoding

Checking whether the generated model has *some* solution cannot compare a
particular `C`. Let `A(e,o)` be the hashed generated declarations/facts for the
receipt's options. Version 1 uses `A(e,o) ∧ Pin(C)` with an explicitly selected
command and bound vector. The implemented pinning relation must:

1. Existentially name exactly the used non-root objects with pairwise distinct
   atom variables; assert **equalities** for every user signature's full extent
   and every field's full tuple relation. Include empty extents/relations and
   inherited fields with their declaring signature. Membership constraints or
   cardinalities alone do not pin a candidate. Use quantified variables, not new
   subtype signatures that change `abstract`/`extends` coverage.
2. Encode overlapping subtype/super membership with the same variable and encode
   each reference head as its own atom. Pin every local reference field exactly;
   never pin only the reduced source-to-target relation. No free containment or
   dereference tuple may be filled by the solver.
3. Reconstruct the virtual root singleton and its top-level containment during
   decoding; no generated root signature is expected. Account for `Int`, `seq/Int`,
   `String`, library symbols and solver/skolem relations separately. Integer
   atoms support cardinality arithmetic, not user objects. Every additional
   signature/field must be classified by the receipt; unknown auxiliaries are
   unsupported, not silently discarded.
4. Exclude unused **user** atoms by extent equalities. Spare scope capacity is not
   an instance object. Ignore only explicitly classified non-user auxiliaries,
   after checking they do not add hidden user structure. Decode every SAT witness
   and verify `decode(witness) ≅ C`; otherwise report a pin/decode failure.

Conversely, decode an unpinned bounded Alloy witness into the same candidate
schema, synthesize parent/inverse/composite link occurrences without collapsing
parallel bag targets, and check it on the Lean side. The
[importer](resolved-import.md) supplies compiler capture and checked input; the
[comparison harness](bounded-comparison.md) supplies Alloy pinning, decoding and search.
Neither this decoding nor the finite model interpretation invokes Claferize.

## Manual bounds, solver pin and arithmetic

Each run supplies a total per-user-signature scope map, including zero scopes,
abstract upper bounds, overlapping inheritance memberships and the global scope.
Candidate cardinalities must fit these bounds. Pinning fixes candidate extents;
scope capacity alone does not. For reverse enumeration, exhaust all models within
the same upper bounds, with an explicit isomorphism policy. For every class d,
require `|H_d| ≤ B_d`; a super bound constrains the union of its subtype objects,
not a separate allocation of super objects. Bound vectors need not equal sums
of subtype maxima: they can additionally restrict their simultaneous populations.

Emit explicit bounds for every top-level Alloy signature and every relevant
subsignature, with no exact-count modifier except when supplied intentionally
and reflected in the candidate domain. Record those exactness flags. The harness
validates the resulting Alloy command AST and records it; no inferred/default
scope is accepted.

The [comparison harness](bounded-comparison.md) uses this solver profile: Alloy **6.2.0**, official [distribution JAR][alloy-jar],
SHA-256 `6b8c1cb5bc93bedfc7c61435c4e1ab6e688a242dc702a394628d9a9801edb78d`,
manifest `6.2.0.202501090817`, Git `794226dd07b536fe35c5ca44b529417183cd629b`.

Use its bundled SAT4J implementation (fixed by the JAR hash), Java 17 with the
actual runtime/build recorded, static solving, one worker, no temporal/unbounded
mode, no decomposition (`decompose_mode = 0`, `decompose_threads = 1`), symmetry
breaking 0, skolem depth 0, partial-instance inference disabled, and overflow
prevention enabled (`A4Options.noOverflow = true`). Keep `unrolls = -1`,
`coreMinimization = 2`, `coreGranularity = 0`, `recordKodkod = false` as in the
pinned [A4Options source][alloy-options].

Record all effective solver
options, including defaults, solver identity, timeout and memory limit. An
unavailable option/profile is unsupported; do not silently substitute a solver.
The source audit itself supplies no solver run; executable comparison evidence is
produced by the separately authorized [bounded comparison harness](bounded-comparison.md).

Set Alloy integer bitwidth `b` explicitly. Define `M` from the largest absolute
integer literal and a conservative upper bound for every cardinality and
intermediate arithmetic expression in the **generated and pinning** formula,
under all declared scopes. Include inherited unions and relation tuple counts,
not just each source card. Require all evaluated integers to lie in
`[-2^(b-1), 2^(b-1)-1]`; a conservative nonnegative-count test is
`M ≤ 2^(b-1)-1`.

Counts are natural numbers on the Lean side. `-1` is translated
to absence of an upper constraint, never to a count. If the required bitwidth
is unsupported, cannot be established, or resource limits prevent solving,
report that outcome. Overflow prevention does not prove arithmetic adequacy:
it can exclude valuations, so the independent range argument is mandatory.

Scope inference and optimization correctness are outside the comparison claim.
The test may find disagreement caused by emitted `_glCard` shortcuts; retain it.
Do not discard a disagreement by assuming those shortcuts preserve semantics,
or modify the generated facts to force agreement. Only the recorded command
replacement and candidate pin are added to the hashed original model.

## Artifact schema and outcome algebra

Artifact schema identifier: `clafer-structural-comparison/v1`, implemented by the
[bounded comparison harness](bounded-comparison.md). Executable artifacts and
review are evidence separate from this schema specification. Reject unknown schema versions and duplicate
keys. IDs are strings; counts/bounds are exact decimal integers; unbounded core
upper limits use `null` after validating compiler `-1`. Tables have explicit
column names and stable IDs. Sets serialize as sorted duplicate-free arrays;
link arrays retain distinct occurrence IDs, never endpoint deduplication.

| Artifact | Required fields |
| --- | --- |
| `manifest.json` | `schema`, `contract_revision`, `compiler_commit`, `compiler_build_sha256`, `lean_commit` (actual checkout commit, or `null` when source-root Git metadata is absent), `paper_sha256`, `effective_options`, `generation_receipt`, `inputs` mapping logical relative names to byte size/SHA-256; matrix decision IDs and admitted fragment |
| `source.json` | Complete current Lean/adapter source byte size/SHA-256 inventory, also mandatory for captured trees without Git metadata; replay requires matching source bytes |
| `capture/generation.json` | Source/feature/token audit, both IR hashes, JSON/Alloy hashes, consumed UID-map projection/hash, registry, symbol/field mapping, scopes/string-map results, backend selector, `_glCard` optimization metadata |
| `core.json` | Ordered declaration inventory with UID/name/parent/super/kind/target/abstract/local and group bounds, using the [importer's root/sentinel convention](resolved-import.md); compiler-only metadata separate; no fabricated authored fields |
| `candidate.json` | Original `objects`, `root`, class membership and typed ordinary relation tables from the [checker/import protocol](resolved-import.md); preserve original bytes/row order in the input identity |
| `command.json`, `pin.als`, `comparison.als` | Original/replacement command text, complete pin hash/text, requested/effective scope maps, bitwidth and independent range argument; occurrence-indexed derived spans in `command.json` |
| `settings.json`, `capture/manifest.json` | Search mode/seed/domain, timeout/heap limits and supplied options; exact requested scope vector in the capture manifest |
| `profile.json`, `checker-runtime.json`, `language-runtime.json` | Pinned distribution/bridge/runtime identities, JVM/OS memory and wall limits, checker build/stream identity and Python build |
| `execution.json`, `solver.json`, `witness.xml` | Parsed original/comparison command ASTs, all effective solver options, actual Java build, stage/solver observations and full tuple/native witnesses; checkpoints preserve observed verdicts on failure |
| `decoded.json`, `bijection.json`, `lean.json`, `decoded-lean.json` | Decoded candidate, reviewed object-renaming certificate (which induces occurrence bijections), original and decoded checker verdicts/failed predicate names |
| `result.json` | Input-manifest digest, admission result, Lean verdict, solver outcome, comparison category, witness/decode/isomorphism result, diagnostics, elapsed time, replay command, completeness flag and `outputs` mapping raw output/witness names to byte size/SHA-256 |

This concrete file mapping retains the contract's schema obligations without adding
solver-generated ASTs or witnesses to the acyclic input manifest. Canonical
comparison tables are sorted and duplicate-free; raw candidate input identity is
preserved separately. Search reports retain termination and all case denominators.
An unavailable `lean_commit` never waives manifest input hashes, source matching
or runtime identity checks. Never read a parent repository's commit; corrupt Git
metadata and Git execution failures remain inconclusive execution errors.

Retain the source, original IR/Alloy, actual command/pin, raw solver output and
decoded witness as artifacts too. Hash raw bytes with SHA-256; do not normalize
then claim the original bytes match. Hash references form an acyclic manifest
(the manifest does not hash itself); a result references the manifest digest.
The input manifest excludes results and solver outputs; result/output artifacts
are downstream and do not change its digest. Artifact digests bind contents,
not producer trust or semantic correctness.

Lean evaluation has `satisfies`, `violates` (with predicate/binding witness), or
`error`. Solver outcomes are `sat`, `unsat`, `unknown`, `timeout`, `resource_limit`,
or `error`. Admission has `admitted`, `unsupported` (including D rows),
`malformed`, or `compiler_rejected`; a well-formed core with no satisfying model
is not malformed. Failures remain separate structured records, never Boolean
false coerced into agreement.
For a stage that did not run, its verdict is `null` with an explicit stage/reason
record; it must not acquire a synthetic `violates` or `unsat` result.

| Comparison category | Necessary observations |
| --- | --- |
| `agree_satisfies` | Lean satisfies; pinned Alloy SAT; decoded witness is isomorphic to C |
| `agree_violates` | Lean violates; complete pinned Alloy UNSAT under adequate bounds/bitwidth |
| `alloy_accepts_lean_rejects` | Lean violates; pinned SAT witness successfully decodes to C |
| `lean_accepts_alloy_rejects` | Lean satisfies; complete pinned UNSAT under adequate bounds/bitwidth |
| `inconclusive` | Any unknown, timeout, resource limit, missing prerequisite, overflow uncertainty, tool error or uncompleted search; retain the reason |
| `unsupported` / `malformed` / `compiler_rejected` | Admission failure; no semantic comparison |
| `pin_decode_failure` | SAT witness cannot be decoded or is not isomorphic to the pinned candidate; adapter failure, not a compiler counterexample |

For reporting, retain a denominator of all requested cases and counts in every
category, including unsupported/failed cases. “No mismatch found” must include
the admitted/completed counts and bounds; a batch with inconclusive cases is not
an exhaustive agreement result.

## Comparison properties and their limits

Let `D_B(e)` be the explicitly specified finite candidate domain under bounds B,
and `L(e,C)` the independent `StructuralSatisfies e (realize C)` predicate. Let
`P_A(e,C,B)` mean existence of a valid Alloy witness for the **same** pinned C,
using the fixed options and adequate bitwidth. Before drawing semantic conclusions,
the [checker correctness theorem](structural-checker.md) must connect execution with `L`; the adapter must establish
pin/decode fidelity and candidate representation completeness for this fragment.

- **Bounded soundness of Alloy relative to the selected semantics:** for all
  admitted `e` and `C ∈ D_B(e)`, `P_A(e,C,B) → L(e,C)`.
- **Bounded reverse comparison:** for the same domain,
  `L(e,C) → P_A(e,C,B)`. A failure may be caused by encoding/bitwidth/domain
  restrictions; those must be ruled out before reporting a semantic counterexample.
- **Witness direction:** every unpinned bounded Alloy solution must decode to an
  admitted candidate satisfying `L`. This detects Alloy acceptance errors but
  cannot establish reverse comparison or preservation of all Lean models.
- **Representation/renaming obligations:** satisfaction is invariant under the
  object/link bijections above; `decode(encode(C)) ≅ C`; every satisfying model
  in the stated finite structural domain has a representable candidate. These
  obligations are addressed by the [external relation argument](bounded-comparison.md)
  and executable tests; they are not consequences of JSON serialization or local
  CD well-formedness and remain subject to independent semantic review.

Random generation searches for counterexamples and must retain its distribution,
seed and coverage; it proves neither direction. Finite exhaustive checking can
establish both directions only for a fixed core/options/bound vector after
enumerating **all** candidates (or proved-complete isomorphism representatives),
including invalid structures. Enumerating only SAT Alloy witnesses is not such
a check. Universal theorems over all finite bounds, all inputs or infinite models
require separate kernel-checked proofs and explicit assumptions. Solver UNSAT is
a bounded tool result, not automatically a Lean proof. No compiler, parser,
name/default elaboration, optimization, scope inference, expression preservation,
Claferize or arbitrary-model reflection theorem is claimed.

## Positive and negative example inventory

These are acceptance obligations for the importer and comparison harness. The
source audit alone supplies no execution evidence. “Accept/reject” means semantic satisfaction unless the row specifies
admission. Use explicit analyzed core records for core tests; source snippets
require their own paired generation receipt. Pinned upstream fixtures often
contain excluded expressions and must not be relabeled as entirely admitted.

| ID | Example and positive case | Negative/boundary case and expected classification |
| --- | --- | --- |
| E1 | Two parents with identically named children but distinct UIDs; nested `0..1`, `1..1`, `2..3`, `0..*` intervals | Duplicate UID/dangling target/parent: malformed; missing or extra child relative to a bound: violates. |
| E2 | Three bag heads under one parent all dereferencing one target | Same candidate as set: violates key. Two parents each referencing the same target once: satisfies set key. Compare C8 and its `.als/.js/.html/.dot.reg` files. |
| E3 | Group `2..3` with one child declaration instantiated twice | One or four child objects: violates; two bag heads with one target count two. Cited `group_cardinality_counts_child_instances` source/Alloy regression is a structural example. |
| E4 | Leaf abstract basic with two disjoint concrete subclasses covering its head; an unused abstract has empty head | Uncovered abstract object or overlap of siblings: violates. Abstract zero-subtype family nonempty: violates cover. Unrelated class overlap violates the [declaration-disjointness rule](sources.md#declaration-disjointness-clarification); keep it in candidate generation. No extra root membership for abstract heads. |
| E5 | Nested concrete basic extending a top-level abstract leaf; same atom at both class memberships | Cloning the super object, self/cyclic super, or incompatible kind: membership violation or rejected core as appropriate; no ID/name substitution. |
| E6 | Concrete direct cyclic class references with finite head objects; reference head containing its own child | Dangling or non-class target: malformed/unsupported; zero or two dereference targets, zero or two parents: violates; no recursive traversal through targets. |
| E7 | Explicitly supplied effective cards under numeric, xor/or/mux/opt or inherited group metadata | Authored-default claims: [D1](resolved-ir-comparison.md#decision-d1). `group_children_optionality`, `groupCardInheritance`, `groupCardInheritance2` record historical default differences; their full fixtures include assertions and are excluded. Current defaults have separate scoped agreement checks. |
| E8 | Accepted local head-only Shape for top-level abstract basic; head/target/deref for abstract reference | Global key on parentless abstract set and finite abstract card restrictions: [D3](resolved-ir-comparison.md#decision-d3), not assumed agreement. `abstract_reference_clafer` contains primitive/constraint features as well. |
| E9 | Simple S inheritance case versus more general compiler refinements | `extends_nested_abstract_in_context`, `inherited_reference_not_shared`, `NestedInheritanceAndReference2`: [D2](resolved-ir-comparison.md#decision-d2)/[D4](resolved-ir-comparison.md#decision-d4), not silently accepted; negative `extends_nested_abstract_out_of_context`, `gi77_self_inheritance`, `gi77_inheritance_loop` exercise rejected input. |
| E10 | Zero/empty classes and fields pinned with equality; correct fresh root and renamed objects/links | Extra user atom, missing field pin, changed inheritance membership or same-cardinality wrong relation: pin/decode failure. Unclassified auxiliary: unsupported. |
| E11 | Largest required count fits signed bitwidth; explicit adequate manual scopes | Count 8 at bitwidth 4, missing abstract scope, scope below candidate, unsupported bitwidth or inferred scopes: inconclusive/unsupported, never semantic UNSAT agreement. |
| E12 | Same-environment paired hashes and complete backend receipt | JSON/Alloy from different options, stale UID map, tampered hash, `_glCard` shortcut mismatch: malformed/unsupported receipt or retained semantic discrepancy once faithfully encoded. |
| E13 | All admitted nodes/modifiers satisfy the constructor whitelist | One case for every rejected constructor/modifier/option above, including an enum erased into otherwise admitted nodes, escape absent from JSON, primitive reference, goal, soft assertion and inherited temporal modifier: unsupported. |
| E14 | Completed random batch or exhausted finite domain reports its precise scope | Inject timeout/unknown/tool error, skipped D row or interrupted enumeration: retain counts and incomplete status; never call these agreement or universal proof. |

Upstream related fixture paths are under [test/positive][positive],
[test/negative][negative] and [test/regression][regressions] at the same compiler
commit. Static inspection establishes emitted structure only, not solver truth.

<a id="decisions-location-proposal-and-prerequisites"></a>

## Decisions, accepted locations and dependency boundaries

D1–D8 are the project decision IDs defined in the table below and used in dependent contracts;
they are not the paper's Appendix 4 section numbers. In particular, [D2](resolved-ir-comparison.md#decision-d2) concerns
nested abstractness, [D4](resolved-ir-comparison.md#decision-d4) inheritance/refinement, and [D6](resolved-ir-comparison.md#decision-d6) group/global obligations.

The following dispositions distinguish the accepted structural interfaces and
external comparison from deferred language extensions. Existing [span composition (Q1)](sources.md#span-composition-q1-research-for-4), [common-target disjointness (Q8)](sources.md#predicate-contracts-and-the-accepted-q8-correction) and the
top-level abstract correction remain accepted as documented in the [source map](sources.md).
Record new disagreements in a scoped issue before implementation; no
compiler behavior overrides a current Lean requirement.

| Decision | Accepted disposition / alternatives | Implementation boundary and review |
| --- | --- | --- |
| <a id="decision-d1"></a>D1 — authored/effective and defaults | Use effective core plus erasure/satisfaction bridge. A faithful minimal authored export is an alternative. Preserve authored provenance as a separate obligation and retain the historical numeric-group/opt/_isKeyword observations above. Current group defaults agree with 0.5.4 on the scoped cases; no imported Defaults/name-resolution theorem. | The [effective-core bridge](structural-checker.md) checks effective well-formedness; it does not recover source provenance. |
| <a id="decision-d2"></a>D2 — nested abstractness | Keep S limited to leaf abstract basics; reject differing declared/effective abstractness. The [inherited realization extension](inherited-realization.md) retains authored flags and realizes ordinary effective-abstract fields through actual parent objects. | The Appendix 6 extension does not enlarge the finite checker's guarded domain. |
| <a id="decision-d3"></a>D3 — parentless key and cards | Retain corrected Shapes; reject abstract references and nontrivial abstract global cards until reviewed. Do not add a root parent/key to force compiler agreement. | Any extension must reconcile the effective-core contract, [MCS disciplines](mcs-invariants.md) and [gluing](architecture.md#mcs-gluing). A new source correction requires separate review. |
| <a id="decision-d4"></a>D4 — inheritance/refinement | Require selected parent/kind rules and the guarded S subset. [Inherited realization](inherited-realization.md) restricts existing field maps while preserving equal-parent declaration edges. Compiler parent-subtyping, redefinition and target narrowing remain excluded. | Preserve the existing input requirement and guarded checker. |
| <a id="decision-d5"></a>D5 — hidden generation state | Require a same-generation minimal receipt and exact options; input is unsupported without it. A broader state export would need a versioned schema. | The [paired importer](resolved-import.md) and [bounded adapter](bounded-comparison.md) implement the capture and comparison boundaries separately. |
| <a id="decision-d6"></a>D6 — group/global obligations | Abstract groups are inheritable bounds; concrete contexts count the union of own and inherited child heads. Empty inventories count zero, intentionally differing from C3's skip. | [Group compilation](group-compilation.md) generates and interprets a separate declaration component. [Inherited realization](inherited-realization.md) adds ordinary-field groups and map restrictions. Both preserve the guarded checker. |
| <a id="decision-d7"></a>D7 — location and scope | Keep reusable semantics, candidates, bridges and checker in this repository. Do not create a separate `clafer-compare` repository. | The [importer/capture](resolved-import.md) and [solver harness](bounded-comparison.md) use the locations below and retain full validation and separate external-adapter review. |
| <a id="decision-d8"></a>D8 — structural dependencies | The guarded interface builds on resolved syntax, concrete predicates, formal CDs, MCS disciplines, core typing, Compile, gluing and this compiler audit. The [architecture](architecture.md) records those delivered dependencies. | The [structural interpretation and finite correctness bridges](structural-checker.md) include global [declaration disjointness](sources.md#declaration-disjointness-clarification): incomparable heads cannot share objects in satisfying models, while overlapping raw candidates remain representable. Expression evaluation and external comparison are separate contracts. |

**Accepted location ([D7](resolved-ir-comparison.md#decision-d7)).** Whole-model structural semantics and effective-core,
interpretation and representation bridges live under `Clafer/Semantics/`;
finite candidate verification lives under `Clafer/Verification/`. Shared definitions
remain in the owning Clafer layer. The repository retains one Lake package and
`Clafer -> FormalCD -> DPGraph -> Mathlib`; `DPGraph` stays independently importable.
The [intent](intent.md), [architecture](architecture.md) and
[extension requirements](spec.md#effective-structural-core-and-supported-fragment)
state this boundary. The existing full pinned validation policy is unchanged.
The [resolved importer](resolved-import.md) location is `Clafer/Verification/` for import/validation/bridge,
`scripts/verification/` for compiler capture/protocol, and `tests/` for fixtures.
The [import protocol](resolved-import.md) states the implemented boundary and trust
limits. The [bounded comparison harness](bounded-comparison.md) supplies test enumeration,
solver pin/decode and comparison in `scripts/verification/`; tests stay under `tests/`.

**Whole-model proof obligations.** Existing `AST.WellFormed`, `Shape.diagram`,
`Shape.raw_wellFormed`, and [core expression typing](spec.md#resolved-core-constraint-typing) are not a whole-model
satisfaction predicate. Structural results from [Compile](compile.md) and [gluing](architecture.md#mcs-gluing) are also insufficient
alone. The [structural checker guide](structural-checker.md) and
[trace artifacts](clafer-trace.md#effective-structural-core) identify the declarations
covering these accepted obligations:

1. A complete interpreted structural signature/declaration inventory, including
   root singleton, abstract cover/disjointness, containment ownership/reachability,
   inheritance identity/commutation, reference key/totality, multiplicities,
   effective group bounds and all applicable guarded Appendix 5 clauses.
2. A chosen whole-model interpretation into a bounded shared-object/span graph,
   related explicitly to `DPGraph.Interpretation.Satisfies`/`IsModel` and the
   generated/glued CD. Existing reduct is one direction; it supplies no general
   whole-model reflection. No unproved universal SetMap or metamodel instance
   assumption may fill this gap.
3. The effective-core well-formedness and erasure bridge above, plus exact
   prerequisites on the reviewed structural outputs of [MCS disciplines](mcs-invariants.md), [Compile](compile.md) and [gluing](architecture.md#mcs-gluing) (including
   label congruence and declaration completeness). Local role matching does not
   settle the [guarded Appendix 5 clauses (Q2)](mcs-invariants.md#appendix-e-inventory), [resolved-referent identity (Q4)](sources.md#mcs-gluing-and-the-approved-q4-rule) or inherited field identity.
4. Finite object/link encoding and a terminating Boolean checker with a theorem
   `check e C = true ↔ L(e,C)` under explicit admission assumptions. Prove finite
   fiber-count correspondence to the current cardinal predicates, key behavior,
   invariance under renaming and completeness of the representable model domain.
5. Positive and violating whole-model witnesses exercising **all** structural
   declarations together, and a dependency disposition linked from [finite structural semantics](structural-checker.md) and
   reviewed before any “constraint-free” shortcut. [Core typing](spec.md#resolved-core-constraint-typing) is not semantic
   interpretation; conversely unrelated deferred language features need not be
   finished if the exact structural slice and bridge are separately accepted.

The [structural checker guide](structural-checker.md) records the delivered
representation and correctness bridges for the accepted boundary. The
[resolved importer](resolved-import.md) and [bounded comparison harness](bounded-comparison.md)
have separate executable policies, implementation evidence and review obligations.
Review of this document alone does not establish that their implementations or
semantic claims are correct.

[compiler]: https://github.com/gsdlab/clafer/tree/15adb2216909421bcb5022174d2d84ef2b42307c
[license]: https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/LICENSE
[pipeline]: https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer.hs#L497
[ir]: https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Intermediate/Intclafer.hs#L69
[alloy]: https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Generator/Alloy.hs#L39
[common]: https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Common.hs
[environment]: https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/ClaferT.hs#L101
[resolver]: https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Intermediate/Resolver.hs#L38
[inheritance]: https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Intermediate/ResolverInheritance.hs
[desugarer]: https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Intermediate/Desugarer.hs
[optimizer]: https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Optimizer/Optimizer.hs#L42
[strings]: https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Intermediate/StringAnalyzer.hs#L36
[args]: https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/ClaferArgs.hs#L50
[changes]: https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/CHANGES.md
[bag-fixture]: https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/test/positive/set_and_bag_references.cfr
[bag-regression]: https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/test/regression/set_and_bag_references.als.reg
[positive]: https://github.com/gsdlab/clafer/tree/15adb2216909421bcb5022174d2d84ef2b42307c/test/positive
[negative]: https://github.com/gsdlab/clafer/tree/15adb2216909421bcb5022174d2d84ef2b42307c/test/negative
[regressions]: https://github.com/gsdlab/clafer/tree/15adb2216909421bcb5022174d2d84ef2b42307c/test/regression
[alloy-jar]: https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.2.0/org.alloytools.alloy.dist.jar
[alloy-options]: https://github.com/AlloyTools/org.alloytools.alloy/blob/794226dd07b536fe35c5ca44b529417183cd629b/org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/translator/A4Options.java
