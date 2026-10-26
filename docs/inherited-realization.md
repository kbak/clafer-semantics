<a id="appendix-f-inherited-realization"></a>

# Appendix 6 inherited realization

This contract explains how Appendix 6's ordinary fields and explicit abstract
types are realized, including inherited views of the same objects and links.
It preserves the guarded [structural checker contract](resolved-ir-comparison.md),
[Compile input](compile.md), and [group policy](group-compilation.md).
The [complete fixture](telematics.md) combines it with all twelve constraint
bodies and the selected semantic bridge. The accepted clarification is recorded
in the [inherited-realization issue](https://github.com/kbak/clafer-semantics/issues/66).

## Source and accepted clarification

Primary: the 37-page publisher e-offprint, SHA-256
`653fc7868637680c44b6176d8ff643ec20149534fe1681ea4fc4ce636db76f2d`,
[Appendix 6, PDF p.34](sources.md#primary-source).
The supplied inventory includes a visual indentation check. Relevant text:
§4.2.2–3, §5.3.4–5, §5.5/Figures 18–19, §6.2.3–5, Appendices 3–5.
The paper's abstract-default and explicit-subtype rules do not completely specify
inherited-field realization. The following is the accepted selected clarification,
not a theorem attributed to the paper.

The labels [D2](resolved-ir-comparison.md#decision-d2), [D4](resolved-ir-comparison.md#decision-d4) and [D6](resolved-ir-comparison.md#decision-d6) below identify the comparison audit's
[nested-abstractness, inheritance/refinement and group decisions](resolved-ir-comparison.md#decisions-location-proposal-and-prerequisites).
They are project decision IDs, not sections of the paper's Appendix 4.

* **Nested abstractness ([D2](resolved-ir-comparison.md#decision-d2)):** authored explicit abstract types and ordinary
  field templates made effectively abstract by containment have different realization rules. Preserve both flags in
  the AST. Field templates have instances at realized parent objects; they are not
  emptied by an absent written subtype. An explicit abstract leaf is empty.
* **Inheritance and refinement ([D4](resolved-ir-comparison.md#decision-d4)):** preserve equal-parent declaration
  inheritance. All seven written super edges below target parentless abstracts. No unequal-parent AST edge, relocation,
  reference narrowing or general nested redefinition is introduced. A contextual
  field is the same field objects whose existing unique parent is in the context.
  Its containment/dereference links are restrictions of the original links.
  Ancestor/descendant contexts may overlap; disjoint parent alternatives have
  disjoint owned fibers. Parent realization never bypasses explicit type cover.
* Explicit abstracts are covered by direct explicit subtype heads, pairwise
  disjoint in their common target ([Q8](sources.md#predicate-contracts-and-the-accepted-q8-correction)). Some covering heads are field templates.
  Contextual classifications and explicit subtype classifications intersect; they
  are not a single list of disjoint competitors.
* **Group bounds ([D6](resolved-ir-comparison.md#decision-d6)):** retain the group policy's union of own/inherited child
  head objects and its effective override/empty-inventory rules. Realized ordinary field contexts enforce their
  effective group even if the effective abstract flag is true, notably options.size.
  Ordinary owner constraints apply to the same objects in all subtype/context views.
* Preserve [Q1](sources.md#span-composition-q1-research-for-4) links, corrected top-level abstract heads, role/referent/name
  separation, exact declaration-image gluing and effective-default completeness.
  Parentless abstracts have no invented root parent or local parent-fiber bounds.
  Their unused numeric AST slot is not authored global cardinality.

Supplementary audited 0.5.3 evidence (MIT; no source copied):
[gsdlab/clafer@15adb2216909421bcb5022174d2d84ef2b42307c](https://github.com/gsdlab/clafer/tree/15adb2216909421bcb5022174d2d84ef2b42307c),
`Intermediate/Desugarer.hs` (`desugarModifiers`),
`Intermediate/ResolverInheritance.hs` (`resolveNClafer`), `Common.hs`
(`isProperNesting`, `isProperRefinement`), `Generator/Alloy.hs` (`claferDecl`,
`genParentSubrelationConstriant`, `genRefSubrelationConstriant`), and
`test/regression/Telematics_PLA.als.reg`,
`test/regression/extends_nested_abstract_in_context.als.reg`.
The compiler keeps ordinary children of abstract parents ordinary. Its wider
parent-subtyping is not selected; its Telematics fixtures differ from the printed
model, including names and extra version constraints. Preserve the remaining [comparison boundaries (D1–D8)](resolved-ir-comparison.md#decisions-accepted-locations-and-dependency-boundaries).
The current [0.5.4 assessment](resolved-ir-comparison.md#compiler-054-compatibility)
retains these realization boundaries separately from its default/group fixes.

## Scoped source-to-core inventory

IDs d01–d26 identify distinct declarations, not names or semantic equality.
`root` is synthetic basic concrete Sing, parentless, with no super; `int` is the
implicit basic concrete integer domain parented by root, with no super. Source
`integer` resolves to int. No other declarations are implicit.

The complete fixture gives int explicit unrestricted 0..* bounds and contains
every represented integer under root. The older structural projection retains
its finite 1..1 placeholder and is not the complete interpretation.

`A/E` means authored/effective abstractness. Unmarked groups are 0..*.
Parentless abstract bounds are N/A (the unauthored storage default 1..1 has no
local predicate). Other unmarked parented bounds default to 1..1; optional and
1..2 bounds are authored. Each xor alternative explicitly has `?`.

| ID | Path | Parent | Super | Kind/target | A/E | Local | Group |
| --- | --- | --- | --- | --- | --- | --- | --- |
| d01 | options | — | — | basic | 1/1 | N/A | 0..* |
| d02 | options.size | d01 | — | basic | 0/1 | 1..1 | xor |
| d03 | options.size.small | d02 | — | basic | 0/1 | 0..1 | 0..* |
| d04 | options.size.large | d02 | — | basic | 0/1 | 0..1 | 0..* |
| d05 | options.cache | d01 | — | basic | 0/1 | 0..1 | 0..* |
| d06 | options.cache.size | d05 | — | set → int | 0/1 | 1..1 | 0..* |
| d07 | options.cache.size.fixed | d06 | — | basic | 0/1 | 0..1 | 0..* |
| d08 | comp | — | — | basic | 1/1 | N/A | 0..* |
| d09 | comp.version | d08 | — | set → int | 0/1 | 1..1 | 0..* |
| d10 | ECU | — | d08 | basic | 1/1 | N/A | 0..* |
| d11 | display | — | d08 | basic | 1/1 | N/A | 0..* |
| d12 | display.server | d11 | — | set → d10 | 0/1 | 1..1 | 0..* |
| d13 | display.options | d11 | d01 | basic | 0/1 | 1..1 | 0..* |
| d14 | plaECU | — | d10 | basic | 1/1 | N/A | 0..* |
| d15 | plaECU.plaDisplay | d14 | d11 | basic | 0/1 | 1..2 | 0..* |
| d16 | ECU1 | root | d14 | basic | 0/0 | 1..1 | 0..* |
| d17 | ECU2 | root | d14 | basic | 0/0 | 0..1 | 0..* |
| d18 | ECU2.master | d17 | — | set → d16 | 0/0 | 1..1 | 0..* |
| d19 | telematics | root | — | basic | 0/0 | 1..1 | 0..* |
| d20 | telematics.channel | d19 | — | basic | 0/0 | 1..1 | xor |
| d21 | telematics.channel.single | d20 | — | basic | 0/0 | 0..1 | 0..* |
| d22 | telematics.channel.dual | d20 | — | basic | 0/0 | 0..1 | 0..* |
| d23 | telematics.extraDisplay | d19 | — | basic | 0/0 | 0..1 | 0..* |
| d24 | telematics.size | d19 | — | basic | 0/0 | 1..1 | xor |
| d25 | telematics.size.small | d24 | — | basic | 0/0 | 0..1 | 0..* |
| d26 | telematics.size.large | d24 | — | basic | 0/0 | 0..1 | 0..* |

Seven super edges: d10→d08, d11→d08, d13→d01, d14→d10,
d15→d11, d16→d14, d17→d14. The five cover/disjoint families are
`d01 ← {d13}`, `d08 ← {d10,d11}`, `d10 ← {d14}`,
`d11 ← {d15}`, `d14 ← {d16,d17}`.
Xor inventories are `d02 ← {d03,d04}`, `d20 ← {d21,d22}`,
`d24 ← {d25,d26}`. Quoted display.options elaborates to d13 extending d01;
the three names size (d02/d06/d24) remain distinct.

<a id="constraint-scope-handoff"></a>

## Constraint inventory

These twelve explicit conjuncts are manually elaborated as `c01`–`c12` in
[Expressions](../Clafer/Examples/Telematics/Expressions.lean), with resolved
support proofs against the structural AST. Their independent equations, local
definedness obligations and positive/negative witnesses are indexed in the
[denotation contract](constraint-denotation.md) and [proof inventory](clafer-trace.md#manual-appendix-f-expression-implementation).
Navigation arrows below select child heads unless explicitly marked widen,
dereference or parent. The [selected preservation bridge](constraint-preservation.md) derives source
predicate meanings; the [combined acceptance fixture](telematics.md) applies it to all twelve bodies.

| ID/context | Meaning and navigation |
| --- | --- |
| c01/d01 | small size and cache imply fixed: self→d02→d03, self→d05, self→d05→d06→d07. Visit fixed on the cache.size reference HEAD before any integer dereference. |
| c02/d11 | display version ≥ server version, without optional-server guard: self→widen d08→d09→dereference int; self→d12→dereference d10→widen d08→d09→dereference int. Only this conjunct needs integer singleton extraction. |
| c03/d15 | no inherited cache: self→widen d11→d13→widen d01→d05. |
| c04/d15 | server equals owning parent at ECU: self→widen d11→d12→dereference d10; self→parent d14→widen d10. |
| c05/d19 | channel.dual present iff ECU2 present: self→d20→d22; global d17. |
| c06/d19 | extraDisplay present iff exactly two ECU1 plaDisplay heads: self→d23; global d16→widen d14→d15. |
| c07/d19 | extraDisplay present iff (ECU2 present implies exactly two ECU2 plaDisplay heads): self→d23; global d17; global d17→widen d14→d15. Preserve implication and vacuity when ECU2 is absent. |
| c08/d19 | size.large present iff no small options on all plaECU plaDisplays: self→d24→d26; global d14→d15→widen d11→d13→widen d01→d02→d03. |
| c09/d19 | size.small present iff no large options on all plaECU plaDisplays: self→d24→d25; global d14→d15→widen d11→d13→widen d01→d02→d04. |
| c10/root | select dual: global d19→d20→d22. |
| c11/root | select extraDisplay: global d19→d23. |
| c12/root | select telematics.size.large: global d19→d24→d26. |

Global d14 is its whole realized extent, not a direct Sing child. c01 belongs to
options, c02 to display, c03/c04 to plaDisplay, c05–c09 to telematics; the final
three are global. No printed construct is dropped by this division of ownership.

## Structural representation and proof boundary

`Semantics.Realization.Core.ofInput` retains the original authored abstract flag
alongside `EffectiveCore.erase`. `Core.Selected` admits parentless explicit
abstracts, basic explicit super targets and parented references. A finite
realization rank decreases when following an explicit type to a direct realization
or an ordinary field to its owner. This bounds the selected combinations and
excludes disconnected recursive realization islands. `reaches` derives root
reachability using this rank, actual coverage and unique parent ownership.

`View`, `headView` and `derefView` restrict the existing object sets and link
carriers. Forgetting restriction proofs injects links into the original maps;
`targetLink` retains the original [Q1](sources.md#span-composition-q1-research-for-4) composable link pair. Context coverage is
derived from parent coverage, and ordinary constraint scope transports to every
subtype/view of the same ambient object. No contextual declaration IDs or
unequal-parent super edges are allocated.

`Compile.Realization.bank` includes the entire [generated group bank](group-compilation.md), two actual built-in
cover/disjoint formulas per explicit abstract, and one group formula per ordinary
effective-abstract field. Direct subtype arities are enumerated from actual super
edges, including the empty family. Field-group arities reuse the group-compilation construction. `declarations`
and `glued_declarations` establish completeness and exact translated images;
`defaults` retains complete effective defaults and `forget` recovers the previous
augmentation. The existing structural MCS remains valid; the larger raw bank does
not assert its positive-args discipline.

`correspondence` and `whole_model` identify generated/glued satisfaction with the
independent extended structural conditions and the original constraint occurrences.
Authored expression meanings remain a parameter; no caller supplies the structural
equivalence. `supported_input_compatibility` derives flag agreement on a selected
AST whose erasure satisfies the [finite checker guard](structural-checker.md),
proving the same structural result and
therefore preserving the supported checker's existing correctness result.

The witness IDs use source `DeclId` numbers 1–26, root=0 and int=27, injectively.
Preorder positions are separate and recorded by `source_order`. The witness is a
structural projection of Appendix 6, including all declarations; it has no source
expression bodies and does not claim the printed final selections or the complete
model result. In particular its one plaDisplay per ECU exercises 1..2 realization,
while the separate expression witnesses reject its c06/c07 counts. A modified
typed candidate accepts the two-display c06 condition and rejects a wrong owner
in c04; it is not claimed as a whole structural model. The [complete fixture](telematics.md) combines all structural and authored
constraints with the final selections using a separate configuration.

## Declaration identity and whole-model disjointness

The [declaration-disjointness clarification](sources.md#declaration-disjointness-clarification) applies
`Configuration.DeclarationDisjoint` to the resolved declaration inventory in
`Realization.Satisfies`. Ancestor views of one field remain restrictions of its
existing objects and links; they are not additional declarations to partition.
This preserves the version, options and display witnesses, including shared
objects along super chains and the complete integer-domain fixture.

`Compile.Realization.whole_model` and `ConstraintMeaning.whole_model` require
declaration disjointness alongside typedness and root conditions on the model
side. The generated bank retains its actual abstract-family and group formulas;
it does not generate the additional global partition. The concrete inherited and
full Appendix 6 configurations each prove `declaration_disjoint` independently.
The guarded compatibility theorem includes the same condition on both sides.
