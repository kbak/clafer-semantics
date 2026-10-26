# Compiling effective group cardinalities

Group compilation extends the [structural Compile contract](compile.md) with
interpreted group declarations, as specified in the [group-compilation issue](https://github.com/kbak/clafer-semantics/issues/65).
`Compile.compileAugmented` retains the original well-formed MCS, adds generated
group declarations and exposes their complete union. `Compile.gluedGroups`
preserves that exact union and derives `FormalCD` naming/default validity.

## Source and selected meaning

The [published article](sources.md#primary-source), SHA-256
`653fc7868637680c44b6176d8ff643ec20149534fe1681ea4fc4ce636db76f2d`, supplies:

| Locator | Meaning and boundary |
| --- | --- |
| §4.2.1 PDF p.9; §6.2.2 PDF p.21 | Group bounds constrain child instances per parent object. |
| §4.2.2 PDF p.9; Appendix D.4 PDF pp.33–34 | Explicit constraints hold for every object of their context, including subtype objects. |
| §4.2.3 PDF p.10; §5.5 PDF p.17; Appendix 6 PDF p.34 | Inheritance shares objects and structure; map commutation/realization requires separate obligations. |
| Appendix 3 PDF p.32 | xor = 1..1, or = 1..*, mux = 0..1, opt = 0..*. Effective bounds/defaults are supplied by resolved input. |
| B.4 Definitions 8–10 PDF p.31; §6.2.3–5 PDF pp.22–23 | Formulas retain full graph bindings; gluing translates declarations. Figure 23 total args is a separate MCS restriction. |

The selected group-inheritance behavior was audited against compiler commit
`15adb2216909421bcb5022174d2d84ef2b42307c`:

* [Generator/Alloy.hs, genGroupConst](https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Generator/Alloy.hs#L324)
  unions own and super-hierarchy child relations and skips abstract contexts.
* [Intermediate/ResolverInheritance.hs, analyzeGCard](https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Intermediate/ResolverInheritance.hs#L213)
  resolves the nearest authored group along the hierarchy.
* [Common.hs, findHierarchy](https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Common.hs#L171)
  includes self and successive supers.
* [groupCardInheritance.cfr](https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/test/positive/groupCardInheritance.cfr),
  its [Alloy regression](https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/test/regression/groupCardInheritance.als.reg),
  and [groupCardInheritance2.cfr](https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/test/positive/groupCardInheritance2.cfr)
  distinguish inherited alternatives, newly added children and local overrides.

An abstract group supplies an inheritable bound. It does not additionally impose
an invariant over only the abstract declaration's original inventory. Every
concrete context enforces its resolved effective bound over the union of its own
children and children of every super. If abstract xor A has x/y and B : A adds z,
a B object with only z passes. An effective opt override on B can admit two
children. This special treatment of groups refines the paper's context-constraint
account; ordinary explicit constraints on abstracts retain that account unchanged.

Authored/effective provenance and explicit overrides are preserved; child defaults
follow the adopted [policy](sources.md#current-child-default-policy), including its
numeric-group evolution from Appendix 3. The comparison audit treats [authored defaults (D1)](resolved-ir-comparison.md#decision-d1) and
[group semantics (D6)](resolved-ir-comparison.md#decision-d6)
as separate decisions.

An empty inventory counts zero. Bounds containing zero hold; a positive lower
bound forces the context extent empty. An empty context satisfies the universal
predicate vacuously. This deliberately differs from the audited 0.5.3
`genGroupConst` empty-inventory skip. The current
[0.5.4 capture profile](resolved-ir-comparison.md#compiler-054-compatibility)
rejects concrete groups whose lower bound cannot be reached, even when their
context could be empty; abstract groups remain exempt. This compiler rejection
does not replace the independent zero-count meaning. The
[compiler license/source policy](sources.md#pinned-compiler-compatibility-audit)
applies; no compiler source is incorporated.

## Representation and interpretation

`Groups.Ancestor` selects the reflexive transitive super hierarchy by resolved
identity. `Groups.Child` pairs an ancestor with each declaration whose resolved
parent is that ancestor. Finite ASTs therefore have finite inventories.
The arity has one vertex for each selected ancestor and child, a distinguished
context vertex, each selected child-head arrow, and the inclusion arrows between
selected ancestor heads. `Groups.binding` maps all vertices and arrows into the
canonical role graph, preserving incidence and ownership. A generated predicate
symbol identifies one concrete owner; its effective bound and inventory are fixed
by the compiled family. Reference children bind their heads, never their targets.

For each context object, `Groups.Objects` takes the **set union of ambient child
objects** reached by those head maps from that same parent identity. Distinct bag
heads with one reference target count separately. Multiple links or inherited
paths witnessing the same object count once. No sum of declaration cardinalities
or target deduplication is used. `InRange` gives the embedding-based meaning even
for infinite sets; finite specialization uses the shared `inRange_card` bridge in
[DPGraph/Predicates/Finite.lean](../DPGraph/Predicates/Finite.lean), with explicit
finiteness of the counted subtype.

The extra component can contain vertex-only formulas. A childless context with
no super has its context vertex and no arrows. These are legal under B.4
Definition 8, but cannot satisfy Figure 23 total args. The original MCS bank, its
literal bag key, nonempty argument proof and the positive-support contract for
user constraints remain intact. No synthetic identity role is added. The complete
raw bank is not claimed to satisfy the old MCS total-args discipline.
`forget_augmented` recovers the existing structural result exactly.

## Gluing and semantic boundary

The complete source bank contains the union of original and generated
declarations, including ordinary/inclusion effective defaults. `glued_declarations`
proves exact image equality for both components, retaining full bindings under
labeling. Compile's referents are injective, so incidence, metadata compatibility
and a graph inverse to labeling are derived. `descendGroups` therefore constructs
an actual glued interpretation from a configuration and proves its reduct equality.
Generic noninjective MCS gluing still requires its existing consistency conditions.

`objects_interpret` proves that a typed [relational configuration](structural-checker.md)
realizes each
selected head fiber as containment at the same parent identity. `generated_group_iff`
and `descended_group_iff` identify source/glued formula satisfaction with the
selected bounds. `descended_model_iff` accounts for both declaration components;
satisfying a group alone does not establish the remaining structural obligations.
No user-expression interpreter is inferred from fresh predicate symbols.

The [finite checker and guarded comparison fragment](structural-checker.md) remain unchanged. `direct_child_iff`
relates inventories when strict ancestors have no children; effective-bound
agreement is also necessary when comparing to its `Configuration.Groups` (and
holds for `EffectiveCore.erase`). The finite checker does not depend on this extension.

The separate [realization extension](inherited-realization.md) supplies the
selected inherited-field realization and commuting map restrictions. Selecting an
inherited head map does not prove those obligations or copy any object. Tests of
an inherited abstract-child fiber are explicitly group-predicate tests under typed
relations, not proofs of complete inherited-family realizability; the separate
[Appendix 6 witnesses](../Clafer/Examples/Telematics/Structural.lean) exercise the realization extension. The zero-arrow example
uses only Sing; its empty-context case tests the group predicate vacuously and
does not assert the separate root singleton obligation.

Named implementation/proof and acceptance artifacts are in
[the Clafer trace](clafer-trace.md). [Representative integration](representative-models.md)
and the [complete Telematics model](telematics.md) have separate acceptance criteria.
