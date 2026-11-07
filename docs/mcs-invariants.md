# MCS structural inventory

The source is SoSyM §6.2.3/Figure 23 (PDF pp.22–23) and Tables 5–8 (see Appendix 5)
(PDF pp.22–23), in the [published article](sources.md#primary-source). The inventory below
records the guarded expansion of Appendix 5 clauses and the separation of role
identities from referents and names, accepted in the
[MCS disciplines issue](https://github.com/kbak/clafer-semantics/issues/20). The
[existing Shape contract](spec.md#individual-clafer-shapes) controls exact presence.
The [MCS modules](../Clafer/MCS/Basic.lean) implement this structural inventory.
The [source correction](#figure-23-source-multiplicity-correction) applies to
seven associations. [Structural Compile](compile.md) supplies formula generation.
[Resolved-referent gluing](#gluing-boundary) has separate input hypotheses;
semantic model existence remains a separate obligation.

<a id="appendix-e-inventory"></a>

## Appendix 5 inventory

Write `H`, `S`, `T` for head/source/target class roles and `h`, `p`, `d`, `t`
for head/parent/dereference/target map roles. `P` means the clafer has a parent;
`R` means its kind is reference set or reference bag. A subscript `super`
denotes the selected super's corresponding role. A guard does not allow required
roles to be omitted: `H` always exists; `S` exists exactly when `P`; `T` exactly
when `R`; `h,p` exactly when `P`; `d` exactly when `R`; and `t` exactly when
`P ∧ R`. These are the existing `Roles.classPresent` and `Roles.mapPresent`
rules in [Shape.lean](../Clafer/Shape.lean).

| Source clause | Guard | Equation or obligation |
| --- | --- | --- |
| Table 5: head endpoints | `P` | `so(h) = S`, `ta(h) = H` |
| Table 5: analogous parent endpoints | `P` | `so(p) = H`, `ta(p) = S` |
| Table 5: analogous dereference endpoints | `R` | `so(d) = H`, `ta(d) = T` |
| Table 5: analogous target endpoints | `P ∧ R` | `so(t) = S`, `ta(t) = T` |
| Table 6: parent cojoining | `P` | `S = parent.H` |
| Table 6: target cojoining | `R` | `T = target.H` |
| Table 6: head inclusion | super exists | `so(super_h) = H`, `ta(super_h) = H_super` |
| Table 6: analogous source inclusion | super exists and both source roles exist | `so(super_s) = S`, `ta(super_s) = S_super` |
| Table 6: analogous target inclusion | super exists and both target roles exist | `so(super_t) = T`, `ta(super_t) = T_super` |
| Table 7: Sing/root | synthetic root | Basic, no parent, no source/target class, no ordinary maps and no super; the head remains |
| Table 7: Dom | any supported primitive domain | Basic, parent is root, source cojoins root's head, no target and no super |
| Table 7: basic | basic kind | No target/dereference/target-map; source/head-map/parent-map exist exactly when parented |
| Table 7: analogous reference set | reference-set kind | Target/dereference required; source/head-map/parent-map/target-map exist exactly when parented; ordinary target-map mode |
| Table 7: analogous reference bag | reference-bag kind | Same role presence as reference set; bag target-map mode |
| Table 7: parentless non-root | no parent and not root | Abstract; retains head; a reference also retains target/dereference |
| Table 8: head naming | `P` | `label(h) = label(H)` |
| Table 8: parent naming | `P` | `label(p) = "parent"` |
| Table 8: analogous dereference naming | `R` | `label(d) = "dref"` |
| Table 8: target naming | `P ∧ R` | `label(t) = label(h) ++ "*"`; equivalently `label(H) ++ "*"`, derived using the head equation |
| Table 8: Sing equivalence | every clafer | synthetic root iff head label is `"Sing"` |
| Table 8: int equivalence | every clafer | primitive int iff head label is `"int"` |
| Table 8: string equivalence | every clafer | primitive string iff head label is `"string"` |
| Table 8: bool equivalence | every clafer | primitive bool iff head label is `"bool"` |

No super means no inclusion slots; a selected super requires the head inclusion
and every shared-endpoint inclusion. Missing one of two source/target endpoints
forbids that inclusion slot rather than generating an equation with an undefined
side. `Shape.SharedClass` already describes this boundary. The root and
parentless basic exceptions use the [top-level abstract correction](sources.md#resolved-2014-clafer-and-individual-shapes).
The supported primitive-domain vocabulary is `int`, `string`, `bool`, as in
`PrimitiveDomain`; the analogous expansion quantifies over all three. Both
implications of each canonical naming equivalence are required, including the
exclusion of reserved head names from ordinary user clafers.

Inclusion names are `"isA"` under the inherited §6.1.1/§6.1.3 naming discipline.
That obligation comes from the class-diagram foundation, not an additional
printed Table 8 row. Local inverse, triangle, multiplicity and reference-key
formulas remain those of [Shape/Diagram.lean](../Clafer/Shape/Diagram.lean).

## Identity and formula boundaries

Keep local role slots, graph role identities, resolved class/map referents, and
displayed strings distinguishable. Cojoining equalities must explicitly state
which identity level they compare. Equality of displayed `parent`, `dref` or
`isA` strings must not by itself identify arrows. Preserve endpoints and the
information needed for intended identifications. The approved [gluing](architecture.md#mcs-gluing)
congruence and its graph/DP-morphism proof use the explicit resolved-referent
contract described below; the MCS representation alone does not select that policy.

Figure 23 also includes Role, ClassRole, MapRole, InclRole, String, PredefStr,
Formula and Signature, with the ClassRole/MapRole cover/disjoint partition,
inclusion roles, total labels/endpoints, formula ownership and diagram predicates.
Formula data must retain the symbol and complete graph binding, including
isolated vertices and repeated argument occurrences. The literal bag key on
`(args,pred)` and total `args` are separate conditions; neither follows just
from well-typed full bindings. Reuse the
[existing distinction and counterexamples](sources.md#literal-key-total-args-and-the-19-obligation).
Do not weaken that key to indexed equality or suppress total args for zero-arrow
arities.

## Figure 23 source-multiplicity correction

The accepted ownership correction changes the source multiplicity on each of the four
ordinary-map and three inclusion-role associations from `1` to `0..1` over its
common target: each role has at most one owner within each association's image.
Shape and inheritance guards still enforce exact required and forbidden presence.
The head class always exists. Top-level abstracts omit source and parent-dependent
maps, retaining target/dereference when they are references.

The printed lower bounds cannot support nonempty map examples: source `1` on
both parent_map and dref_map forces every MapRole into both images. Table 8 then
requires its single label to be both `"parent"` and `"dref"`. The correction removes
these conflicting inverse-existence obligations, including on all three super
associations. It does not change head-class source `1` (each ClassRole is one
clafer's head) or formulas source `1` (each Formula has one owner). The publication
and frozen historical snapshots retain the printed annotations.

## Definition and proof map

All names below are in `Clafer.MCS` unless qualified. The representation uses
explicit ordinary and inclusion slot occurrences as map-role identities. Shared
class roles are vertices of a common graph; `Roles.Cojoining` compares those
vertices, before referent or string equality. `Family.canonicalRoles` supplies a
constructible cojoining of a resolved family, without resolving names or compiling
an AST. Arbitrary vertex assignments remain expressible and are checked by
`Roles.Cojoining`. The occurrence presentation retains separate arrows until the
later gluing operation, even if their endpoints, referents or names agree.

| Inventory clauses | Definition/proposition | Boundary evidence |
| --- | --- | --- |
| Table 5 head, parent, dref, target endpoints | `Roles.binding`, `Roles.source`, `Roles.target`, existing `Roles.source/target` in `Clafer.Roles` | `Roles.incidence`; typed Shape arrows have the two exact endpoints |
| Table 6 parent and target cojoining | `Roles.Cojoining.parent`, `.target` | `Family.canonical_cojoining`, `primitive_cojoins_root`, `Examples.wrong_parent_cojoining_rejected`, `Examples.wrong_target_cojoining_rejected` |
| Table 6 head/source/target inclusions | `Family.InclusionSlot`, `Roles.inclusion` | `Roles.inclusion_incidence`, `super_has_head`, `no_super_no_inclusion`, `missing_sub_source`, `missing_super_source`, `missing_sub_target`, `missing_super_target`, `Examples.shared_source_present` |
| Table 7 Sing/root | `Family.WellFormed.root_origin`, `.root_shape` | `root_has_head`, `root_no_maps`, `no_super_no_inclusion`, `Examples.root_super_rejected` |
| Table 7 Dom: int/string/bool | `Family.WellFormed.primitive_shape`, `.unique_primitive` | `primitive_no_target`, `primitive_cojoins_root`, `Examples.family_valid` covers all three; `Examples.primitive_reference_rejected` |
| Table 7 basic/set/bag presence and modes | `Family.shape`, `ReferenceTo.kind/target`, `Clafer.Roles.classPresent/mapPresent/mode`, `Family.MapId.mode` | `reference_target_iff`, existing `Clafer.Roles.no_basic_target`, `.no_parent_source`, `.no_parent_maps`, `Examples.bag_mode` |
| Table 7 parentless exception | `Family.WellFormed.parentless_abstract` | `Examples.parentless_reference_retains_dref`, `Examples.family_valid` (abstract basic and reference), `Examples.missing_parent_rejected` |
| Table 8 head/parent/dref/target names | `Labels.WellFormed.head_name`, `.ordinary_name` | `target_name_via_head`, `Examples.labels_valid` |
| Table 8 Sing and each primitive equivalence, both directions | `Labels.WellFormed.sing_iff`, `.primitive_iff` | `reserved_names_exclude_users`, `Examples.user_named_Sing_rejected` |
| Inherited inclusion naming | `Labels.WellFormed.inclusion_name` | `Examples.repeated_inclusion_names` |
| Corrected ordinary/inclusion ownership | `Family.MapId` occurrence identities | `ordinary_owner_unique`, `inclusion_owner_unique` |
| Literal head-class and formula ownership | `Roles.Cojoining.head_bijective`, `Formulas.owner` | `Family.canonical_cojoining`, `Examples.sample_valid` |
| Role cover/disjointness and inclusion subtype | `Role`, `Family.MapId.inclusion`, `Family.MapId.mode` | `role_cover`, `role_disjoint`, typed inclusion incidence |
| Total labels and endpoints; PredefStr | `Labels.label`, `Roles.source/target`, `predefinedStrings` | `Labels.WellFormed`, `Roles.incidence` |
| Formula symbol, full binding and occurrence bag | `Formulas`, `.Arg`, `.argument`, `.diagram` | `Examples.repeated_occurrences_preserved`, `.repeated_args_valid` |
| Separate total args and literal (args,pred) key | `Formulas.WellFormed.total_args`, `.literal_key`, `Formulas.SameBag` | `Formulas.no_zero_arrow`, `.formula_injective`, `.sameBag_iff_map_roles`, `Examples.duplicate_formulas_rejected` |
| Local Shape diagram predicates | `Roles.localDiagram` translates existing `Shape.declarations` | `Roles.local_declared`, `Examples.shapes_compose` |

[Metamodel.lean](../Clafer/MCS/Metamodel.lean) enumerates all nine nodes and twenty
arrows of Figure 23. Its `Metamodel.diagram` uses the existing `FormalCD` vocabulary,
including bag args, literal key, role cover/disjointness, functional/total maps,
unchanged source-one ownership and the seven corrected source bounds.
The explicit `nd`/`ad` symbols attach to the whole structural context; the typed
bindings and separate validity propositions above state their contracts. This does
not assert a semantic self-instantiation or a concrete span interpretation of the
whole metamodel.

`Examples.sample` combines eleven owners, all primitive domains, basic/set/bag
shapes, parentless abstracts, two inheritance patterns and a nonempty formula
bank. `Examples.sample_valid` proves its complete structural obligations.
`Examples.repeated_parent_names`, `.repeated_dref_names` and
`.repeated_inclusion_names` retain distinct identities despite equal strings.
The sample bank contains inclusion declarations and unrestricted ordinary-arrow
bounds. Local inverse/triangle/key/default formulas can be transported by
`Roles.localDiagram`; [Compile](compile.md) generates them and proves its
formula-bank obligations separately. Structural validity neither assumes that
compilation theorem nor proves satisfaction of the declared constraints.

The [requirements](spec.md#mcs-metamodel-and-ownership) are linked by annotations
in the [metamodel](../Clafer/MCS/Metamodel.lean) and [structural laws](../Clafer/MCS/Laws.lean).

## Gluing boundary

The identity rule accepted in the [resolved-referent gluing issue](https://github.com/kbak/clafer-semantics/issues/23)
identifies equal resolved class/map referents only. `Gluing.Incidence` requires
equal map referents to have equal endpoint class referents. `Gluing.Compatible`
also requires equal class/map names, predefined annotations and map modes on
identified fibers. The registry determines kind from identity. Neither name
matching nor endpoint matching supplies a referent equality.

[Gluing.lean](../Clafer/MCS/Gluing.lean) proves graph incidence and exact
identification before constructing the translated declaration image and DP map.
These obligations are additional to `Valid`. Role-level ownership/cojoining,
the [guarded Appendix 5 clauses (Q2)](#appendix-e-inventory),
[source ownership bounds (Q9)](#figure-23-source-multiplicity-correction) and source
total-args/literal-key disciplines remain unchanged.
`Gluing.Naming` and `Gluing.Defaults` are separate prerequisites of the `FormalCD`
validity theorem. [Origins.lean](../Clafer/MCS/Gluing/Origins.lean) derives naming
from valid MCS origins, while effective-default completeness must still be
supplied. The existing nonempty `Examples.formulas` has ordinary multiplicity
formulas without setValued defaults: `Gluing.Boundaries.missing_default_rejected`
shows why DP preservation alone does not establish CD validity.

The positive gluing fixture proves `Gluing.Examples.valid`, `defaults` and
constructs `glued`, merging two user classes and two head maps but preserving
parallel parent maps. Its source key holds while translated formulas collide.
The [gluing boundary examples](../Clafer/MCS/Gluing/Boundaries.lean) check repeated
names, isolated vertices and repeated arguments.
