# Clafer implementation and proof links

These artifacts follow [the Lean trace convention](traceability.md). Source
locators and the accepted top-level abstract correction are in the
[source map](sources.md#resolved-2014-clafer-and-individual-shapes). All declarations
below are in namespace `Clafer`, with witnesses in `Clafer.Examples`. Kernel
checking establishes the Lean statements; independent review must assess their
correspondence to the paper and the selected input boundary.

Browse implementation and proof artifacts by topic:

- **Structure:** [syntax and Shapes](#deep-resolved-declarations),
  [MCS](#mcs-metamodel), [Compile](#compile-input-and-finite-identity-allocation) and
  [gluing](#mcs-gluing-representation).
- **Constraints:** [typing](#resolved-core-expression-constructors),
  [integer extraction](#integer-extraction-interface),
  [denotation](#resolved-constraint-denotation) and
  [preservation](#derived-source-predicate-meanings).
- **Realization:** [group generation](#interpreted-group-generation) and
  [inherited fields and abstract families](#selected-inherited-realization).
- **Verification:** [effective core](#effective-structural-core),
  [whole-model meaning](#whole-model-structural-meaning),
  [finite checker](#finite-structural-checker),
  [importer](#resolved-compiler-import-and-capture) and
  [bounded comparison](#external-bounded-comparison-execution).
- **Worked models:** [walkthrough](#small-model-walkthrough),
  [representative integration](#representative-model-integration) and
  [complete telematics](#complete-appendix-6-resolved-model).

## Deep resolved declarations

`impl~clafer-resolved-syntax~1`

[Syntax.lean](../Clafer/Syntax.lean): `Kind`, `Reference`, `Origin`,
`PrimitiveDomain`, `Declaration`, `Tree`, `Forest`, `Tree.branch`, `AST`, `Multiplicity`, `GroupCard`,
`GroupMultiplicity`, `Defaults`. [Context.lean](../Clafer/Context.lean) defines
`DeclId` separately from names. The forest stores containment; targets/supers
store IDs. Numeric groups and keywords retain distinct authored forms.

Covers:
- `req~clafer-resolved-syntax~1`

## Resolved syntax witnesses

`proof~clafer-resolved-syntax~1`

[Examples.lean](../Clafer/Examples.lean): `sample_wellFormed` constructs a mixed
model, including a primitive domain and an abstract reference; `repeated_names_distinct_ids`
checks identity separation. `keyword_default`, `explicit_overrides_keyword`,
`inherited_group_bounds`, `unbounded_range_valid` and `inverted_range_rejected`
exercise the resolved/defaulted multiplicity boundary. These are input validation
statements, not claims about a parser or resolver.

Covers:
- `req~clafer-resolved-syntax~1`

## Local input obligations

`impl~clafer-input-wellformedness~1`

[Syntax.lean](../Clafer/Syntax.lean): `AST.WellFormed`, `Kind.CanExtend`,
`ValidRange` and `Defaults` state resolved identity, root/domain, containment,
abstractness, inheritance, interval and constraint-context obligations. Rank is
proof data for inheritance acyclicity. Generic `FormalCD`/`DPGraph` contracts are reused.

Covers:
- `req~clafer-input-wellformedness~1`

## Input invariants and rejected cases

`proof~clafer-input-wellformedness~1`

[Syntax.lean](../Clafer/Syntax.lean): `AST.WellFormed.no_self_parent`,
`no_self_super`, `parent_wellFounded`, `super_wellFounded`. [Examples.lean](../Clafer/Examples.lean):
`sample_wellFormed`, `concrete_orphan_rejected`, `duplicate_ids_rejected`,
`different_inheritance_parents_rejected`, `self_inheritance_rejected`,
`primitive_reference_rejected`, `basic_reference_inheritance_rejected`,
`bag_set_inheritance_rejected`,
`set_bag_inheritance_allowed`, and `inverted_range_rejected` establish selected
positive/negative boundaries. These are not a complete decision procedure for
all AST validity conditions.

Covers:
- `req~clafer-input-wellformedness~1`

## Context and occurrence interface

`impl~clafer-constraint-boundary~1`

[Context.lean](../Clafer/Context.lean): `BinderId`, `Binder`,
`ConstraintBoundary`, `ConstraintBoundary.Resolved`, `Occurrence`, `referenced`.
The context and each occurrence are already resolved. Finite lists retain
repetitions; the constraint extension attaches typed bodies without a reverse
dependency from the boundary module.

Covers:
- `req~clafer-constraint-boundary~1`

## Context boundary witnesses

`proof~clafer-constraint-boundary~1`

[Examples.lean](../Clafer/Examples.lean): `repeated_scope_resolved`,
`repeated_scope_positions`, `dangling_scope_rejected`.
[Context.lean](../Clafer/Context.lean): `ConstraintBoundary.occurrences_finite`.
Different positions can name the same declaration; unknown IDs are rejected.
No expression typing or Appendix 4 semantic equation is asserted.

Covers:
- `req~clafer-constraint-boundary~1`

## Typed individual role graphs and local diagrams

`impl~clafer-individual-shapes~1`

[Shape.lean](../Clafer/Shape.lean): `Roles.classPresent`, `mapPresent`, `Class`,
`Map`, `Arrow`, `graph`, `mode`, `Shape`, `Located.shape`, `Shape.Realization`,
`SharedClass`, `Inclusions`, `OptionalInclusions`.
[Diagram.lean](../Clafer/Shape/Diagram.lean): `Shape.inverseBinding`,
`triangleBinding`, `keyBinding`, `declarations`, `raw`, `diagram`, `realization`.
These reuse graph-valued predicates and `FormalCD`'s defaults. Optionality is
controlled by kind and endpoints. Inheritance's inclusion arrows are typed in
one shared carrier; this does not impose the remaining global MCS equations.

Covers:
- `req~clafer-individual-shapes~1`

## Shape incidence, kind and optionality

`proof~clafer-individual-shapes~1`

[Shape.lean](../Clafer/Shape.lean): `Roles.endpoints_present`, `incidence`,
`no_basic_target`, `no_parent_source`, `no_parent_maps`, `root_only_head`,
`root_no_maps`, `Located.shape_has_head`, `parentless_has_no_source`,
`Shape.no_source_inclusion`, `Shape.Inclusions.declared` (under `FormalCD` well-formedness).
[Diagram.lean](../Clafer/Shape/Diagram.lean): `Shape.raw_wellFormed`,
`inverse_declared`, `key_declared`, `key_conditions`.
[Examples.lean](../Clafer/Examples.lean): constructible `basicShape`, `setShape`,
`bagShape`, `abstractShape`, `abstractReferenceShape` and their map witnesses;
`abstract_basic_keeps_head`, `abstract_reference_incidence`, `reference_modes`,
`key_guard`, `wrong_head_incidence_uninhabitable`, `abstract_inclusion_has_head`,
`abstract_inclusion_has_target`, `abstract_reference_no_key`, `bag_no_key`, and
`inclusion_witness_no_source`. `inclusionWitness`, `withSuper` and `withoutSuper`
construct the optional inclusion data in a partial carrier. The local CD proof is syntactic, not satisfaction
or existence of an instance.

Covers:
- `req~clafer-individual-shapes~1`

## Structural traversal

`impl~clafer-finite-traversal~1`

[Syntax.lean](../Clafer/Syntax.lean): `Tree.fold`, `Forest.fold`, `Tree.entries`, `Forest.entries`, `AST.entries`,
`AST.Occurrence`, `AST.at` provide structural processing and finite indexing.
[Shape.lean](../Clafer/Shape.lean) restricts roles to finite enums/subtypes.
Reference and inheritance IDs remain data; neither is a recursive subtree.
The primitive-recursive folds/traversal are kernel-reducible and marked
`noncomputable` for native code generation; this is a mathematical compilation
basis, not an executable compiler. The AST constructors remain directly usable.

Covers:
- `req~clafer-finite-traversal~1`

## Finite representation and decreasing measures

`proof~clafer-finite-traversal~1`

[Syntax.lean](../Clafer/Syntax.lean): `Tree.child_smaller`,
`AST.occurrences_finite`, `AST.every_entry_indexed`, `AST.WellFormed.parent_wellFounded`.
[Shape.lean](../Clafer/Shape.lean): `Roles.classes_finite`, `arrows_finite`,
`Shape.inclusion_roles_finite`.
[Examples.lean](../Clafer/Examples.lean): `finite_reference_cycle` and `fold_counts_reference_cycle` count the
complete traversal despite cyclic reference edges. No compilation or parser
correctness theorem follows from these finite presentation results.

Covers:
- `req~clafer-finite-traversal~1`

## MCS metamodel

`impl~clafer-mcs-metamodel~1`

[MCS/Metamodel.lean](../Clafer/MCS/Metamodel.lean): `Metamodel.Node`, `Edge`,
`declarations`, `raw`, `diagram`, `corrected`, `isOwned`. [MCS/Basic.lean](../Clafer/MCS/Basic.lean):
`Family.MapId`, `Role`, `Roles.graph`, `Labels`, `predefinedStrings`,
`Roles.Cojoining.head_bijective`, `Formulas.owner`. These declarations separate
role identities, referents and strings and encode the accepted ownership bounds.

Covers:
- `req~clafer-mcs-metamodel~1`

## MCS metamodel boundaries

`proof~clafer-mcs-metamodel~1`

[MCS/Metamodel.lean](../Clafer/MCS/Metamodel.lean): `Metamodel.wellFormed`,
`twenty_edges`, `edges_complete`, `corrected_declared`, `ownership_declared`,
`correction_boundary`, `args_total_declared`, `literal_key_declared`.
[MCS/Laws.lean](../Clafer/MCS/Laws.lean): `role_cover`, `role_disjoint`,
`ordinary_owner_unique`, `inclusion_owner_unique`, `Family.canonical_cojoining`.
[MCS/Examples.lean](../Clafer/MCS/Examples.lean): `repeated_parent_names`,
`repeated_dref_names`, `repeated_inclusion_names`, `sample_valid`.
These are structural statements; no whole-metagraph semantic instantiation is claimed.

Covers:
- `req~clafer-mcs-metamodel~1`

<a id="mcs-appendix-e-definitions"></a>

## MCS Appendix 5 definitions

`impl~clafer-mcs-disciplines~1`

[MCS/Basic.lean](../Clafer/MCS/Basic.lean): `Family`, `Family.WellFormed`,
`Family.shape`, `Family.InclusionSlot`, `Roles.binding`, `Roles.Cojoining`,
`Labels.WellFormed`, `Valid`, `Model`. The [inventory](mcs-invariants.md#definition-and-proof-map)
expands every printed row and analogous case, with exact declarations and guards.

Covers:
- `req~clafer-mcs-disciplines~1`

## MCS structural laws and nonempty composition

`proof~clafer-mcs-disciplines~1`

[MCS/Laws.lean](../Clafer/MCS/Laws.lean): `Roles.incidence`, `Roles.inclusion_incidence`,
`Family.canonical_cojoining`, `no_super_no_inclusion`, `super_has_head`,
`missing_sub_source`, `missing_super_source`, `missing_sub_target`, `missing_super_target`,
`root_no_maps`, `root_has_head`, `primitive_no_target`, `primitive_cojoins_root`,
`reference_target_iff`, `Family.WellFormed.no_self_parent`, `.no_self_super`,
`target_name_via_head`, `reserved_names_exclude_users`.
[MCS/Examples.lean](../Clafer/MCS/Examples.lean): `family_valid`, `labels_valid`,
`sample_valid`, `shapes_compose`, `parentless_reference_retains_dref`,
`missing_inherited_source`, `shared_source_present`, `bag_mode`,
`wrong_cojoining_rejected`, `wrong_parent_cojoining_rejected`,
`wrong_target_cojoining_rejected`, `missing_parent_rejected`,
`primitive_reference_rejected`, `root_super_rejected`, `user_named_Sing_rejected`.
The eleven-owner example covers int/string/bool and basic/set/bag, parentless
abstracts, both shared-source and absent-source inheritance.

Covers:
- `req~clafer-mcs-disciplines~1`

## MCS formula representation

`impl~clafer-mcs-formulas~1`

[MCS/Basic.lean](../Clafer/MCS/Basic.lean): `Formulas`, `Formulas.Arg`, `.argument`,
`.SameBag`, `.WellFormed`, `.diagram`. [MCS/Laws.lean](../Clafer/MCS/Laws.lean):
`Roles.localDiagram`. Full bindings and indexed occurrences are retained; the
literal bag key and total arguments are additional, separately checked propositions.

Covers:
- `req~clafer-mcs-formulas~1`

## MCS formula boundary proofs

`proof~clafer-mcs-formulas~1`

[MCS/Laws.lean](../Clafer/MCS/Laws.lean): `Formulas.no_zero_arrow`,
`Formulas.formula_injective`, `Formulas.sameBag_iff_map_roles`,
`Roles.arrowData_ext`, `Roles.local_declared`.
[MCS/Examples.lean](../Clafer/MCS/Examples.lean): `formulas_valid`,
`duplicate_formulas_rejected`, `repeated_args_valid`, `repeated_occurrences_preserved`.
These establish structural formula-bank conditions, not generation of the complete
Compile output or semantic satisfaction of the declarations.

Covers:
- `req~clafer-mcs-formulas~1`

## Resolved core expression constructors

`impl~clafer-core-typing~1`

[Typing.lean](../Clafer/Constraints/Typing.lean): `Constraints.Collection`, `Ty`,
`SetOp`, `Arithmetic`, `Expr`, and `Expr.some/no/one/lone` implement the selected
D.1–D.3 forms. `Expr.widenObjects` and `widenRelation` carry explicit
`Constraints.Widen` paths from [Support.lean](../Clafer/Constraints/Support.lean).
No evaluator or semantic preservation theorem is implemented. Integer-only
arithmetic is an implementation boundary, not a claim that D.3 forbids other
primitive domains. The [Appendix 4 notation decision (Q3)](sources.md#appendix-d-rule-dispositions-q3)
is recorded in the source map.

Covers:
- `req~clafer-core-typing~1`

## Core typing witnesses and rejection assertions

`proof~clafer-core-typing~1`

[Constraints/Examples.lean](../Clafer/Constraints/Examples.lean), namespace
`Clafer.Constraints.Examples`: `navigation`, `inheritedNavigation`, `composed`,
`inheritedJoin`, `compatibleUnion`, `numericConstraint`, `collectionConstraint`,
`relationConstraint`
and `duplicateIdentity` are actual indexed expression values. The named
`wrong_image_rejected`, `wrong_join_rejected`, `mixed_collection_rejected`,
`bare_set_is_not_boolean`, `boolean_arithmetic_rejected`,
`integer_cardinality_rejected` and `mixed_equality_rejected` assertions use
`fail_if_success` on construction of the invalid terms. They check elaboration
failure; their `True` conclusions are not semantic impossibility theorems.
`non_inclusion_cannot_widen` checks a non-inheritance map's kind;
`unrelated_widening_rejected` proves that a path to an unrelated class cannot exist.

Covers:
- `req~clafer-core-typing~1`

## Lexical binding and compiler assumptions

`impl~clafer-core-binding~1`

[Typing.lean](../Clafer/Constraints/Typing.lean): `Local`, `Var`, `Expr.all`,
`Domains`, `Constraint`, `Constraint.Input`, `ResolvedConstraint` retain lexical
scope, typed external
domains, AST validity and the resolved boundary assumptions. `Support.Boundary`
in [Support.lean](../Clafer/Constraints/Support.lean) maps each recorded scope
and domain occurrence separately. `Constraint.Input` does not claim that the
boundary bags were computed by traversing the expression.

Covers:
- `req~clafer-core-binding~1`

## Binder scope and resolved-input evidence

`proof~clafer-core-binding~1`

[Typing.lean](../Clafer/Constraints/Typing.lean): `Var.index_lt`, `Var.lookup`,
`Var.closed` establish valid lexical positions and the absence of a closed free
variable. `Var.index` and `Path.navigate` use kernel-reducible primitive recursors
with native code generation omitted, as for the existing tree folds. [Constraints/Examples.lean](../Clafer/Constraints/Examples.lean):
`quantified`, `nested`, `shadowed_name_keeps_ids`, `outer_variable_position`,
`externalDomains`, `constraint_input`, `resolvedConstraint`, `external_input`,
`repeated_scope_retained`
and `repeated_domain_retained` give positive
witnesses. `nonboolean_body_rejected`, `relation_domain_rejected`,
`out_of_scope_rejected` and `domain_cannot_use_own_binder` are failed-construction
assertions; `duplicate_binder_id_rejected` proves the freshness condition false.
The singleton meaning of a variable is documented, not proved by these statements.

Covers:
- `req~clafer-core-binding~1`

## Graph support and predicate seam

`impl~clafer-core-support~1`

[Support.lean](../Clafer/Constraints/Support.lean): `MapKind`, `MapRef`, `Support`,
`Support.Arrow`, `graph`, `arrow`, `MapResolved`, `Resolved`, `DirectSuper`,
`Extends`, `Widen`, `Support.Boundary`.
[Typing.lean](../Clafer/Constraints/Typing.lean): `Path`, `Path.navigate`,
`signature`, `Constraint.formula`. The signature records graph arity only;
semantic interpretation and actual compilation remain separate work.

Covers:
- `req~clafer-core-support~1`

## Navigation, inheritance and full binding evidence

`proof~clafer-core-support~1`

[Support.lean](../Clafer/Constraints/Support.lean): `Support.incidence` and
`Widen.resolved` prove incidence and actual inheritance ancestry;
`Extends.preserves` transports invariants along inheritance.
[Typing.lean](../Clafer/Constraints/Typing.lean): `Path.navigate` is an
endpoint-indexed construction of well-typed navigation; `Path.navigate_nil`
and `Constraint.formula_binding` preserve the supplied start/binding exactly.
[Constraints/Examples.lean](../Clafer/Constraints/Examples.lean):
`support_resolved`, `widening_follows_super`, `pathNavigation`,
`repeated_scope_retained`, `repeated_maps_retained`, `full_graph_binding`,
`wrong_map_incidence_rejected`.
None of these declarations asserts satisfaction of a constraint predicate.

Covers:
- `req~clafer-core-support~1`

## Compile input and finite identity allocation

`impl~clafer-compile-structure~1`

[Compile/Structure.lean](../Clafer/Compile/Structure.lean) defines `Compile.Input`,
`ConstraintId`, `find`, `resolve`, `family`, `roles` and `labels`.
[Compile/Basic.lean](../Clafer/Compile/Basic.lean) defines `compile` as the actual
MCS construction. The [contract](compile.md) states its assumptions and limits.

Covers:
- `req~clafer-compile-contract~1`
- `req~clafer-compile-structure~1`

## Compile structural preservation

`proof~clafer-compile-structure~1`

In [Structure](../Clafer/Compile/Structure.lean), `find_spec`, `sourceId_injective`,
`resolve_sourceId`, `parent_ids`, `super_ids`, `target_ids`, `shape_preserved`,
`family_wellFormed`, `naming`, `heads_bijective`, `names_preserved` and `referents_preserved` prove
finite resolution and structural preservation. In
`naming`, the private `primitive_name_injective` and `primitive_name_ne_sing`
lemmas isolate the finite canonical-name checks of Table 8 (see Appendix 5). In
[Basic](../Clafer/Compile/Basic.lean), `wellFormed`, `fresh_heads`, `fresh_maps`,
`shared_target` and `maps_finite` establish output validity, freshness, resolved
sharing and finite generated map carriers.
[Examples](../Clafer/Compile/Examples.lean) checks `output_valid`,
`nested_repeated_names`, `shared_reference_target`,
`shared_target_distinct_dereferences`, `inheritance_preserved`,
`primitive_identity`, `reserved_user_rejected`, `zero_map_rejected`,
`zero_generic_input` and `zero_not_compile_support`.
These are structural theorems; no expression interpretation is assumed.

Covers:
- `req~clafer-compile-contract~1`
- `req~clafer-compile-structure~1`

## Compile declarations and occurrence bindings

`impl~clafer-compile-formulas~1`

[Binding](../Clafer/Compile/Binding.lean) constructs `vertex`, `mapOwner`,
`boundArrow` and `binding` from resolved support.
[Local](../Clafer/Compile/Local.lean) defines `LocalId`, `LocalId.formula` and
`localFormulas`. [Basic](../Clafer/Compile/Basic.lean) combines these with typed
constraints using `vocabulary`, `FormulaId`, `formula` and `formulas`.

Covers:
- `req~clafer-compile-formulas~1`

## Compile formula validity and completeness

`proof~clafer-compile-formulas~1`

[Binding](../Clafer/Compile/Binding.lean): `map_spec`, `binding_vertices`,
`binding_maps` and `binding_context` establish incidence, complete support
mapping and owner context. [Local](../Clafer/Compile/Local.lean):
`LocalId.argument_owner`, `LocalId.key_unique`, `localFormulas_wellFormed` and
`local_complete` derive the local bag key and generation completeness.
[Basic](../Clafer/Compile/Basic.lean): `formulas_wellFormed`, `shape_declared`,
`inclusion_declared`, `constraint_declared`, `constraint_owner` and
`constraint_binding` establish the combined bank contract.
[Examples](../Clafer/Compile/Examples.lean): `repeated_support_maps`,
`repeated_support_vertices`, `isolated_vertex_retained`,
`repeated_constraint_boundaries` and
`compiled_constraint_present` exercise occurrence preservation in actual output.

Covers:
- `req~clafer-compile-formulas~1`

## Compile group metadata and direct-child inventory

`impl~clafer-compile-group-data~1`

[MCS/Basic.lean](../Clafer/MCS/Basic.lean) adds `Family.group` as metadata;
the existing MCS structural disciplines do not interpret it.
[Compile/Structure.lean](../Clafer/Compile/Structure.lean) carries the complete
group record in `family`. `DirectChild` selects exactly declarations whose
resolved parent is the owner; `directChildHead` constructs their typed head maps.
These declarations do not generate group predicates or select inherited paths.

Covers:
- `req~clafer-compile-group-data~1`

## Compile group data preservation proofs

`proof~clafer-compile-group-data~1`

In [Structure](../Clafer/Compile/Structure.lean), `group_preserved` retains the
whole metadata record, `group_bounds_valid` derives valid effective bounds,
`directChild_iff` relates the inventory to source IDs, and
`directChildHead_owner`/`directChildHead_injective` retain distinct child map
identities. `directChildren_finite` derives finiteness from AST occurrences.
[Examples](../Clafer/Compile/Examples.lean) checks
`empty_xor_metadata_preserved`, `nested_has_no_direct_children`,
`nested_child_head_incidence` and `reference_child_head_not_target`.
The empty xor witness is accepted input, not a claim that its bound is enforced.

Covers:
- `req~clafer-compile-group-data~1`

## MCS gluing representation

`impl~clafer-gluing-identity~1`

[Gluing.lean](../Clafer/MCS/Gluing.lean), namespace `Clafer.MCS.Gluing`:
`Class`, `Map`, `classLabel`, `mapLabel`, `Incidence`, `source`, `target`,
`Arrow`, `graph`, `label`, `labeledArrow`, `Compatible`. Used referents determine
identity; representative choice only defines functions on already chosen fibers.
Compatibility checks incidence, names, registry annotations and modes.

Covers:
- `req~clafer-gluing-identity~1`
- `req~clafer-mcs-metamodel~1`
- `req~clafer-mcs-disciplines~1`

## MCS gluing identification proofs

`proof~clafer-gluing-identity~1`

[Gluing.lean](../Clafer/MCS/Gluing.lean): `classLabel_eq_iff`, `mapLabel_eq_iff`,
`classRepresentative_spec`, `mapRepresentative_spec`, `source_label`,
`target_label`, `arrowData_ext`, `labeledArrow_eq_iff`, `label_obj_surjective`.
The total-arrow equality theorem includes endpoint agreement and ensures
that different map referents cannot collapse even at equal endpoints/names.

Covers:
- `req~clafer-gluing-identity~1`

## Exact declaration image

`impl~clafer-gluing-declarations~1`

[Gluing.lean](../Clafer/MCS/Gluing.lean): `diagram`, `labelHom`. Declarations
are a set image of complete translated formulas; the source bank's indexed
identity and key are not asserted for the target image.

Covers:
- `req~clafer-gluing-declarations~1`
- `req~clafer-mcs-formulas~1`
- `req~dpgraph-morphisms~1`

## Declaration and binding preservation

`proof~clafer-gluing-declarations~1`

[Gluing.lean](../Clafer/MCS/Gluing.lean): `declared_iff`, the `preserves` proof
in `labelHom`, `translated_vertex`, `translated_arrow`. `label` is the actual
incidence-checked Prefunctor used by every formula translation.

Covers:
- `req~clafer-gluing-declarations~1`

## Glued CD metadata and assumptions

`impl~clafer-gluing-formalcd~1`

[Gluing.lean](../Clafer/MCS/Gluing.lean): `raw`, `Naming`, `Defaults`, `cd`.
[Origins.lean](../Clafer/MCS/Gluing/Origins.lean): `Predefined`, `registry`,
`originAnnotation`, `annotations`, `ofValid`. Names are metadata; semantic
origins select registry identities and kinds. Defaults are source-bank
membership hypotheses over the compatible vocabulary embedding.

Covers:
- `req~clafer-gluing-formalcd~1`
- `req~formalcd-structure~1`
- `req~formalcd-naming~1`
- `req~formalcd-declarations~1`
- `req~formalcd-morphisms~1`

## Separate FormalCD well-formedness

`proof~clafer-gluing-formalcd~1`

[Gluing.lean](../Clafer/MCS/Gluing.lean): `className_label`, `mapName_label`,
`predefined_label`, `kind_label`, `mode_label`, `raw_wellFormed`.
[Origins.lean](../Clafer/MCS/Gluing/Origins.lean): `annotations_head`,
`naming_of_valid`, with private `originAnnotation_injective` recovering semantic
origins from annotations (§6.1 / Table 8 (see Appendix 5)). `naming_of_valid` derives
naming and predefined uniqueness from `MCS.Valid`, but neither it nor `labelHom`
assumes effective-default completeness.
`raw_wellFormed` explicitly requires that separate hypothesis.

Covers:
- `req~clafer-gluing-formalcd~1`

## MCS gluing acceptance fixtures

`impl~clafer-gluing-examples~1`

[Examples.lean](../Clafer/MCS/Gluing/Examples.lean), namespace
`Clafer.MCS.Gluing.Examples`: `family`, `labels`, `predef`, `formulas`, `glued`,
`emptyBank`, `badEndpoints`, `badClassNames`, `badMapNames`, `badAnnotation`.
[Boundaries.lean](../Clafer/MCS/Gluing/Boundaries.lean), namespace
`Clafer.MCS.Gluing.Boundaries`: the existing eleven-owner MCS fixture,
`modeConflict`, `completeBank`, `completeCD`, `Isolated.binding`, `Isolated.bank`.

Covers:
- `req~clafer-gluing-examples~1`

## MCS gluing acceptance proofs

`proof~clafer-gluing-examples~1`

[Examples.lean](../Clafer/MCS/Gluing/Examples.lean): `compatible`, `valid`,
`defaults`, `intentional_class_merge`, `intentional_map_merge`,
`parallel_maps_distinct`, `translated_formulas_not_injective`,
`canonical_name_preserved`, `registry_kind_preserved`, `empty_valid`,
`empty_defaults_rejected`, `empty_cd_rejected`, `source_conflict_rejected`,
`target_conflict_rejected`, `class_name_conflict_rejected`,
`map_name_conflict_rejected`, `annotation_and_kind_conflict_rejected`.
The nonempty source bank satisfies the literal bag key even though its
translated formulas are not injective. `glued` carries the separate CD proof.

[Boundaries.lean](../Clafer/MCS/Gluing/Boundaries.lean):
`repeated_parent_not_identified`, `repeated_isA_not_identified`,
`bag_mode_preserved`, `bag_has_no_added_setValued`, `missing_default_rejected`,
`mode_conflict_rejected`, `spelling_does_not_create_marker`,
`reserved_spelling_rejected`, `primitive_identity_preserved`,
`complete_valid`, `complete_defaults`, `inclusion_default_preserved`,
`repeated_arguments_retained`,
`Isolated.bank_valid`, `Isolated.isolated_vertex_retained`,
`Isolated.isolated_declaration_preserved`. These are kernel-checked structural
claims, not model satisfaction or compiler correctness statements.

Covers:
- `req~clafer-gluing-examples~1`

## Integer extraction interface

`impl~clafer-integer-extraction~1`

[Support.lean](../Clafer/Constraints/Support.lean): `Support.integer` and
`Support.Resolved.integers` preserve primitive resolved IDs.
[Typing.lean](../Clafer/Constraints/Typing.lean): `Expr.integerOf` accepts an
annotated unary integer collection in the existing lexical context.
[FormalCD integer realization](../FormalCD/Integer.lean) supplies `Extracts`,
`WellDefined`, `extract` and `objectEquiv`; [DPGraph navigation](../DPGraph/Predicates/Navigation.lean)
supplies `navigationImage`. [Integer.lean](../Clafer/Constraints/Integer.lean)
re-exports compatibility names and defines `IntegerBinding`. No VC import is
needed to interpret expressions.

Covers:
- `req~clafer-integer-extraction~1`

## Integer extraction correspondence and boundaries

`proof~clafer-integer-extraction~1`

[FormalCD/Integer.lean](../FormalCD/Integer.lean): `extracts_unique`,
`wellDefined_iff`, `extract_eq_some_iff`, `extract_none_iff`, `encode_decode`,
`objectEquiv`, `extract_encoded`, `extract_empty`, `extract_multiple`,
`extract_wrong_domain`. [Clafer binding](../Clafer/Constraints/Integer.lean):
`IntegerBinding.widen_subset`, `singleton_defined`.
[DPGraph navigation](../DPGraph/Predicates/Navigation.lean): `navigationImage_empty`, `navigationImage_subset`, `navigationImage_singleton`, `navigationImage_one`
and `function_one` establish the domain, uniqueness and navigation hypotheses.
[IntegerExamples.lean](../Clafer/Constraints/IntegerExamples.lean): `empty`,
`empty_navigation`, `multiple`, `wrong_domain`, `negative_unbounded`, `wrong_sort_rejected` and
`forged_primitive_rejected` check the actual extraction/typing/resolution boundary.
`potentiallyEmpty` is a well-typed operand without a runtime singleton guarantee.

Covers:
- `req~clafer-integer-extraction~1`

<a id="appendix-f-selected-version-navigation"></a>

## Appendix 6 selected version navigation

`impl~clafer-version-navigation~1`

[IntegerNavigation.lean](../Clafer/Constraints/IntegerNavigation.lean), namespace
`VersionNavigation`: `fragment`, `support`, `displayWiden`, `ecuWiden`, `version`,
`displayVersion`, `serverVersion`, `comparison`, `constraint`, `Model`,
`Model.versionObjects`, `Model.serverObjects` and `compareVersions` retain the
selected actual declaration/reference paths and partial comparison. `Model`
assumes the selected semantic link bounds, not the resulting singleton operands.

Covers:
- `req~clafer-version-navigation~1`

<a id="appendix-f-operand-definedness-and-comparisons"></a>

## Appendix 6 operand definedness and comparisons

`proof~clafer-version-navigation~1`

[IntegerNavigation.lean](../Clafer/Constraints/IntegerNavigation.lean):
`fragment_wellFormed`, `support_resolved`, `default_multiplicities`,
`constraint_input`, `Model.version_singleton`, `Model.server_singleton`,
`Model.operands_defined`, `Model.comparison_defined`, `compareVersions_encoded`,
`compareVersions_not_less`.
[IntegerExamples.lean](../Clafer/Constraints/IntegerExamples.lean): `model`,
`display_objects`, `server_objects`, `server_version_objects`, `comparison_value`,
`greater`, `equal`, `lower`, `empty_server`, `multiple_server` and
`wrong_domain_server` exercise concrete reference-object navigation and the
accepted direction. The example domain contains all integers. These are selected
fragment claims, not whole Appendix 6 model satisfaction or Figure 21's guarded VC.

Covers:
- `req~clafer-version-navigation~1`

## Effective structural core

`impl~clafer-effective-core~1`

[EffectiveCore.lean](../Clafer/Semantics/EffectiveCore.lean): `EffectiveCore`,
`WellFormed`, `Supported`. [Compile erasure](../Clafer/Compile/EffectiveCore.lean): `erase`. [Admission.lean](../Clafer/Verification/Admission.lean):
`CoreCertificate`, `coreChecks`, `supportChecks`. The
[interface](structural-checker.md) explains effective fields and fragment guards.

Covers:
- `req~clafer-effective-core~1`

## Effective-core correspondence proofs

`proof~clafer-effective-core~1`

[Compile/EffectiveCore.lean](../Clafer/Compile/EffectiveCore.lean): `erase_wellFormed`,
`erase_shape`. [Bridge.lean](../Clafer/Semantics/Bridge.lean): `ConstraintFree`,
`compiled_bank_iff`, `erasure_correspondence`, `equal_erasure_satisfaction`.
[Admission.lean](../Clafer/Verification/Admission.lean): `admitted_wellFormed`,
`admitted_supported`, `certificate_exists`. Erasure uses the existing
`Compile.Input` and its naming/default obligations; no authored AST is fabricated.

Covers:
- `req~clafer-effective-core~1`

## Whole-model structural meaning

`impl~clafer-structural-satisfaction~1`

[Structural.lean](../Clafer/Semantics/Structural.lean): `Configuration`,
`StructuralSatisfies`, `Typed`, `Rooted`, `Inherits`, `Abstracts`, `Parents`,
`References`, `Keys`, `Multiplicities`, `Child`, `Groups`, `DeclarationDisjoint`.
[Inheritance.lean](../Clafer/Semantics/Inheritance.lean): `EffectiveCore.Ancestor`
is super-edge closure; `next` supplies the finite decision procedure.
[Interpretation.lean](../Clafer/Semantics/Interpretation.lean): `headMap`,
`derefMap`, `targetMap`, `ordinaryMap`, `inclusionMap`, `interpret`.
[Bridge.lean](../Clafer/Semantics/Bridge.lean): `LocalConditions`,
`GlobalConditions`, `structuralInterpretation`, `SatisfiesAST`.

Covers:
- `req~clafer-structural-satisfaction~1`

## Structural interpretation and representation proofs

`proof~clafer-structural-satisfaction~1`

[Bridge.lean](../Clafer/Semantics/Bridge.lean): `key_local_iff`, `local_model_iff`,
`structural_model_iff` connect independent clauses to the exact local compiled
bank plus explicit global obligations. [Abstracts.lean](../Clafer/Semantics/Abstracts.lean):
`abstracts_iff` gives the existing Cover/[Q8](sources.md#predicate-contracts-and-the-accepted-q8-correction) Disjoint meaning.
[Structural.lean](../Clafer/Semantics/Structural.lean): `declarationDisjoint_iff`
relates shared-head comparability to pairwise disjointness of incomparable heads.
[Inheritance.lean](../Clafer/Semantics/Inheritance.lean): `ancestor_iff_iterate`,
`iterate_bounded`, `ancestor_iff_bounded` justify the terminating ancestry decision
without admission assumptions.
[DPGraph relational laws](../DPGraph/Predicates/Relational.lean): `inRange_one_iff`,
`one_iff_total_single`, `compositeFiber`, `composite_multiplicity`, `two_key_iff`.
[Clafer/Relational.lean](../Clafer/Semantics/Relational.lean) retains compatibility
names and proves `parent_one_iff`, `deref_one_iff`. [Interpretation.lean](../Clafer/Semantics/Interpretation.lean):
`headFiberEquiv`, `head_multiplicity_iff`, `ordinary_representation`.
[Normalization.lean](../Clafer/Semantics/Normalization.lean): `SpanModel.headIso`,
`derefIso`, `parentIso`, `targetIso`, `inheritedIso`, `normalize_satisfies` extract
simultaneous relational representatives from arbitrary local-bank models.
[Representation.lean](../Clafer/Verification/Representation.lean): `realize_encode`,
`representable`, `finite_model_representable` give finite completeness.
[Renaming.lean](../Clafer/Semantics/Renaming.lean): `structural_rename`.
[Reachability.lean](../Clafer/Semantics/Reachability.lean): `structural_reaches`,
`concrete_descendant`, `unused_abstract_empty`.

Covers:
- `req~clafer-structural-satisfaction~1`
- `req~predicate-key~1`
- `req~predicate-key-functional~1`
- `req~predicate-multiplicity~1`
- `req~predicate-interpretation~1`

## Finite structural checker

`impl~clafer-finite-checker~1`

[Finite.lean](../Clafer/Verification/Finite.lean): `Candidate`, `realize`,
`multiplicityChecks`, `groupChecks`, `Checks`, `check`; `CountInRange` is re-exported
from [DPGraph](../DPGraph/Predicates/Finite.lean).
[Protocol.lean](../Clafer/Verification/Protocol.lean): `RawCandidate`, `decode`,
`InputError`, `Result`, `verify`. [Admission.lean](../Clafer/Verification/Admission.lean):
`RunResult`, `run`. Ordinary tuples and reference-head occurrences retain distinct
identities; [protocol documentation](structural-checker.md#executable-interface)
states error priority and checked-certificate input requirements.

Covers:
- `req~clafer-finite-checker~1`

## Checker and protocol correctness

`proof~clafer-finite-checker~1`

[DPGraph/Finite.lean](../DPGraph/Predicates/Finite.lean): `inRange_card`.
[Verification/Finite.lean](../Clafer/Verification/Finite.lean): `checks_iff`,
`check_correct`, `malformed_rejected`. [ProtocolProofs.lean](../Clafer/Verification/ProtocolProofs.lean):
`decode_root`, `decode_members`, `decode_containment`, `decode_references`,
`objectLabels`, `member_row_preserved`, `link_row_indices`, `tuple_identity`,
`verify_correct`, `verify_violation`, `illTyped_rejected`, `success_tablesValid`,
`malformed_tables_rejected`, `run_correct`. [Protocol.lean](../Clafer/Verification/Protocol.lean):
`duplicate_objects_rejected`, `missing_root_rejected`.
[Admission.lean](../Clafer/Verification/Admission.lean): `unsupported_rejected`.
These are kernel proofs; no claim of fresh per-instance proof certificates is made
for native execution.

Covers:
- `req~clafer-finite-checker~1`

## Structural checker fixtures and mutation controls

`impl~clafer-checker-witnesses~1`

[Examples.lean](../Clafer/Verification/Examples.lean), namespace
`Clafer.Verification.Examples`: `refs`, `bag`, `collapsed`, `overlapping`,
`rawBag`, `inheritance`, `nested`, `siblingOverlap`, `uncovered`, `emptyClasses`,
`cyclic`, `cycle`, `noOccurrences`, `twoParents`, `sharedTarget`,
`multipleParents`, `multipleTargets`, `unusedChain`, `onlyRoot`,
`collapseMutant`, `upperBoundMutant`, `missingChild`, `relaxedGroup`, `executableTests`.

Covers:
- `req~clafer-checker-witnesses~1`

## Structural checker kernel witnesses

`proof~clafer-checker-witnesses~1`

[Examples.lean](../Clafer/Verification/Examples.lean): `bag_satisfies`,
`set_not_satisfies`, `set_rejects_repetition`, `exact_two_accepts`,
`optional_rejects_two`, `zero_rejects_two`, `lower_three_rejects`,
`unbounded_accepts`, `group_three_accepts`, `group_two_rejects`,
`unrelated_overlap_rejected`, `unrelated_overlap_typed`, `overlap_group_union`,
`overlap_old_checks`, `overlap_protocol_violates`, `nested_overlap_typed`,
`nested_overlap_rejected`, `separate_trees_overlap_violates`,
`separate_trees_distinct_satisfy`, `missing_target_violates`, `missing_target_typed`,
`nested_satisfies`, `nested_reachable`, `sibling_overlap_rejected`,
`uncovered_abstract_rejected`, `empty_classes_accept`, `reference_cycle_accepts`,
`zero_accepts_empty`, `optional_accepts_empty`, `optional_accepts_one`,
`missing_child_group_rejected`, `missing_child_locally_valid`,
`set_shared_target_accepts`, `multiple_parents_typed`, `multiple_parents_rejected`,
`multiple_targets_typed`, `multiple_targets_rejected`, `unused_chain_satisfies`,
`protocol_accepts`, `protocol_set_violates`, `duplicate_identity`,
`duplicate_tuple`, `duplicate_membership`, `missing_root`, `dangling_identity`,
`unknown_class`, `ill_typed_endpoint`, `empty_reference_table_violates`,
`collapse_mutant_killed`, `upper_bound_mutant_killed`. Reduction-based witnesses
exercise finite inputs without `native_decide` or new axioms.

Covers:
- `req~clafer-checker-witnesses~1`

## Structural checker native regression execution

`utest~clafer-structural-checker~1`

[structural_checker.lean](../tests/structural_checker.lean) executes
`Clafer.Verification.Examples.executableTests` from
[Examples.lean](../Clafer/Verification/Examples.lean), including mutation controls
on unchanged reference fixtures. `scripts/check.sh` discovers and runs this test
and builds/audits/replays all library witness modules. Command-level evidence
records the full command outcome, not a separate per-artifact certificate.

Covers:
- `req~clafer-finite-checker~1`
- `req~clafer-checker-witnesses~1`

## Interpreted group generation

`impl~clafer-compile-groups~1`

[GroupSupport.lean](../Clafer/Compile/GroupSupport.lean): `Ancestor`, `Child`,
`arity`, `binding`, `Id`, `Objects`, `interpretation`, `ChildObjects`, `Holds`.
[Groups.lean](../Clafer/Compile/Groups.lean): `groupBank`, `groupVocabulary`,
`promote`, `generatedGroup`, `completeBank`, `Augmented`, `compileAugmented`,
`gluedGroups`, `groupInterpretation`. The complete union keeps the original
MCS bank separate from vertex-only generated declarations.

Covers:
- `req~clafer-compile-groups~1`
- `req~clafer-compile-formulas~1`
- `req~clafer-gluing-declarations~1`

## Group generation and gluing correspondence

`proof~clafer-compile-groups~1`

[GroupSupport.lean](../Clafer/Compile/GroupSupport.lean): `binding_context`,
`child_iff`. [Groups.lean](../Clafer/Compile/Groups.lean): `forget_augmented`,
`complete_declarations`, `group_declared`, `group_owner`, `group_context`,
`complete_defaults`, `groupCompatible`, `glued_declarations`, `glued_group_declared`,
`group_label_unlabel`, `original_satisfaction`, `glued_model_iff`.
[GroupSemantics.lean](../Clafer/Compile/GroupSemantics.lean): `head_relation`,
`objects_interpret`, `satisfies_iff`, `finite_bounds`, `direct_child_iff`,
`empty_holds_iff`, `generated_group_iff`, `descendGroups_reduct`,
`glued_group_iff`, `descended_group_iff`, `descended_model_iff`.
Typedness proves endpoint representation; finite counts reuse
`DPGraph.Predicates.inRange_card` from the [finite-range bridge](../DPGraph/Predicates/Finite.lean).
The [inherited realization proofs](inherited-realization.md) separately establish
field realization and commuting map restrictions. Generic interpretations still require authored predicate meanings.

Covers:
- `req~clafer-compile-groups~1`
- `req~clafer-gluing-declarations~1`
- `req~clafer-gluing-formalcd~1`
- `req~predicate-multiplicity~1`

## Compiled and glued group witnesses

`proof~clafer-compile-group-examples~1`

[GroupExamples.lean](../Clafer/Compile/GroupExamples.lean): `emitted`,
`glued_emitted`, `compiled_count`, `glued_count`, `xor_compiled_glued`,
`numeric_compiled_glued`, `keywords_compiled_glued`, `inherited_new_child`,
`abstract_has_no_group`, `override_two`, `one_declaration_two_objects`,
`shared_target_occurrences`, `xor_individually_optional`, `xor_optional_head_maps`.
[EmptyGroupExamples.lean](../Clafer/Compile/EmptyGroupExamples.lean):
`inventory_empty`, `no_support_arrows`, `no_role_maps`, `accepted_iff`,
`empty_context_positive`, `inhabited_context_positive_rejected`,
`inhabited_zero_bounds`.
[GroupOverlapExamples.lean](../Clafer/Compile/GroupOverlapExamples.lean):
`overlap_typed`, `union_unchanged`, `two_head_paths_one_object`,
`compiled_overlap_xor`, `glued_overlap_xor`. These preserve raw group-union
semantics without claiming whole-model declaration disjointness, under explicit typed
configurations. They do not establish the complete
[inherited-family realization contract](inherited-realization.md).

Covers:
- `req~clafer-compile-groups~1`

## Selected inherited realization

`impl~clafer-inherited-realization~1`

[Realization](../Clafer/Semantics/Realization.lean) defines `Core`, `Core.ofInput`,
`Core.Selected`, `Abstracts`, `Groups`, `Satisfies`, `View`, `headView`, `derefView`
and `targetView`. The extension retains authored metadata and original link
identities. `Satisfies` also requires declaration disjointness while views retain
the original field objects. [The source contract](inherited-realization.md) records the selected
nested-abstractness, inheritance and group combinations (comparison decisions
[D2](resolved-ir-comparison.md#decision-d2)/[D4](resolved-ir-comparison.md#decision-d4)/[D6](resolved-ir-comparison.md#decision-d6)) and the complete scoped Appendix 6 inventory.

Covers:
- `req~clafer-inherited-realization~1`

`proof~clafer-inherited-realization~1`

In [Realization](../Clafer/Semantics/Realization.lean), `abstracts_generic`,
`explicit_leaf_empty`, `same_parent_fiber`, `view_cover`, `abstract_parent_cover`,
`disjoint_views`, `owner_agrees`, `deref_agrees`, `head_view_relation`,
`deref_view_relation`, `context_parents`, `context_references`,
`context_multiplicity`, `view_inverse`, `view_commutes`,
`target_links_injective`, `child_view_iff`,
`constraint_on_subtype`, `constraint_on_view` and `reaches` state the selected
object/link, scope and whole-model guarantees.
[RealizationCompatibility](../Clafer/Semantics/RealizationCompatibility.lean)
proves `guarded_groups`, `guarded_compatibility`,
`supported_input_compatibility` and `supported_checker_compatibility`. Selected
AST input derives flag agreement; no satisfaction equivalence is an assumption.

Covers:
- `req~clafer-inherited-realization~1`

## Generated realization declarations

`impl~clafer-compile-realization~1`

[Compile.Realization](../Clafer/Compile/Realization.lean) constructs `fanBinding`,
`coverFormula`, `disjointFormula`, `fieldFormula`, the complete `bank`, `glued`,
`interpretation` and `descend`. Abstract predicates use the built-in vocabulary;
new field groups reuse the child-object union from
[group compilation](group-compilation.md). The old bank and original
constraint occurrences are promoted with full bindings.

Covers:
- `req~clafer-compile-realization~1`

`proof~clafer-compile-realization~1`

[RealizationLocal](../Clafer/Semantics/RealizationLocal.lean) proves `local_model`
and `local_model_iff` for the selected broader input. In
[Compile.Realization](../Clafer/Compile/Realization.lean), `cover_iff`,
`disjoint_iff`, `declarations`, `cover_declared`, `disjoint_declared`,
`field_declared`, `defaults`, `glued_declarations`, `forget`, `descend_reduct`,
`field_iff`, `abstract_iff`, `bank_model_iff`, `correspondence` and `whole_model`
connect actual generated declarations and exact gluing to the independent
structural conditions, with authored expression meaning left as a parameter.
`whole_model` explicitly requires declaration disjointness on the model side;
the generated local/abstract/group bank does not entail this extra global clause.

Covers:
- `req~clafer-compile-realization~1`

<a id="inherited-appendix-f-acceptance-witnesses"></a>

## Inherited Appendix 6 acceptance witnesses

`impl~clafer-inherited-witnesses~1`

[Structural](../Clafer/Examples/Telematics/Structural.lean) constructs the structural AST,
source-order mapping, accepted Compile input and shared-object configuration.
The structural fixture retains the 26 printed declarations plus implicit root/int;
the separate twelve-conjunct inventory is in the source contract.

Covers:
- `req~clafer-inherited-witnesses~1`

`proof~clafer-inherited-witnesses~1`

[Structural](../Clafer/Examples/Telematics/Structural.lean) supplies `wf`, `selected`, `declaration_disjoint`, `satisfies`, `all_reach_root`, `compiled_glued_model`,
`inherited_version`, `inherited_options_and_displays`, `realized_xor_generated`
and `realized_xor_glued`.
[StructuralRejections](../Clafer/Examples/Telematics/StructuralRejections.lean) proves
`inconsistent_context_parent`, `inconsistent_context_reference`,
`shared_owner_rejected`, `duplicate_rejected`, `uncovered_rejected`,
`overlap_rejected`, `uncovered_generated_cover`, `overlap_generated_disjoint`,
`unrelated_fields_typed`, `unrelated_fields_disjoint_rejected`, `unrelated_fields_rejected`,
`two_options_rejected`, `generated_xor_rejects_two` and
`glued_xor_rejects_two`. No general expression satisfaction is claimed.

Covers:
- `req~clafer-inherited-witnesses~1`

## Resolved constraint denotation

`impl~clafer-constraint-denotation~1`

[Denotation.lean](../Clafer/Constraints/Denotation.lean) supplies `Environment`,
`Environment.Admissible`, `Expr.denote`, `Expr.Defined`, `Expr.Holds`,
`finiteCard` and `universal`; it re-exports `ambientRelation`, `relationalImage`
and `relationalJoin` from [DPGraph navigation](../DPGraph/Predicates/Navigation.lean).
`Expr.extent`, `Expr.implies`, `Expr.iff` and `Expr.ge` in
[Typing.lean](../Clafer/Constraints/Typing.lean) supply the resolved expansions.
[DenotationInvariance.lean](../Clafer/Constraints/DenotationInvariance.lean)
adds `LinkEquivalence` and `IntegerBinding.Coherent` for repeated resolved maps.

Covers:
- `req~clafer-constraint-environments~1`
- `req~clafer-constraint-denotation~1`
- `req~clafer-constraint-semantic-laws~1`

## Constructor and environment meaning proofs

`proof~clafer-constraint-denotation-laws~1`

[Denotation.lean](../Clafer/Constraints/Denotation.lean) proves
`Environment.push_admissible` and re-exports `image_span` and `join_span` from
[DPGraph navigation](../DPGraph/Predicates/Navigation.lean).
[CollectionMeaning.lean](../Clafer/Constraints/CollectionMeaning.lean) proves
`Expr.collection_meaning`, `Expr.cardinality_objects_defined`,
`Expr.cardinality_relation_defined`, `Expr.integerOf_singleton_defined` and
`Expr.all_defined`;
these derive class membership and local cardinality/domain obligations.
[DenotationLaws.lean](../Clafer/Constraints/DenotationLaws.lean) names every
constructor equation (`denote_boolean` through `denote_all`), finite/infinite
cardinality cases, `universal_empty`, `universal_defined`, `universal_undefined`, and the
`denotes_some`, `denotes_no`, `denotes_one`, `denotes_lone`, `denotes_implies`,
`denotes_iff` and `denotes_ge` equations.
[DenotationInvariance.lean](../Clafer/Constraints/DenotationInvariance.lean)
re-exports `ambientRelation_iso` from DPGraph and proves `LinkEquivalence.reduction`,
`repeated_map_denotation`, `Expr.denote_congr`, `Expr.environment_congr` and
`widening_path_irrelevant`.
[DenotationSupport.lean](../Clafer/Constraints/DenotationSupport.lean) defines
`Expr.extents` and `Expr.maps` and proves `Expr.denote_support_congr`: unused
extents and maps cannot affect the denotation. These observations do not
replace the full graph binding.
[DenotationRenaming.lean](../Clafer/Constraints/DenotationRenaming.lean)
proves `Expr.denote_rename` for arbitrary binder-display-name changes.
[DenotationDefined.lean](../Clafer/Constraints/DenotationDefined.lean)
proves `VersionNavigation.denotation_defined` and `comparison_agrees`, using
actual structural head/dereference bounds through `Model.operands_defined`.

Covers:
- `req~clafer-constraint-environments~1`
- `req~clafer-constraint-denotation~1`
- `req~clafer-constraint-semantic-laws~1`

<a id="manual-appendix-f-expression-implementation"></a>

## Manual Appendix 6 expression implementation

`impl~clafer-appendix-f-expressions~1`

[Expressions.lean](../Clafer/Examples/Telematics/Expressions.lean)
defines `c01`–`c12`, `inventory`, all explicit head/dereference/parent paths and
inheritance widenings. `support_resolved` and `inventory_resolved` check the
source IDs against `Telematics.Structural.ast`.
[ExpressionEnvironment.lean](../Clafer/Examples/Telematics/ExpressionEnvironment.lean) supplies `position`,
`objects`, `links`, `graphMap` and `model`, with the full integer realization
and the shared nonprimitive objects of [inherited realization](inherited-realization.md). `shared_extent`, `model_coherent`,
`objects_finite`, `closed_admissible` and `example_contexts` retain the identity, finite-extent and
environment obligations.
[Definedness.lean](../Clafer/Examples/Telematics/Definedness.lean) defines
`FiniteStructural`, projects the original version spans via `versionGraph` and
`versionModel`, and proves `c01_defined`–`c12_defined`. The c02 proof uses the
four actual version/server multiplicity obligations from [integer extraction](integer-extraction.md); the other bodies
use admissible environments and local finite structural extents.

Covers:
- `req~clafer-appendix-f-expressions~1`

## Constraint semantic witnesses

`proof~clafer-constraint-semantic-witnesses~1`

[DenotationExamples.lean](../Clafer/Constraints/DenotationExamples.lean)
checks `intersection_common`, `difference_other`,
`intersection_is_not_difference`, `no_empty`, `some_empty_fails`,
`joined_server`, `joined_server_not_reference_head`,
`universal_detects_counterexample`, `empty_universal`, `nested_shadowing`,
`shadow_does_not_capture`, `arithmetic_negative`, `greater_version`,
`equal_version`, `lower_version_fails`, `repeated_map_union`,
`infinite_integer_cardinality`, `head_count`, `reduced_target_count`,
`occurrence_links_distinct`, `occurrence_fiber_count`, `empty_extraction`,
`comparison_undefined`, `nonempty_undefined_quantifier` and
`empty_undefined_quantifier`.
These assertions inspect actual typed expressions and distinguish false from
undefined results.
[RepeatedDenotation.lean](../Clafer/Constraints/RepeatedDenotation.lean) checks
`distinct_occurrences`, `same_resolved_identity`, `same_links`,
`repeated_meaning` and `repeated_union` for different support edges denoting the
same original server-head span.
[ExpressionExamples.lean](../Clafer/Examples/Telematics/ExpressionExamples.lean)
checks `actual_c01`, `actual_c02_value`, greater/equal/lower numeric cases,
`no_cache`, `actual_c04`, `actual_c05`, `actual_c06_rejects_one_display`,
`actual_c07_rejects_one_display`, `actual_c08`–`actual_c12`, and the intermediate
relative/global/inherited paths.
[Definedness.lean](../Clafer/Examples/Telematics/Definedness.lean) proves
`c07_vacuity` on an absent ECU2 extent.
[Mutations.lean](../Clafer/Examples/Telematics/Mutations.lean) proves
`c06_accepts_two` and `c04_rejects_wrong_owner` on a typed moved-display
candidate. Its deliberately violated ECU2 bound is documented; no whole-model
satisfaction is inferred from those expression tests. The expression inventory
is separate from the [complete Appendix 6 satisfaction theorem](telematics.md).

Covers:
- `req~clafer-constraint-semantic-laws~1`
- `req~clafer-appendix-f-expressions~1`

## Derived source predicate meanings

`impl~clafer-constraint-predicates~1`

[Predicate.lean](../Clafer/Constraints/Predicate.lean) defines `Domains.close`,
`Constraint.Holds` and `predicateInterpretation`. Each occurrence keeps its body,
complete support and explicitly supplied domains; the integer realization is
fixed independently of truth. The meaning's existential packages admissibility
evidence for exactly the supplied graph map.

Covers:
- `req~clafer-constraint-predicates~1`

`proof~clafer-constraint-predicates~1`

`IntegerBinding.ext`, `predicate_meaning_iff` and `closed_constraint_iff` in
[Predicate.lean](../Clafer/Constraints/Predicate.lean) prove that admissibility
proof choices cannot change the interpretation and that the generated meaning
agrees with independent body denotation at every applicable context object.

Covers:
- `req~clafer-constraint-predicates~1`

## Selected semantic Compile correspondence

`impl~clafer-constraint-preservation~1`

[ConstraintMeaning.lean](../Clafer/Compile/ConstraintMeaning.lean) defines
`Admissible`, `supportModel`, `authored`, `interpretation` and `SourceHolds`.
It consumes the generated binding, preserves the source occurrence symbol and
uses the body-derived interpretation in the existing generated realization bank.

Covers:
- `req~clafer-constraint-preservation~1`

`proof~clafer-constraint-preservation~1`

In [ConstraintMeaning.lean](../Clafer/Compile/ConstraintMeaning.lean),
`vertex_same_id`, `boundArrow_same_id`, `vertex_integer`, `links_of_identity`,
`support_coherent`, `arity_binding` and `context_binding` account for resolved
identities and complete arity interpretation. `admissible_of_local` extracts
inclusion meanings from generated local declarations. `constraint_iff`,
`compiled_model_iff`, `glued_constraint_iff`, `glued_constraint_declared`, `authored_iff` and
`whole_model` prove the selected satisfaction correspondence using the actual
label and complete generated bank. The latter composes
`Compile.Realization.whole_model` and retains its selected structural conditions,
including explicit declaration disjointness;
it does not infer reflection from generic model reduct.
[VersionPreservation.lean](../Clafer/Examples/VersionPreservation.lean) specializes
`generated_version_iff` and `generated_operands_defined` to the actual compiled
and glued c02 attachment, deriving the interpreter’s scalar hypotheses from
`VersionCompilation.versionModel` and emitted local declarations.

Covers:
- `req~clafer-constraint-preservation~1`

## Constraint predicate acceptance boundaries

`impl~clafer-constraint-preservation-witnesses~1`

[ConstraintPredicates.lean](../Clafer/Examples/ConstraintPredicates.lean) constructs
body-derived predicate interpretations and full identity arity bindings on the
existing Appendix 6 graph environments. `liveDomain` and `emptyDomain` exercise
external binders without an arbitrary interpretation parameter. The
[support audit](constraint-preservation.md#appendix-f-support-audit) records real
navigation and the finite-primitive/full-integer fixture boundary.

Covers:
- `req~clafer-constraint-preservation-witnesses~1`

`proof~clafer-constraint-preservation-witnesses~1`

In [ConstraintPredicates.lean](../Clafer/Examples/ConstraintPredicates.lean),
`satisfies_iff`, `display_count_rejected`, `display_count_accepted`,
`changed_count_body_accepted`, `server_parent_accepted`, `wrong_server_parent_rejected`,
`version_value_at_every_display`, `version_predicate_iff`, `version_order_sensitive`,
`external_domains_sensitive`, `wrong_context_rejected` and
`wrong_context_body_rejected` check semantic sensitivity.
`inventory_positive`, `inventory_total_args` and `inventory_observes_map` audit every body;
`structural_success_does_not_discharge_constraints` separates MCS validity from
interpreted truth. Existing integer/denotation witnesses retain extraction failure,
repeated-occurrence and finite-cardinality boundaries.
[ConstraintBinding.lean](../Clafer/Examples/ConstraintBinding.lean) proves
`identical_arrow_arguments`, `complete_binding_accepted`, `wrong_binding_rejected`
and `compiled_isolated_identity`: changing an isolated repeated class occurrence
invalidates the predicate meaning despite preserving every arrow argument.

Covers:
- `req~clafer-constraint-preservation-witnesses~1`

## Representative model integration

`impl~clafer-representative-integration~1`

[Integration.lean](../Clafer/Examples/Integration.lean) defines `Small.glued`,
`Small.label` and the concrete inclusion slot `Small.inheritedHead`, reusing
`Compile.Examples.input`, `Compile.GroupExamples.input` and `Examples.Telematics.Structural.input`.
[VersionCompilation.lean](../Clafer/Examples/VersionCompilation.lean) defines
`ast`, `input`, `q`, `glued`, `navigation`, `LocalHolds` and `versionModel` for the
mandatory Appendix 6 comparison. These examples use the existing Compile/group
and inherited realization interfaces without changing their contracts.

Covers:
- `req~clafer-representative-integration~1`

`proof~clafer-representative-integration~1`

In [Integration.lean](../Clafer/Examples/Integration.lean),
`Small.compilation_gluing_valid`, `exact_declarations`, `nested_names_and_identity`,
`nesting_incidence`, `shared_target_distinct_maps`, `inheritance_declared`,
`typed_attachments` and `repeated_binding_after_gluing` prove the concrete
structural connections. `Xor.declarations` proves emitted membership on both sides.
`Xor.optional_declarations` checks the actual emitted
optional multiplicities at zero/one/two objects; `Xor.boundaries` proves one
passes and zero/two fail separately before and after gluing. `TelematicsStructural.source_ids`,
`exact_declarations`, `structural_model` and `version_and_server` account for the
inherited declaration projection and its nonempty structural model.

In [VersionCompilation.lean](../Clafer/Examples/VersionCompilation.lean),
`wf`, `support_resolved`, `constraint_typed`, `output_valid`, `attachment`, `full_binding` and
`mandatory_bounds` check resolved typed attachment and preservation.
`local_of_model` extracts the actual generated local predicates from an interpreted
glued model; `versionModel` derives the four multiplicities and inclusions from
those predicates. `operands_defined` and `comparison_defined` apply the delivered
integer-navigation results, with primitive domain equality explicit. They do
not assume or prove c02's truth or a general expression interpreter.

Covers:
- `req~clafer-representative-integration~1`

`impl~clafer-representative-coverage~1`

The [coverage matrix](representative-models.md) accounts for features, source
locators, all d01–d26 declarations and c01–c12 conjuncts, assumptions and remaining
obligations discharged separately by the [complete Appendix 6 model](telematics.md),
[constraint denotation](constraint-denotation.md) and
[preservation bridge](constraint-preservation.md). It links the authoritative inventory rather than
redefining source semantics. The full structural projection and separate c02
fragment retain distinct representation and satisfaction boundaries.

Covers:
- `req~clafer-representative-coverage~1`

`proof~clafer-representative-coverage~1`

The integration proofs above and the existing
[Structural.lean](../Clafer/Examples/Telematics/Structural.lean) `source_order`, `satisfies`,
`compiled_glued_model`, `inherited_version`, `inherited_options_and_displays`,
`realized_xor_generated` and `realized_xor_glued` substantiate the structural rows.
[IntegerExamples.lean](../Clafer/Constraints/IntegerExamples.lean)
`comparison_value`, `greater`, `equal`, `lower`, `empty_server`, `multiple_server`
and `wrong_domain_server` substantiate the partial-comparison row.
[FormalCD examples](../FormalCD/Telematics/Examples.lean) `model_iff` and
[SelfDescription.lean](../FormalCD/SelfDescription.lean) `bounded_self_description`
remain separate Figure 21 results. Public import tests and the discovered-module
build/audit cover the layer boundary. The coverage table itself is a reviewable
accounting document, not a Lean theorem of source completeness or a substitute
for the omitted constraints' proofs.

Covers:
- `req~clafer-representative-coverage~1`

## Resolved compiler import and capture

`impl~clafer-resolved-import~1`

[Import.lean](../Clafer/Verification/Import.lean) supplies `Row`, `Input.normalize`,
`Represents`, `bindingChecks`, `admit`, `UidCandidate.translate` and the UID
inventory. [ImportMain.lean](../Clafer/Verification/ImportMain.lean) provides the
native JSON boundary. [The external decoder](../scripts/verification/protocol.py)
checks pinned IR/receipt schemas, identities, metadata and the guarded fragment;
[capture.py](../scripts/verification/capture.py) connects it to Lean admission.
The [import guide](resolved-import.md) states the unproved byte-decoding boundary.

Covers:
- `req~clafer-resolved-import~1`

### Imported representation and semantic correspondence

`proof~clafer-import-correspondence~1`

[ImportProofs.lean](../Clafer/Verification/ImportProofs.lean) proves
`representation_unique`, `normalization_correspondence`, `imported_check_correct`,
`imported_verify_correct`, `lookup_sound`, `classId_represents` and
`translate_represents`. `Accepted.uid_identity` in Import.lean retains distinct
UIDs independently of repeated names; `Accepted.wellFormed` and
`Accepted.supported` derive the semantic hypotheses from checked data.
`CandidateRepresents` relates every original candidate row, object label and
endpoint to its finite-ID translation, retaining reference occurrences.
These results compose with the independent [structural meaning and
compiled-bank/span interpretation](structural-checker.md). They do not prove the external parser or
upstream compiler transformations correct.

Covers:
- `req~clafer-resolved-import~1`

### Same-generation capture implementation

`impl~clafer-compiler-capture~1`

[Export.hs](../scripts/verification/Export.hs) performs the source/token audit,
analysis and paired generation in one compiler environment. The
[builder](../scripts/verification/build.py) checks pinned original sources and
records build identities. [protocol.py](../scripts/verification/protocol.py)
checks consumed-map projection/registry, backend ownership/processing, options,
explicit bounds and artifact hashes. [capture.py](../scripts/verification/capture.py)
retains source and original JSON/Alloy with the common manifest and receipt.
[runtime.py](../scripts/verification/runtime.py) prepares or checks that exporter
for the shared validation command, retaining its build outside captured source.

Covers:
- `req~clafer-compiler-capture~1`

### Import and capture acceptance assertions

`utest~clafer-resolved-import~1`

[Python tests](../tests/test_resolved_import.py) execute actual pinned captures,
replay the emitted bundles through Lean admission and mutate schemas, bindings,
cards, source constructors, options and receipts. They check live source spans
and malformed position metadata, escaped/colliding apostrophe UIDs, keyword and
numeric defaults, comment layout, unreachable concrete groups, old-version
rejection and the saved IR's equality with a fresh export. [Lean tests](../tests/resolved_import.lean)
exercise kernel/native admission and identity witnesses in
[ImportExamples.lean](../Clafer/Verification/ImportExamples.lean), including
repeated names, reference modes and repeated-target occurrences.
[Runtime setup tests](../tests/test_capture_runtime.py) check fresh provisioning,
cache invalidation, explicit producer settings, hash failures and child-process
environment/status propagation. [Runner tests](../tests/test_check_script.py)
check setup ordering and failure propagation through the shared validation gates.

Covers:
- `req~clafer-resolved-import~1`
- `req~clafer-compiler-capture~1`

<a id="complete-appendix-f-resolved-model"></a>

## Complete Appendix 6 resolved model

`impl~clafer-appendix-f-complete~1`

[Input](../Clafer/Examples/Telematics/Input.lean) defines `decl`, `attachments`,
`ast`, `input`, `occurrence`, `core` and the unrestricted primitive head.
[Configuration](../Clafer/Examples/Telematics/Configuration.lean) defines
`integers`, `heads`, `ownership`, `targets` and `config` for the complete selected
model. [Compiled](../Clafer/Examples/Telematics/Compiled.lean) fixes
`domains`, `compiledSupport` and the body-derived `interpretation` of the actual
compiled/glued bank. [The source contract](telematics.md) distinguishes this
fixture from earlier structural and expression subsets.

Covers:
- `req~clafer-appendix-f-complete~1`

<a id="complete-appendix-f-model-proofs"></a>

## Complete Appendix 6 model proofs

`proof~clafer-appendix-f-complete~1`

[Input](../Clafer/Examples/Telematics/Input.lean): `wf`, `inventory_input`,
`sourceIndex_occurrence`, `occurrence_sourceIndex`, `occurrence_body`,
`occurrence_owner`, `mcs_valid`, `gluing_compatible`, `effective_defaults`,
`formalcd_valid`, `exact_declarations` and `selected`.
[Configuration](../Clafer/Examples/Telematics/Configuration.lean):
`integer_extent`, `primitive_root_containment`, `nonprimitive_finite`,
`typed`, `rooted`, `inherits`, `parents_hold`, `references_hold`, `keys`,
`multiplicities`, `abstracts`, `groups`, `declaration_disjoint` and `structural_satisfaction`.
[Satisfaction](../Clafer/Examples/Telematics/Satisfaction.lean):
`c01_all`, `c02_all`, `c02_defined`, `c03_all`, `c04_all`,
`c05_holds` through `c12_holds`.
[Compiled](../Clafer/Examples/Telematics/Compiled.lean): `admissible`,
`compiled_objects`, `compiled_relations`, `source_holds`,
`compiled_glued_model` and `nonempty_configuration`.
The final concrete theorem discharges every hypothesis of the selected semantic
bridge for this exact input/configuration and its canonical descent. Manual
source elaboration remains a review boundary.

Covers:
- `req~clafer-appendix-f-complete~1`

<a id="complete-appendix-f-rejection-candidates"></a>

## Complete Appendix 6 rejection candidates

`impl~clafer-appendix-f-rejections~1`

[Rejections](../Clafer/Examples/Telematics/Rejections.lean) reuses the
existing count, version and wrong-owner environments for the actual full input's
attached symbols. `Probe.model` supplies finite navigation witnesses for cache,
fixed and the product-line equivalences. `xorConfig` supplies zero/one/two child
candidates for the full model's actual channel group. These are focused negative
candidates and may violate several obligations simultaneously.

Covers:
- `req~clafer-appendix-f-rejections~1`

## External bounded comparison execution

`impl~clafer-bounded-comparison~1`

[comparison.py](../scripts/verification/comparison.py) reuses `import_bundle`
and `ImportMain.execute` for checker admission/verdicts. Its `command`,
`command_bounds`, `compare` and `category` preserve generated facts, explicit
manual bounds and both-direction outcomes. [alloy_runtime.py](../scripts/verification/alloy_runtime.py)
checks distribution/build identities and limits; [AlloyBridge.java](../scripts/verification/AlloyBridge.java)
checks resolved scopes, staticness, symbols, auxiliary inventory, arithmetic AST
and fixed solver options before executing bundled SAT4J. `ImportMain.failedPredicates`
in [ImportMain.lean](../Clafer/Verification/ImportMain.lean) names failed existing
checker conjuncts; it does not change `check` or claim per-instance proof certificates.

Covers:
- `req~clafer-bounded-comparison~1`

## External candidate representation

`impl~clafer-alloy-representation~1`

[relation.py](../scripts/verification/relation.py) defines `inventory`, `pin`,
`decode`, `isomorphism`, `occurrences` and `range_argument`, implementing the
[reviewed relation obligations](bounded-comparison.md). SAT extents and fields
are extracted by `AlloyBridge.execute` and checked against the original candidate.
The object/link-bijection argument and external trust boundary are documented;
this is an external implementation artifact, not an executable Lean proof.

Covers:
- `req~clafer-alloy-representation~1`

## Bounded enumeration and artifacts

`impl~clafer-comparison-replay~1`

[candidates.py](../scripts/verification/candidates.py) supplies complete labelled
table enumeration for its stated domain, seeded generation, strict deletion
shrinking and search accounting. [search.py](../scripts/verification/search.py)
exposes both search modes. `comparison.compare`/`replay` retain raw-byte hashes,
source identities, verdicts and replay inputs. `source_commit` records an optional
checkout commit without parent discovery; `source_snapshot` and replay retain
mandatory source byte matching even without Git metadata. Git failures remain
execution diagnostics. [mutations.py](../scripts/verification/mutations.py)
implements the three explicit injected sensitivity defects. The normal Python
test discovery runs these comparisons; CI provisions and retains external evidence.

Covers:
- `req~clafer-comparison-replay~1`

## Bounded comparison assertions

`utest~clafer-bounded-comparison~1`

[test_bounded_comparison.py](../tests/test_bounded_comparison.py) executes actual
paired compiler captures, Lean checks, pinned solver calls, witness fidelity and
replay. Its numbered live tests cover repeated-target sets/bags, local/group bounds,
nesting, abstract cover/shared inheritance, rejected unrelated overlap with
`agree_violates`, accepted distinct heads, nested overlap rejection, malformed/root inputs,
cyclic and nonfunctional tables, unpinned witnesses, the fixed exhaustive domain,
seeded candidates, all three shrunk mutations and pin/arithmetic/execution failures.
`test_10_apostrophe_names_compare_and_replay` checks an exact nonempty candidate
with escaped and colliding UIDs against Alloy and Lean, then replays it.
`test_original_parser_failure_retains_stage` injects malformed Alloy directly
into the bridge and checks the parser-stage error with no solver outcome.

`RelationTests` checks generator counts, seeds, interruption and result algebra.
It also checks exact predicate-name collisions and missing/duplicate original
commands. `LiveComparisonTests.test_13_predicate_substring_comparison_and_replay`
compiles `predicate_name.cfr` with the pinned compiler and checks empty and
singleton candidates plus replay against the actual backend, including witness
fidelity, for the generated signature `c0_ib_candidate`.

`SourceIdentityTests` exercises snapshot comparison/replay with isolated capture
admission, actual checkout/worktree Git metadata, parent/environment isolation,
corrupt metadata/execution errors, source/input byte tampering and runtime mismatch.
`LiveComparisonTests.test_12_source_snapshot_comparison_and_replay` checks a
complete real comparison and replay with identical hashed sources relocated to
a tree without Git metadata, retained runtime identities and tampering rejection.

Existing [test_resolved_import.py](../tests/test_resolved_import.py) retains E1/E7–E9/
E12–E13 strict source/IR/receipt/constructor/option rejection assertions; these
complement the relation-specific E1–E14 comparisons. Mutation assertions are
explicitly about injected faults. Full validation and independent review remain
separate evidence; this trace item does not certify their completion.

Covers:
- `req~clafer-bounded-comparison~1`
- `req~clafer-alloy-representation~1`
- `req~clafer-comparison-replay~1`

## Small model walkthrough

`impl~lean-walkthrough~1`

[Walkthrough.lean](../Clafer/Examples/Walkthrough.lean): `model` encodes the
synthetic root, phone and optional camera; `configuration` supplies finite
objects and containment for a given camera count. The
[getting-started guide](getting-started.md) explains the manually resolved
boundary, declaration/object IDs and the connection to semantic statements.

Covers:
- `req~lean-walkthrough~1`

## Walkthrough satisfaction and rejection

`proof~lean-walkthrough~1`

[Walkthrough.lean](../Clafer/Examples/Walkthrough.lean): `model_valid` and
`model_supported` discharge the input conditions. `accepts_no_camera`,
`accepts_one_camera` and `rejects_two_cameras` use kernel reduction.
`no_camera_satisfies`, `one_camera_satisfies` and `two_cameras_violate` apply
`Verification.check_correct` to the independent structural semantics.

Covers:
- `req~lean-walkthrough~1`

<a id="complete-appendix-f-negative-sensitivity"></a>

## Complete Appendix 6 negative sensitivity

`proof~clafer-appendix-f-rejections~1`

[Rejections](../Clafer/Examples/Telematics/Rejections.lean):
`symbol_rejected` and `generated_rejected` identify the exact attached symbol
and transport its failure through a matching complete arity reduct.
`wrong_display_count`, `forbidden_cache`, `wrong_server_parent` and
`lower_display_version` reject the required full-model body obligations.
`missing_fixed`, `missing_dual`, `conflicting_small_options`,
`conflicting_large_options`, `c07_wrong_display_count` and `c07_vacuity`
preserve operator sensitivity. `xor_counts`, `xor_generated_rejected`,
`xor_glued_rejected` and `xor_declared` connect both xor boundaries to the
actual generated/glued channel group. No independent isolation of coupled
failures is asserted.

Covers:
- `req~clafer-appendix-f-rejections~1`

## Semantic dependency boundaries

`itest~clafer-semantic-dependencies~1`

[semantic_dependencies.lean](../tests/semantic_dependencies.lean) imports the
structural and expression meanings and rejects transitive Compile, Verification
and Telematics modules. [group_dependencies.lean](../tests/group_dependencies.lean)
checks that group mathematics and the erasure adapter remain available without
importing the finite checker. The shared check discovers and compiles both tests
with warnings as errors.

Covers:
- `req~clafer-effective-core~1`
- `req~clafer-compile-groups~1`
- `req~clafer-integer-extraction~1`
