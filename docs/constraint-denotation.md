# Resolved constraint denotation

The constraint denotation interprets the typed core
of SoSyM Appendix 4/Figure 28 and the manual Appendix 6 expansions, as specified
in the [constraint-meaning issue](https://github.com/kbak/clafer-semantics/issues/68). The
[product intent](intent.md), [source map](sources.md#appendix-d-rule-dispositions-q3),
[integer bridge](integer-extraction.md), and [inherited inventory](inherited-realization.md)
remain authoritative for their respective boundaries. The [selected Compile/gluing bridge](constraint-preservation.md) derives predicate
meanings from these equations; the [combined full-model result](telematics.md) applies them to one complete fixture.

## Values and environments

`IntegerBinding` supplies the entire support graph's class sets and spans,
shared resolved class identities, inheritance inclusions and a realization of all
mathematical integers. `IntegerBinding.Coherent` additionally requires repeated
resolved map owners/roles to have bijective link identities with identical ambient
endpoints. Display names do not determine either class or map identity.
`Environment` records one context object and one object for each lexical position.
Its admissibility predicate requires the objects to belong to their declared
classes. Pushing a binder preserves `this`, introduces one singleton variable,
and retains access to outer variables. A quantifier evaluates its domain before
pushing the binder. Names may shadow; fresh binder IDs remain the syntax contract.

`Expr.extent` selects a resolved global class, including a parentless abstract
family such as plaECU. It does not invent a synthetic-root containment map.
Widening preserves the ambient objects and changes only their typing evidence;
`IntegerBinding.widen_subset` supplies the class-inclusion obligation.

## Independent equations and partiality

`Expr.denote` is a noncomputable mathematical function. Boolean values are
propositions, integers are mathematical `Int`, unary collections are sets of
objects and binary collections are sets of endpoint pairs. `Option` distinguishes
an undefined operation from a defined false proposition. There is no executable
search evaluator or solver in this extension.

* Conjunction, negation, equality, integer less-than, addition and subtraction
  have their ordinary mathematical meanings. Equality compares values of the
  same core sort, including whole sets/relations.
* Union, difference and **ordinary intersection** act on both collection shapes
  ([Q3](sources.md#appendix-d-rule-dispositions-q3)). Subsetting is set inclusion. Unary image and binary composition use an
  existential common middle object.
* Map expressions explicitly reduce the original spans to endpoint relations.
  `join_span` proves that composing those relations agrees with reducing the [Q1](sources.md#span-composition-q1-research-for-4)
  composite. The original link carriers remain in the model.
* `this` and variables denote singletons; global extents denote the whole class.
  Widening leaves the underlying collection unchanged.
* Universal quantification asserts the body for every domain object. The empty
  domain yields true. Every body on a domain member must be defined; bodies on
  objects outside the domain impose no obligation.
* Cardinality is defined only when the particular operand set is finite. Its
  value is the natural cardinality embedded in `Int`; an infinite operand is
  undefined. This does not impose a finite ambient universe or finite integer
  domain. The no/one/lone/some helpers retain these local finite-collection bounds.
* `integerOf` uses [exact singleton extraction](integer-extraction.md). Empty, multiple-object and
  off-domain results are undefined. The bridge supplies no arbitrary integer.

Partial operations propagate undefined operands. On admissible finite operands,
implication is `not (p and not q)`, equivalence is both implications, and `a >= b`
is `not (a < b)`. These equations preserve implication vacuity. Appendix 6 c02
has mandatory server/version navigation and receives no Figure 21 guard.
Its singleton obligations follow from the actual head bounds, functional
references and inherited class membership, independently of whether the
comparison holds.

## Empty collections

The adopted [empty-set extension](https://github.com/kbak/clafer-semantics/issues/134)
adds `Expr.empty` at any unary or binary collection shape. It denotes `Option.some ∅`;
`Option.none` continues to mean undefined. The surface `noclafer` has bottom element
type and arity one. A resolved type annotation instantiates that bottom at a
chosen element class without creating a declaration, inheritance edge, or value
dependency on the class extent. Binary empties retain both endpoint annotations.
Boolean and scalar integer types are separate; `integerOf` on an empty integer
collection is undefined.

`Empty.lean` proves count zero, true no/lone, false some/one, union and difference
identities, intersection/subset/navigation laws and vacuous universal quantification.
Laws that discard another operand retain its definedness premise. Empty expressions
observe no extents or maps. General environment, support and renaming invariance
cover the new constructor. This extension leaves structural Compile's positive-map
support requirement unchanged; generic constraint denotation permits constant-only
bodies. General source conditionals remain outside this core.

`noclafer` is reserved in the source language to avoid taking the useful existing
model name `none`. Alloy generation still uses its native `none` spelling. The
name complements the universal-collection spelling `clafer`; adding a universal
source literal is a separate frontend concern.

## Occurrence counts and inherited navigation

Reference heads are objects with identity. A collection of two different heads
has cardinality two even when both dereference to one target. A set of those
targets has cardinality one. Reference-head counts, reduced-relation counts and
link counts are separate operations; reducing a span never changes the original
link carrier. The structural `headFiberEquiv` and `compositeFiber` results retain
head/composite link counts under ownership and functional reference assumptions.

The expression inventory uses the source IDs d01–d26, root=0 and int=27 from
[inherited realization](inherited-realization.md). `Telematics.Expressions.inventory_resolved` checks each support against its
actual AST. The twelve bodies retain the contexts and navigation spelled out in
the [constraint inventory](inherited-realization.md#constraint-scope-handoff).
In particular, c01 visits fixed through the cache.size head before integer
dereferencing; c03 follows inherited options to cache; c04 compares the server
value with the actual owning parent after widening both to ECU; c06/c07 count
plaDisplay heads; c08/c09 start at the whole plaECU extent. The distinct declarations
named size and options retain their distinct IDs. c10–c12 insert implicit some.

The expression environments reuse the nonprimitive objects and links of the
[inherited realization](inherited-realization.md), preserving their identities.
For numeric interpretation its finite primitive placeholder is replaced by the
complete integer realization. This environment construction does not assert
whole-model satisfaction of the compiled primitive declaration or establish
the [constraint-preservation bridge](constraint-preservation.md).
The [finite structural checker](structural-checker.md) retains its guarded domain.

## Proof boundaries

Constructor equations, lexical/environment invariance, repeated-map coherence,
link relabeling, widening-path irrelevance and numeric definedness are stated in
separate Lean modules. `Expr.denote_support_congr` restricts required agreement
to observed extents/maps, proving independence from unused support entries. It
does not discard any part of the full structural binding. `c01_defined`–`c12_defined`
derive definedness from admitted context objects, finite structural extents and
the four version/server map bounds, with no finiteness requirement on int.
The [trace inventory](clafer-trace.md#resolved-constraint-denotation)
links their actual declarations and sensitive positive/negative witnesses.
No textual resolver, automatic coercion insertion, higher-arity relation,
string arithmetic, tuple binder or evaluator correctness is claimed. The separate
[preservation contract](constraint-preservation.md) states the selected
Compile/gluing result and its admissible-model assumptions.
