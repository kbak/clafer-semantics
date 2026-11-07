# Constraint meaning through Compile and gluing

This selected bridge connects the [independent denotation](constraint-denotation.md)
to the actual predicates emitted by [Compile](compile.md), then composes it with
the [inherited structural realization](inherited-realization.md). Its source is
SoSyM §6.2.2–5, B.4 Definition 10/B.5, Appendix 4 (D.4) and Appendices 5–6, with the accepted
[corrections](sosym-errata.md). It concerns resolved typed inputs, not a textual
resolver or a universal compiler-correctness claim.

## Derived predicate meanings

`Constraints.predicateInterpretation` fixes the constraint family, explicit
external-binder `Domains` and one integer realization. Each occurrence's meaning
requires an admissible interpretation of its **entire** arity graph and evaluates
its typed body at every object of the declared context. Equal resolved class IDs
share object sets; equal map owner/role identities share original links and
endpoints. Integer annotations select the complete realized integer domain.
Display names select none of these identities.

`Domains.close` introduces outer binders before inner binders using the core
universal constructor. Domains are evaluated before their binders enter scope.
The existence of some domains in `Constraint.Input` does not select their
meaning: semantic clients supply the actual typed domain expressions explicitly.
Empty domains have universal vacuity; undefined domains and undefined bodies
on applicable objects fail satisfaction. Closed Appendix 6 bodies use `.nil`.
No client supplies an arbitrary set of satisfying diagrams or a source/target
truth equivalence.

## Binding and transport assumptions

`Compile.ConstraintMeaning.supportModel` restricts a role-graph interpretation
along the generated `Compile.binding`. Its admissibility hypotheses are literal
inclusion for generated inclusion slots and equality of actual primitive integer
class extents with the fixed realization. `admissible_of_local` derives the
inclusion hypotheses from the generated local predicates; primitive-domain
realization is an additional model condition. Integer extraction retains the
independent singleton/domain obligations of [integer extraction](integer-extraction.md). Neither inclusion nor scalar
conversion is inferred from names, MCS validity or truth of the source body.

`arity_binding`, `context_binding`, `vertex_same_id`, `boundArrow_same_id` and
`support_coherent` account for the full arity, owner context and resolved maps.
Isolated vertices and repeated occurrences remain present. `constraint_iff`
relates the body-derived interpretation of the actual generated formula to the
independent source denotation. Literal bag-key equality cannot replace this
complete binding agreement.

`glued_constraint_iff` evaluates the actual promoted formula after translation
by `groupLabel`. Its source candidate is exactly that target candidate's reduct.
`glued_constraint_declared` establishes actual membership in the generated image.
`whole_model` composes the result with `Compile.Realization.whole_model`: for a
selected inherited core and an admissible shared-object configuration, typedness,
root conditions, declaration disjointness and satisfaction of its canonically
descended glued diagram are equivalent to extended structural satisfaction and truth of every attached source
constraint. The local, group, inclusion and abstract obligations and complete
declaration image come from the existing generation proofs. The interpretation
substituted for their authored-meaning parameter is fixed by the bodies.

This equivalence uses the exact bank and canonical descent of the selected
configuration. Generic B.5 contravariant reduct alone supplies only its forward
model restriction. Arbitrary added target declarations, arbitrary target models,
or noninjective generic gluing do not inherit unrestricted reflection.
Effective-default completeness remains derived for the generated bank. The
original MCS retains its total-args and literal-key proofs; the larger raw
group/abstract bank retains its documented separate discipline.

<a id="appendix-f-support-audit"></a>

## Appendix 6 support audit

The existing [c01–c12 inventory](inherited-realization.md#constraint-scope-handoff)
uses the complete 28-vertex/34-map graph. Its maps resolve against the complete
structural AST, and each body observes at least one actual navigation map.
`inventory_positive`, `inventory_total_args` and `inventory_observes_map` check
these facts; no extra
support is introduced to satisfy Compile's positive-map condition.

| Conjuncts | Source navigation establishing nonempty map support |
| --- | --- |
| c01 | options.size.small, options.cache and cache.size.fixed heads |
| c02 | version/server heads and dereferences, with actual inheritance widening |
| c03 | inherited display.options.cache heads |
| c04 | display.server head/dereference and plaDisplay parent |
| c05 | telematics.channel.dual heads; ECU2 is a global extent |
| c06–c07 | extraDisplay and plaDisplay heads; count heads before dereferencing |
| c08–c09 | local size heads and inherited options navigation from global plaECU |
| c10–c12 | global telematics followed by the selected child heads |

The existing finite structural witness's primitive placeholder has a `1..1`
head bound. It cannot simultaneously denote all mathematical integers: every
integer object must have the unique root as parent, contradicting that finite
head bound. The separate expression environment therefore is not a whole model
of that unchanged fixture.

SoSyM §5.3.5 PDF p.15 identifies a primitive head with
its value domain. A complete integer-bearing fixture must give that primitive
head an explicit unrestricted bound and the corresponding root containment,
both already admitted by the resolved-input contract. This does not change
version/server `1..1` bounds, finite counted nonprimitive collections, or the
[guarded structural checker](structural-checker.md). The [complete constraint-bearing fixture](telematics.md) applies this conditional
bridge with the unrestricted primitive bound, actual root containment, two
displays per ECU and all twelve bodies proved simultaneously.

The [predicate examples](../Clafer/Examples/ConstraintPredicates.lean) distinguish
version order, display counts, wrong server/parent navigation, external domains
and inadmissible context objects. A changed typed body changes satisfaction on
the same support diagram. Structural compilation validity is separately proved
and does not discharge these semantic checks. See the
[predicate meaning and proofs](../Clafer/Constraints/Predicate.lean).
