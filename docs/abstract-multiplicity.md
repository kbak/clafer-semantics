# Aggregate abstract multiplicity

The **abstract-multiplicity/v1** extension gives authored bounds on abstract
clafers an aggregate meaning. It composes with the behavioral profile through
`Clafer.Behavioral.AbstractMultiplicity`; the historical static checker, importer
and `Structural.Core` APIs retain their recorded meanings. The
[accepted decision](https://github.com/kbak/clafer-semantics/issues/193) and
[source disposition](sources.md#aggregate-abstract-multiplicity) distinguish this
language extension from the papers and the pinned Haskell comparison profile.

## Independent static meaning

[`Semantics.AbstractMultiplicity`](../Clafer/Semantics/AbstractMultiplicity.lean)
defines `Global`, `PerParent` and `Holds` on mathematical configurations.
For an authored abstract declaration `a` with interval `l..u`:

- If `a` has no declared parent, `Global` bounds the entire inherited head of
  `a`, across all actual parents and all containment depths.
- If `a` has declared parent `p`, `PerParent` bounds the containment fiber of
  `a` separately for each live identity in the inherited head of `p`.

Structural validity supplies complete inherited heads, abstract coverage and
consistent actual ownership. The count obligation does not repair invalid raw
configurations or replace those obligations. Nested bounds reuse exactly
`Configuration.Multiplicities`; a parentless global count creates neither a
root containment map nor a reference key. Ordinary concrete and group bounds
keep their existing meanings.

Count head identities once. An identity present in several views along a super
chain remains one member of the abstract head. Distinct reference heads count
separately even when they reference the same target. A parentless abstract set
reference acquires no global target-uniqueness condition.

Omitted abstract multiplicity is `0..*`. The generic `InRange` meaning uses a
lower-bound injection into the counted type and, for finite upper bounds, an
injection out to the upper finite type. It covers zero, optional, exact and
finite intervals, empty extents and infinite extents with unbounded upper
limits. No finite ambient universe is assumed. An empty global extent violates
any positive lower bound. With no live declared parents, a nested bound has no
obligation; its positive lower bound does not require a parent to exist.

## Source provenance and temporal composition

`AbstractMultiplicity.Core` retains the original structural core and a separate
`authoredMultiplicity` field. The frontend supplies these source annotations;
optimizer-derived global cards, unused-abstract zeroing and solver scopes cannot
supply them. `Core.source` uses the authored/default range for authored abstracts,
while preserving ordinary effective bounds, groups, super/parent edges and
reference metadata. Its raw heads, containment and references are unchanged.
`owner_iff`, `deref_iff`, `keys_iff` and `groups_iff` preserve inherited
reference lookup, reference observations, keys and group obligations. The
source core's well-formedness checks the resulting ranges, including bounds
on parentless declarations.

`At` applies the independent static obligation at a state. `Always` quantifies
over every natural-number time; `Valid` combines this with structural validity
of the source core, and `Admissible` also requires well-formedness. The
`model` constructor composes counts with the existing modifiers and attached
constraints on the same trace. Existing formula and initializer obligations do
not substitute for these counts. The separate
[explicit initializer-clock contract](behavioral-initializers.md) admits bounded
parentless `:=` only with an authored clock choice and composes its meaning with
this every-state count obligation.

`valid_iff_global` proves that source-core structural validity already enforces
nested abstract bounds: only the parentless aggregate obligations are additional.
`snapshot_iff` transports the whole count obligation to the live carrier by
head and containment-fiber equivalences. `constant_iff` reduces every-state
counts to static counts under explicit equality of all head and containment
observations. It makes no claim that checking time zero suffices for changing
traces or that arbitrary configurations have a valid trace embedding.

## Cardinalities and specialization

`global_fin_iff` and `perParent_fin_iff` reduce the independent meaning to
ordinary lower/upper numeric cardinality constraints, given exact finite
representations of the counted head or each live parent's fiber. `global_card`
and `perParent_card` provide the corresponding `Fintype` forms. These premises
are local: other heads and the ambient identity pool may remain infinite.
A backend scope limits a search representation; it neither supplies a source
lower bound nor waives a source upper bound.

An aggregate interval is not a per-subclafer interval-refinement check.
For example, two sibling realizations with four heads each violate `3..6`
although each local count lies inside that interval. Conversely, contributions
of one and two heads satisfy aggregate `3..6` although neither meets its lower
bound. `subview_upper` proves only the valid consequence of head inclusion:
a finite aggregate upper bound also bounds each included view.
`inherited_union` proves that adding an ancestor's subtype view again changes
no identities. It does not justify summing overlapping views.

Local intervals alone do not decide aggregate feasibility. A nested realization
under an absent optional ancestor contributes zero; several actual parents may
multiply a local contribution; an abstract chain repeats identities rather than
creating new ones. Any future feasibility analysis must establish these facts
from actual presence, ownership, coverage and disjointness before using sums.
This contract introduces no sum-of-local-bounds admission check.

## Checked witnesses and remaining boundaries

The [aggregate fixtures](../Clafer/Behavioral/AbstractMultiplicityExamples.lean)
exercise aggregate boundaries, cross-parent realizations, optional ancestor
absence, shared super-chain identities, distinct reference heads at a shared
target, and count changes after time zero. The richer existing nested-abstract
fixture supplies a fully admitted nested case under the same local meaning.
The proof declarations retain the exact assumptions for each result.

Downstream compiler implementation must pin an accepted semantic revision,
preserve authored provenance and establish encoding/decoding correspondence.
The extension does not widen the historical finite checker or claim agreement
with the pinned Haskell backend. Independent semantic review remains required
before acceptance; kernel checks establish the stated propositions.
