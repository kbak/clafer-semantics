# Behavioral structural prerequisites

`impl~behavioral-structural-audit~1`

The [behavioral profile](behavioral-profile.md) uses the independent richer
structural and expression interfaces below. They implement the S4 bridge owned
by [structural atom compatibility](https://github.com/kbak/clafer-semantics/issues/126),
while preserving the guarded [trace foundation](behavioral-traces.md) and all
historical static meanings. The [source ledger](sources.md#behavioral-profile-sources)
fixes the compiler candidate and document hashes. S1–S11 denote static errata;
T8/T10/T11 denote temporal errata.

## Reuse and admitted domains

| Prerequisite / profile rows | Delivered interface and exact boundary | Downstream responsibility |
| --- | --- | --- |
| Effective own/inherited groups; B05/B32; S1–S5, T10–T11 | `Structural.Groups` enforces `Semantics.Groups.Holds` on authored ordinary declarations, counting the union of child heads over super ancestry. `Structural.snapshot_groups` transports the complete predicate to live identities. | C6 supplies effective defaults/bounds and their provenance under the adopted default contract. |
| Abstractness and ordinary inherited fields; B01/B05 | `Structural.Core.authoredAbstract` distinguishes authored abstracts from ordinary inherited fields. `IdentitiesValid` permits ordinary direct instances; `Abstracts` covers authored abstract extents by their subtypes. | C6 preserves authored flags when elaborating effective declarations. |
| Nested abstractness/refined parents; B01; S6 | `Core.WellFormed.refined_parent` permits the same parent or a subtype of the super's parent. Nested abstract types can have concrete parents. State typing, fixed actual parents and `View` retain existing objects across contexts. | C6 resolves containment/type identities and checks these model obligations. |
| Concrete supers; B01; S10 | Source admission permits concrete inheritance, as SoSyM §5.5 and behavioral Definition 1.5 require. The concrete-inheritance fixture is admitted outside the old static support guard. | A comparison with the pinned compiler must retain its abstract-super-only limitation. |
| Inherited/refined references; B04/B06/B18; S8–S9/T8 | `InheritedReference.Owner` finds the nearest declared reference. `Structural.Valid.inherited_reference`, `target_typed`, `target_live` and `refined_reference_agrees` derive totality, endpoint validity and shared-head agreement. | S5 applies modifiers to these same heads/assignments/target images; C6 resolves reference target views. |
| Set/bag occurrences; B04; S4/T11 | `Structural.Keys` enforces set uniqueness within each declaration's containment fiber; bags retain separate heads. `StructuralBinding.Link` retains an intermediate head even in parent-to-target maps. | C8 must encode those occurrences, not only an existential relation reduct. |
| Root, actual parents and disappearance; B01/B06; S7 | `Valid` requires a permanent root, live parents and rooted live containment. `top_level_parent`, `view_parent_unique`, `view_covers` and direct parent navigation preserve actual ownership. Raw dangling links fail validity. | Mixed parent classes are resolved per context by C6; no invented parent class is attached to a parentless abstract declaration. |
| Resolved navigation; B06/B08 | `StructuralBinding.Resolution.ofRoles` derives endpoint typing from declaration roles and valid states. Every support vertex/map occurrence is retained. `coherent` compares full links for repeated identities. | C6 inserts implicit dref once and supplies endpoint roles; unresolved name-search order remains separate. |
| Captured variables, this and quantification; B07–B08 | `Structural.observed` supplies inherited current relations to the accepted D1 set evaluator. `CapturedStatic.agrees` covers every static constructor on singleton-compatible environments with live this. Quantifiers evaluate their domain before pushing singleton identities. | C6 supplies resolved lexical metadata and runtime typing. Stored sets/absent identities are not automatically static-admissible. |
| Primitive observations; B31 | `PrimitiveExpression` composes strict extraction, finite-set coercion, cardinality, scalar operations, extrema and indexed folds. `finite_reference_operand` derives definedness from finite captured heads and target-domain typing. | C8 proves bounded-backend correspondence with nonzero divisors and sufficient ranges for every intermediate value. |
| Partial temporal atoms; B08/B31 | `PartialObservation`, `Formula.Defined` and `Satisfies` keep strict definedness separate from signed truth. `StaticObservation` embeds typed static expressions; the primitive adapter embeds the new arithmetic grammar. | Lasso/encoding tasks must preserve the original formula's definedness as well as signed truth. |
| Declaration initializers; B32 | The reviewed profile supports `=` as an ordinary presence-guarded equation and explicitly rejects `:=`. `Initializers.elaborate`, `constant_truth` and `every_live_state` expose that contract. | C6/C7 issue an unsupported-form diagnostic for `:=`; no default override semantics or birth-only initialization is inferred. |

## Structural meaning and historical agreement

[`Structural`](../Clafer/Behavioral/Structural.lean) owns the richer model and
admission predicates. It keeps authored abstractness separately, requires finite
rank witnesses for declaration containment/inheritance, checks reference target
refinement and set/bag kind compatibility, and requires effective group bounds
to agree with the family annotations. `StateValid` enforces typed raw relations,
root uniqueness/separation, inheritance/abstract coverage, unique containment,
reference totality/coherence, set keys, individual multiplicities, inherited
groups, declaration disjointness and root reachability of every live identity.
Unused pool identities still have fixed well-typed direct types and parents.

Behavioral §5 Definition 2 has one partial link function per identity. Refined
reference declarations therefore constrain the same target on a shared head;
they do not introduce independent assignments. The static generator's
`genRefSubrelationConstriant` supplies corresponding subrelation constraints.
The pinned temporal generator's `genConstraints` lacks that corresponding clause.
This is a source/code comparison gap, not a reproduced end-to-end compiler
counterexample; backend agreement must establish the shared-link obligation.

[`StructuralCompatibility`](../Clafer/Behavioral/StructuralCompatibility.lean)
proves `valid_iff_common`: richer validity of `Core.ofEffective m` is equivalent
to old `Trace.Valid m` under old `WellFormed`, `Supported`, and agreement of the
two effective-group fields. Reachability, shared-reference coherence, inherited
keys and groups are derived on that domain. `ofEffective_wellFormed` preserves
model admission; `Structural.observed_common` preserves the complete observed
trace, and `eval_common` preserves every set expression. No historical guard is
removed. `Trace.admissible_projection`, `constant_admissible` and
`constant_snapshot` retain their exact statements and assumptions.

[`StructuralSnapshot`](../Clafer/Behavioral/StructuralSnapshot.lean) supplies a
separate richer live projection. Its `snapshot_groups`, `snapshot_heads`,
`snapshot_assignments` and `snapshot_targets` preserve full inherited child unions
and reference observations. It does not claim old `StructuralSatisfies` outside
the historical common domain. Behavioral public imports remain independent of
Compile and Verification; the owning `Semantics.Groups` predicate is shared.

## Distinguishing cases

The fully admitted [structural fixtures](../Clafer/Behavioral/StructuralExamples.lean)
cover nested abstract Port under concrete SubSystem, a refined-parent variant,
ordinary speed fields inherited under an abstract type, inherited and redeclared
bag references, two heads at one changing target, and inherited group count two.
They reject duplicate set targets, dead heads, dead targets, conflicting refined
assignments, a group bound of one for two children, and direct authored-abstract
instances. [Concrete inheritance](../Clafer/Behavioral/ConcreteInheritanceExamples.lean)
is separately admitted and shown outside the old static support guard.

The [resolved-binding fixtures](../Clafer/Behavioral/StructuralBindingExamples.lean)
exercise head, parent, dref, target and inclusion maps over an admitted model.
Two target-map links have identical endpoints but distinct intermediate heads;
repeated dref occurrences retain the same link carrier. Current dref observes a
changed target without changing the stored head identity.

The [primitive fixture](../Clafer/Behavioral/PrimitiveExpressionExamples.lean)
admits two reference heads alongside the entire infinite mathematical integer
domain and constructs an actual `IntegerBinding`. `complete_static_agreement`
instantiates the all-constructor theorem on that binding. Capturing a head observes
its new target later; capturing the earlier target set keeps that set. Explicit
sum over the two heads returns six at target three, while a whole-integer-extent
coercion is undefined. Empty minimum remains unequal to a present zero.

The existing guarded disappearance/reappearance and swapped-target witnesses
remain valid through the exact common-fragment bridge. The reference-modifier
interface continues to distinguish heads, head-to-target assignments and target
images: swapping targets can preserve the target set while changing assignments.
`Structural.current` exposes these observations with inherited reference lookup;
`finite_current_targets` requires only a finite observed head fiber.

## Captured static atoms and partial temporal composition

`CapturedStatic.capture` constructs a singleton-compatible captured environment
from any static environment. `agrees` and `defined_iff` prove equality with the
unchanged static evaluator for all constructors, including relations, joins,
widening, Boolean operations, quantifiers and strict extraction, assuming live
this. `admissible_push` keeps runtime membership obligations explicit.
`StructuralBinding.Resolution` supplies the current-time maps: declared roles
cover ordinary typed parent navigation, while heterogeneous abstract-parent
navigation uses the ambient `SetExpr.parent` relation or an explicitly justified
specialized resolution. Absence does not rebind stored values; standalone this
is live-filtered, while direct this-parent navigation starts at the retained
identity and requires only a live fixed parent.

The [reviewed partial-domain rule](https://github.com/kbak/clafer-semantics/issues/126#issuecomment-6687520296)
extends the accepted mathematical arithmetic. `PartialObservation` returns
`Option Prop` and `Option (Set U)`. `Formula.Defined` requires:

- Every Boolean operand, including both conditional branches, defined.
- A defined quantifier domain and a defined body for every member, for all five
  quantifier forms; a let body receives the whole evaluated set.
- For next, a defined body at the next state if its actual parent is present.
- For eventually/always/until/weak-until, defined operands at every state in the
  remaining uninterrupted parent lifetime. Until's left operand is checked before
  cancellation even if its right operand could have succeeded earlier.
- For initially/finally, a defined body only when the start/end anchor triggers.

`Satisfies` conjoins this domain with the already accepted signed denotation.
Missing observations may be completed arbitrarily internally;
`raw_extension_agrees` and `extension_agrees` prove both meanings independent of
that completion on the domain. `undefined_neither` prevents either polarity for
an undefined formula. This does not change T2's ability to satisfy both signs of
a defined temporal obligation after cancellation. `total_defined`/`total_agrees`
recover the entire old total-observation language.

`StaticObservation.signed_atom_agrees` gives exact partial static-atom agreement
under the captured-environment hypotheses. `satisfies_iff_lowered` reuses signed
normalization/lowering while retaining the *original* definedness judgment.
It does not assert that arbitrary normalization or Boolean simplification may
erase an undefined operand. The [partial witnesses](../Clafer/Behavioral/PartialExamples.lean)
cover strict branches, every quantified member, empty domains, cancellation,
reappearance, absent attachments, inactive anchors and undefined arithmetic.

## Integer-set conversion

The [reviewed D3 conversion](https://github.com/kbak/clafer-semantics/issues/126#issuecomment-6685233729)
uses the sum of a finite observed integer set for an arithmetic operand. An absent
optional numeric clafer contributes zero in arithmetic. Presence and relational
equality still operate on the original collection: the empty set is not `{0}`.
This convention is shared by the pinned Alloy generator's arithmetic functions
and Choco's `AstCompiler.asInt`. It sums distinct targets; explicit `sum`/`product`
over reference heads is a separate occurrence-sensitive operation.

[`IntegerObservation.coerce`](../Clafer/Behavioral/IntegerObservation.lean) is
defined exactly when its observation is finite and entirely in the supplied
`IntegerRealization.domain`. `coerce_empty` gives zero; `coerce_singleton` gives
the encoded integer. `agrees_with_extract` proves agreement on the entire defined
domain of historical singleton extraction. `operand` propagates a missing
expression result; it does not confuse that result with a defined empty set.
Infinite or noninteger observations remain undefined, and the arbitrary
off-domain decoder is never used. The
[witnesses](../Clafer/Behavioral/IntegerObservationExamples.lean) distinguish
absence from a present zero, check multiple distinct values and duplicate targets,
reject infinite/noninteger observations, and retain arbitrary mathematical `Int`.

The historical `IntegerRealization.extract`, `Expr.integerOf`, static denotation
and their requirements remain unchanged. The behavioral conversion is an explicit
additional interface. The resolved `PrimitiveExpression` grammar composes it with arithmetic,
extrema and occurrence-indexed folds; `PartialObservation.primitives` supplies
the guarded temporal adapter.

## Mathematical arithmetic

The [reviewed scalar rule](https://github.com/kbak/clafer-semantics/issues/126#issuecomment-6685442865)
uses mathematical integers, division truncating toward zero, and the corresponding
signed remainder. Both division and remainder are undefined at a zero divisor,
including `0/0` and `0%0`. Undefined operands propagate. Thus an absent optional
number can contribute zero to addition or as a numerator, but makes a denominator
zero and the resulting division undefined. No source operation wraps at a backend
bit width or at the machine integer limit.

[`Arithmetic`](../Clafer/Behavioral/Arithmetic.lean) defines `Binary.apply`,
strict `Binary.eval`, and `negate`. `defined_iff` gives the exact domain;
`division_remainder` proves `b*q+r=a` for defined quotient and remainder.
`static_arithmetic_agrees` preserves historical scalar addition/subtraction.
The [witnesses](../Clafer/Behavioral/ArithmeticExamples.lean) cover signed division
and remainder, all zero-divisor cases, absence in either operand position,
propagation through multiplication by zero, and values beyond 32-bit range.

The [backend audit](https://github.com/kbak/clafer-semantics/issues/126#issuecomment-6685412556)
shows why these are explicit source choices. Alloy 6.2.0 admits bitvector
wraparound and total zero-divisor results by default; its `--nooverflow` mode
rejects the tested zero-divisor and overflowing witnesses. The pinned Choco
backend rejects constant `5/0` but simplifies `0/0` to zero before checking the
divisor. It does not wrap at the modeled Alloy bit width, but some Java constant
calculations wrap at 32 bits. Neither behavior is forced by model checking.
Encoding correspondence must state finite-observation, nonzero-divisor
and sufficient-range assumptions, including intermediate expressions. These
probes compare specific pinned implementations; they are not a general
backend-correctness proof. Pins and source hashes are in the [source ledger](sources.md#behavioral-arithmetic-comparison).

## Aggregates and extrema

The [reviewed empty-extrema rule](https://github.com/kbak/clafer-semantics/issues/126#issuecomment-6685652746)
preserves a defined empty result for `min`/`max` of an empty integer collection.
Applying arithmetic conversion to that result gives zero; relational equality
with `{0}` remains false. A finite nonempty integer observation selects its unique
minimum/maximum object. Infinite or noninteger inputs are undefined.

[`Aggregate.Extreme.select`](../Clafer/Behavioral/Aggregate.lean) implements these
selectors; `select_defined_iff`, `select_subset`, `select_singleton`, `select_empty`
and `empty_extreme_operand` prove their domain, observed-object and conversion
properties. The same module supplies `Fold.eval` for explicit sums/products over
occurrence indices. It requires finitely many indices and a defined integer value
at each one, with empty identities zero and one respectively. Two heads pointing
to 3 sum to 6 and multiply to 9; implicit coercion of their distinct target set
`{3}` gives 3. `fold_defined_iff`, `fold_missing` and `fold_infinite` retain these
boundaries. The [examples](../Clafer/Behavioral/AggregateExamples.lean) check these
cases and positive/negative extrema, missing values and invalid observations.

The occurrence-indexed interface leaves frontend construction explicit. The pinned
compiler splits syntactic union operands before explicit aggregation; overlapping
operands can therefore contribute repeatedly. Agreement with a deduplicated union
requires disjointness, or the frontend must retain separate operand occurrences.
Neither the selector nor the fold makes the whole primitive domain finite.

## Source dispositions and downstream obligations

| Source item | Disposition |
| --- | --- |
| S1/S2/T10 | Retain adopted numeric/keyword child defaults and inherited opt policy; effective elaboration remains C6. |
| S3/S4/T11 | Enforce the effective group on each authored ordinary declaration over own/inherited child heads; abstract group annotations are inherited templates. Bag heads count separately. |
| S5 | An unreachable lower group bound gives an empty source context. Any compiler rejection is a frontend restriction, not a changed source predicate. |
| S6 | Admit nested authored abstracts under concrete parents and parent refinement; preserve identity and actual parent in inherited views. |
| S7 | Root is a permanent source identity. Parent navigation follows fixed actual parents, including parentless abstract views. Pinned static backend restrictions on root expressions/mixed abstract variables stay explicit in C6 comparison. |
| S8/S9 | Frontends resolve names and insert implicit dref exactly once. Typed support maps and ambient current observations implement the resulting head/target views; name-search order remains with the separate resolution decision. |
| S10 | Keep source-permitted concrete supers. Do not import the pinned compiler's abstract-super-only restriction into source validity. |
| S11 | Use the adopted mathematical integer and partial arithmetic rules above. Other numeric types are outside the accepted profile; finite encoding ranges remain compiler obligations. |
| T8 | Supply inherited heads, assignments and target images; S5 owns final/finalref/finaltarget predicates. |
| B32/D4 | Support constant `=`; explicitly reject `:=` in this profile. |

The [accepted initializer disposition](https://github.com/kbak/clafer-semantics/issues/126#issuecomment-6687520296)
uses the pinned desugarer's presence implication in the enclosing attachment
context. `Initializers.constant` takes separately resolved head and value views,
and builds `some heads => left = value`. Ordinary attachment checks it at every
live context state; no `initially` wrapper is inserted. Operand definedness is
strict even when the presence guard is false. The CheatSheet explicitly says no
backend supports `:=`, and emitting an assertion does not define override/default
semantics. C6/C7 must reject that syntax explicitly for this profile. This reviewed
restriction does not remove default multiplicity/group elaboration.

The source interfaces above compose with the [surface contract](behavioral-surface.md)
for modifiers, transitions and patterns. The compiler owns parsing, name resolution, implicit
views, initializer diagnostics and elaboration preservation; C8 owns bounded
arithmetic/reference encoding correspondence. The [qualification contract](behavioral-qualification.md)
preserves the partial domain as well as signed truth in finite composition.
No backend correctness or complete
behavioral implementation follows from structural compatibility alone.

Covers:
- `req~behavioral-profile~1`
- `req~behavioral-structural-boundary~1`
- `req~behavioral-structural-compatibility~1`
- `req~behavioral-reference-atoms~1`
