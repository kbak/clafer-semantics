# Behavioral traces and structural snapshots

[The behavioral profile](behavioral-profile.md) supplies the versioned source
contract. Its foundational trace API is exposed by `import Clafer.Behavioral`;
ordinary `import Clafer` remains structural. This increment implements the
identity, lifetime and common structural bridge obligations. Formula meaning,
modifiers, surface reductions and lasso analysis remain separate work.

## Shared identities and presence

[`Identities`](../Clafer/Behavioral/Trace.lean) supplies a shared carrier `U`, a
synthetic root, one direct declaration type per identity and an optional actual
parent. Types and parents are independent of time. `Identities.Valid` requires
a concrete direct type, the unique root type, no parent for the root, and a typed
parent for every other pool identity. The actual parent type may refine the
model's declared parent through its super closure. In the common supported
fragment, abstract declaration roles have no containment parent; a concrete
instance of such a role still has its own actual parent.

`Trace` adds `live : Nat → Set U` and a declaration-indexed dereference relation
at every time. Neither time nor the identity carrier is bounded or required to
be finite. The carrier may contain identities that never appear. Relations are
raw data: dangling, missing or multiple reference targets can be represented
but fail the corresponding validity clauses. Reference-head identities are
separate from targets; two bag heads at the same parent and target remain two
objects. A head's targets can change without changing its identity or parent.

`ParentAt t p x` requires both identities live and the static parent assignment
`parent x = some p`. `parent_stable` compares **any two times**, including times
separated by absence. `type_stable` compares snapshot objects through their
embeddings into the shared pool. Equality of names or targets is irrelevant.
`top_level_parent` proves that a live object's actual parent is the root when
its direct declaration's parent is the root declaration.

## Valid states and legal traces

`Trace.raw` presents a state on the shared carrier. Its head sets intersect
presence with the complete super closure of each object's direct type.
Containment requires live endpoints, the static parent and a parent-bearing
declaration view. Dereferences are retained literally, so an invalid endpoint
cannot disappear through filtering.

`StateValid` reuses the independent structural predicates for typing,
inheritance, abstract cover/disjointness, parents, reference totality and
uniqueness, set-only keys, multiplicities, group unions and declaration
disjointness. The root head is exactly the synthetic root, which is excluded
from every other head. Full ambient-object coverage is intentionally absent
from this **pool presentation**. Every live object has its direct head through
the reflexive super closure; a dead pool object belongs to no live head.

`Trace.Valid` combines static identity validity, root presence at every natural
time, parent presence whenever a child is live, and `StateValid` at every time.
The parent-presence clause also applies independently of visible containment
views. These obligations do not make arbitrary sequences of structurally valid
configurations legal: the same identity cannot acquire a different type or
parent at a later time. `Admissible` additionally requires the existing
`EffectiveCore.WellFormed` and `Supported` guards. No temporal formula or modifier
is included in this foundational validity predicate.

## Projection and constant embedding

[`snapshot`](../Clafer/Behavioral/Snapshot.lean) uses the carrier
`Trace.Live t = {x : U // x ∈ live t}`. `embedding t` is the injective map back to
`U`. The root and all relations retain their identity values. This resolves the
existing `Configuration.Rooted` requirement that **every ambient object** be
root or a nonroot head member: unused pool identities are not snapshot objects.

`snapshot_structural` derives `StructuralSatisfies` from `Trace.Valid`.
`admissible_projection` exposes the same result on the accepted common fragment.
The transport proof itself does not need the model guards; they select the
language domain. `fiberEquiv` and `childEquiv` preserve the complete containment
fibers and group unions, so bounds still count head objects. `snapshot_distinct`
and `snapshot_parent_stable` preserve occurrence separation and ownership.

The converse uses `StaticCorrespondence m s ids`. Its exact hypotheses are:

- `ids.Valid m` and agreement of the two roots;
- `x ∈ s.head d` exactly when `d` is in the super closure of `ids.directType x`;
- `s.contains d p x` exactly when the static parent is `p`, that same head view
  is present, and declaration `d` has a parent.

These are explicit direct-type and parent witnesses, including exact agreement
with all overlapping super extents and containment relations. This increment
does **not** derive existence of these witnesses from arbitrary structural
satisfaction. Callers must construct them; the bag and inherited fixtures do so.
The source model must separately satisfy `StructuralSatisfies m s`.
`constant_valid` then gives a trace with every original object always live and
the original dereferences at every time. `constant_admissible` additionally takes
the two model guards. `constant_raw`, `constantEquiv` and `constant_snapshot`
recover the entire original configuration, field by field, through the live
carrier equivalence. The witnesses are not assumptions of temporal preservation.

The bridge is confined to the existing guarded effective core. Richer inherited
references, primitive domains and structural atoms remain obligations of the
[structural atom extension](behavioral-profile.md#ownership-and-proposed-module-boundaries).
No Compile, gluing, checker or importer contract is changed.

## Lifetimes and checked boundaries

`Starts t x` means that `x` is live at `t` and either `t = 0` or it was absent
at the preceding time. `Ends t x` means that `t` is live and `t + 1` is absent:
it identifies the last live state. `starts_zero`, `starts_succ` and
`end_then_start` cover initial presence, absence and reappearance. The root starts only at zero and never ends (`root_starts`, `root_never_ends`).
Constant traces give these same laws for every object. These predicates do not yet interpret
`initially`, `finally` or cancellation of temporal obligations.

[Examples](../Clafer/Behavioral/Examples.lean) kernel-check a four-phase infinite
cycle with two machine identities, repeated-target bag heads, persistent targets
and an unused pool identity. Every live snapshot satisfies the structural model;
the pool presentation fails full `Rooted` coverage. The old heads disappear when
their fixed parent is replaced, then reappear with that same parent. Dereference
targets change across those lifetimes. Mutations retaining an orphan child or
changing one identity's parent across a gap are rejected. A target-only mapping
is proved noninjective on the two bag occurrences; the projected head fiber
satisfies an exact-two bound that its target union violates. A dangling-reference
mutation is rejected, and a target change during one continuous lifetime is
accepted. Existing structural bag and
inheritance models supply concrete constant-embedding witnesses.

The [dependency test](../tests/behavioral_dependencies.lean) ensures the optional
semantic entry point imports neither Compile nor Verification. [Structural-import testing](../tests/structural_without_behavioral.lean) also
keeps `import Clafer` free of the optional extension. Only the fixture module imports the existing structural checker examples. All new modules remain
under Clafer; the generic lower layers retain their existing contracts.

## Source correspondence

The primary behavioral reference is Juodisius et al., §5 Definition 2 and static
typing on p. 2:25, Definition 3 on pp. 2:25–26, and Definition 5.1/5.3 on p. 2:28.
The [pinned source ledger](sources.md#behavioral-profile-sources) retains bytes,
licenses and the exact 0.5.7 candidate. T1 replaces the paper's no-reappearance
clause and strengthens parent stability to all lifetimes. T7 supplies time-zero
birth and repeated lifetime anchors. T11 corrects set-only reference injectivity
and group counting; this bridge retains the existing supported structural group
contract. T13 does not impose finite bounds on the infinite source domain.
SoSyM remains the source for the reused structural predicates. This foundation
does not claim all of Definition 5: its constraint-satisfaction clause requires
the later signed temporal semantics.
