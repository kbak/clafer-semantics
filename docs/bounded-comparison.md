# Bounded structural comparison

The harness under `scripts/verification/` implements the accepted
[comparison contract](resolved-ir-comparison.md) using the
[paired importer](resolved-import.md) and [verified checker](structural-checker.md).
It compares a supplied candidate with the actual pinned compiler's static Alloy
output. Solver observations supplement the checker theorem; they are neither
kernel proof certificates nor universal compiler soundness/completeness results.
Source parsing, defaults, resolution, optimization, inferred-scope adequacy,
expressions, primitives, temporal features and production generation are excluded.

The manifest’s `paper_sha256` belongs to the immutable `52-S/v1` comparison
contract and retains the original preprint identity for replay compatibility.
The [source map](sources.md#primary-source) records that provenance separately
from the publisher e-offprint now used for maintained citations.

## Representation relation

For admitted core `m`, let `U` be the candidate's finite object labels, `r` its
root, `H_d` its head sets and `Q_d`, `R_d` its ordinary relation tables. An Alloy
witness represents the candidate exactly when a bijection from `U \ {r}` to the
union of all user signature extents preserves every `H_d`, every emitted `Q_d`
and every `R_d`. Abstract and subtype membership use the same atom. The root is
virtual: decoding adds exactly one fresh root, with every top-level concrete
head related to it. Abstract declarations have no root containment field.
The remaining `Q_d` are emitted fields, identified by receipt ownership and target.

`relation.pin` existentially quantifies pairwise-distinct variables over the
union of user signatures, then equates **complete** extents and relations with
the corresponding variables and tuples. Empty relations have arity two. There
are no added subtypes, free user fields or cardinality-only candidate pins.
Non-root objects outside every head make the pin impossible. Root membership
or top-level containment incompatible with the virtual-root convention makes
the pin false. These well-typed negative candidates remain checker inputs;
malformed serialization/typing is diagnosed before pin construction. Candidates
outside a requested scope are unsupported comparisons, retaining any observed
checker violation. No unrelated-head disjointness is imposed on Lean admission.

The correspondence argument is explicit: quantified distinct variables give
the object injection; full extent equalities and the quantifier's user-union
domain give surjectivity. Field equalities give both directions of tuple
preservation. Conversely, any representing bijection supplies the quantified
variables and satisfies these equalities. This describes representation, not
satisfaction of the generated facts. Alloy's intrinsic top-level and sibling
`extends` disjointness makes a pin of incomparable overlapping heads unsatisfiable.
The independent Clafer declaration-disjointness obligation rejects the same typed
candidate, producing `agree_violates`. The overlap remains in admission and
enumeration; neither pinning nor decoding assumes disjointness.

Ordinary links are tuples. Reference-composite links are `(uid,parent,head,target)`;
an object bijection induces link bijections, preserving different heads at equal
parent/target. No endpoint-pair deduplication is used. `relation.decode` recovers
all signature/field tuples and the virtual root, checks typing/bounds, and invokes
the same Lean checker. `relation.isomorphism` checks the full incidence structure,
partitioning by all memberships; it has a finite time budget and reports an
inconclusive execution on exhaustion. An unpinned command uses only the manual
bound guards, decodes its returned witness and checks it with Lean. This direction
alone does not establish reverse comparison or complete enumeration.

The reviewed symbol relation uses the signature and field inventory from the
[importer's capture receipt](resolved-import.md),
owners, binary arities and target UIDs. It never strips guessed suffixes. When
reference and containment have identical endpoints, the reference is the first
field according to pinned `Generator/Alloy.hs`, `genRelations` (lines 170–180 at
`6750e6f591b2131549122c13dee94d3d2257eaea`). Receipt order and the reviewed capture's
provenance are explicit external assumptions. S excludes inherited fields;
inherited membership is supported without allocating super objects. Unknown
signatures, fields and auxiliaries cannot be ignored.

The bridge checks each resolved field declaration's endpoint beneath its
multiplicity wrapper. Alloy's inferred relational type may widen an inherited
endpoint to its abstract parent; that approximation does not replace the declared
target identity. Decoded tuples still undergo exact candidate typing checks.

Built-in `univ`, `none`, `Int`, `seq/Int` and `String` are classified explicitly.
The last two have empty extents in this profile. Integers implement cardinality,
and user field types cannot mention them. Pin skolems are recorded and restricted
to the quantified object-variable namespace; they introduce no user atoms or
independent user structure. The pinned `util/integer` module contributes no
user signatures/facts; its arithmetic functions cannot occur in the audited
comparison formula. SAT witnesses are retained as JSON tuples and native XML.

## Scopes and arithmetic

Every signature, including abstracts, has an explicit requested upper bound.
Every actual command scope is inspected through Alloy's resolved AST, including
exactness, range and increment. The harness emits no explicit exact scopes.
All original facts/declarations remain byte-for-byte intact; only the recorded
`run show for 1` command is replaced and the recorded comparison predicate added.
Predicate collision checks compare complete identifiers using the admitted
fragment's grammar; names such as `c0_ib_candidate` remain valid.
Every added constraint, including `#signature <= requested_bound`, is in `pin.als`.

Pinned Alloy `ScopeComputer` rejects a scope other than 1 for `one sig`, and a
scope greater than 1 for `lone sig`, or scope below 1 for `some sig`. The command
therefore uses 1, `min(B,1)` or `max(B,1)` respectively, recording requested/effective scopes and the intrinsic reason.
The independent bound guards retain the requested domain (including `one` at
requested bound zero, which is UNSAT). They also enforce abstract bounds smaller
than the sum of subtype bounds. Post-SAT decoding checks the requested bounds.
This normalization does not exclude any instance satisfying the original
signature multiplicity and requested bounds, or assume optimizer correctness.

The importer validates the entire generated restricted token stream. Generated
and pinning formulas contain only integer literals, cardinalities and comparisons;
relational union/join is not integer addition. `AlloyBridge.audit` additionally
walks resolved command facts, signature facts and invoked pin bodies, rejecting
numeric arithmetic, unknown calls, temporal operators and relation arity above two.

If `N` is the sum of conservative per-signature capacities (the maximum of each
requested and effective scope), every user unary/binary relation has at most
`N`/`N²` tuples. Unions, shared inherited membership and full binary-field counts
are covered. Let `M=max(1,N²,all integer literals,all requested bounds)`.
The explicit bitwidth must satisfy `M <= 2^(b-1)-1`; supported widths are 1–16.
Failure is unsupported, never semantic UNSAT. `noOverflow=true` is supplementary
and does not replace this independent range argument.

The solver is the contract's hash-pinned Alloy 6.2.0 distribution with bundled
SAT4J and Java 17. `alloy_runtime.py` checks JAR/manifest identities, compiles the
bridge from current source outside the repository, and records runtime/vendor/VM
build and all public `A4Options`. It enforces one worker, symmetry 0, skolem depth
0, no partial-instance inference or decomposition, overflow prevention, and the
remaining fixed contract options. It strips ambient JVM option overrides.
Wall-clock, Java heap and process address-space limits are explicit. Missing tools,
timeouts, resource exhaustion and parse/adapter errors fail required checks.
Linux x86_64 can provision a hash-checked Java 17 JDK; explicit invalid runtimes
fail instead of silently falling back. CI already supplies Java 17.

Staticness is checked by `CompUtil.isTemporalModel` and effective min/max trace
bounds `-1`. At the pinned Alloy commit, `A4Solution.java` wraps even static SAT
instances in a one-state `TemporalInstance`; `isTemporal()` alone does not test
whether temporal solving was enabled. Static trace bounds are retained.

## Search, sensitivity and replay

`candidates.domain` enumerates canonical labels `1..n` plus root `0`, for every
`n` from zero through the sum of requested user scopes. Its stated domain fixes
fresh singleton root membership. It enumerates every bounded user membership
subset and every typed ordinary relation subset, including unrelated overlap,
unused objects and missing/multiple endpoints. It applies no symmetry reduction
or satisfaction filtering. Root-violating and malformed inputs remain separate
fixed negative tests. Exhaustiveness is claimed only for a fully consumed domain
with all requested cases completed and the expected denominator matched.

The fixed small suite includes `overlap.cfr` with both user scopes 1 (35 labelled
candidates), and `bag.cfr` with target/head scopes 1 (55 candidates). For the
first domain, universe sizes 0, 1 and 2 contribute 1, 9 and 25 tables; allowing
the optional typed dereference tuple in the second contributes 1, 13 and 41.

Seeded sampling uses Python's MT19937 with recorded seed, uniform
universe size, uniform per-class cardinality and subset at that cardinality,
and independent fair relation bits. It is not uniform on the full domain and
does not establish bounded completeness. Reports retain requested/admitted/
completed counts, every outcome category, interruption/budget reasons and unrun
cases. The checker itself remains a supplied-candidate verifier.

A bounded line stream
through `ImportMain` amortizes interpreter startup; every request still calls the
existing admission and checker. The adapter first builds that import closure with
Lake, then records Lean runtime/binary/module identities, checks response sequence
numbers and enforces per-request timeouts. Source changes or broken framing retire
the worker. Python runtime/build and the finite request limit are also recorded.

`mutations.py` supplies three explicitly labelled injected defects: omit the
receipt-identified set uniqueness clause, collapse repeated-target bag heads in
the pin, and drop a selected optional signature's cardinality restriction.
The original paired output and checker candidate remain retained. The first and
third expose Alloy acceptance against Lean rejection; the collapse exposes
pin/decode failure. These are sensitivity experiments, not current-compiler bug
claims. `candidates.shrink` removes objects or single rows deterministically,
retaining each comparison. A completed fixed point is deletion-minimal under
those operations, not globally minimal; inconclusive trials cannot establish
minimality. Stable fixtures are MIT licensed; raw evidence stays external.

`comparison.py` writes `clafer-structural-comparison/v1` artifacts. Raw input
hashes cover source, both IR states via receipt, compiler build, original Alloy,
core, candidate, pin, command, bounds, settings and current Lean/adapter sources.
`source.json` retains the complete source byte inventory in checkouts and captured
source trees alike. `lean_commit` records the actual checkout commit, or `null`
when the source root has no `.git` entry. Git lookup uses only that root's metadata;
it never discovers a parent repository. Corrupt metadata and Git execution failures
produce an inconclusive execution diagnostic, not an unavailable-commit success.
The optional commit field never replaces source hashes or replay runtime checks.

The input manifest does not hash itself or outputs. Results reference that
manifest and hash raw solver logs, witness, decoded tables and bijection. Null
verdicts identify stages not run. `ImportMain.failedPredicates` names failed
conjuncts of the existing checker for violating candidates; it introduces no
second satisfaction definition.

Replay rejects duplicate keys, unknown versions,
missing input hashes, changed bytes and changed checker/adapter source.
CLI candidates and replays retain the exact supplied JSON bytes before strict
parsing, including whitespace and malformed/duplicate-key inputs. Generated or
dictionary API candidates use their deterministic serialized bytes. Malformed
input receives a replayable diagnostic with null checker/solver verdicts.
It also checks the recorded Python, checker and Alloy/Java runtime identities.
Original-model parsing, comparison parsing, profile validation, solving and
witness extraction have distinct diagnostics. A failure after solving preserves
the observed SAT/UNSAT result and cannot count as a completed comparison.

The importer `spellings.cfr` fixture checks Latin-1 display names, escaped
apostrophe UIDs and collisions with literal `__prime__` names. Its exact candidate
and replay must complete with `agree_satisfies`, retaining distinct objects and
reference heads. A separate injected malformed-Alloy test retains the
`original_parse` diagnostic with no solver result. Unexpected execution errors
fail required validation. The stable unrelated-overlap candidate and all three
deletion-minimal injected cases are also retained as licensed JSON fixtures.

```sh
python3 scripts/verification/comparison.py compare /external/capture candidate.json \
  /external/new-result --overall 5 --bitwidth 8
python3 scripts/verification/comparison.py replay /external/new-result /external/replay
python3 scripts/verification/search.py /external/capture /external/search \
  --mode seeded --seed 52 --count 20 --overall 5 --bitwidth 8
```

Prepare captures with the existing import guide. `CLAFER_ALLOY_JAR`,
`CLAFER_JAVA_HOME` and `CLAFER_ALLOY_CACHE` select explicit external tools/cache;
`CLAFER_COMPARISON_EVIDENCE` selects the external test evidence parent. Full
validation discovers `test_bounded_comparison.py`, which invokes real paired
compiler, Lean and solver runs. CI retains the evidence directory. There is no
automatic upstream posting. Bounded UNSAT, sampled success, tool roundtrips and
trace coverage never establish unbounded compiler correctness. Independent
semantic review and full source-matched validation remain acceptance gates.

External trust includes the Haskell parser/compiler/capture observer, strict
Python byte decoder and SHA-256, the Alloy parser/AST translator/SAT4J solver,
the Java/Python/Lean runtimes and extraction of witness tuples. The relation
argument above and executable tests are reviewed evidence, not Lean theorems
about those external tools. Hashes establish byte identity, not producer identity.
