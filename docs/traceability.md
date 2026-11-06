# Tracing Lean definitions and proofs

The pinned IntentBond/OpenFastTrace combination imports Markdown requirements
and artifacts, but OpenFastTrace 4.9.0 does not import `.lean` source tags.
Do not put OFT coverage annotations directly in Lean files and assume they are
checked. Lean files remain in `scope.json`: their contents are captured, their
modules are built and kernel checked, and their changes require review.

## Lean artifacts

Until native Lean tag support is adopted, declare named implementation and proof
artifacts in Markdown under `docs/`, beside explicit links to the corresponding
Lean file and declaration names. For example, when a real requirement exists:

```markdown
## Representation of model shape
`impl~model-shape-representation~1`

The `ModelShape` declaration in Clafer/Syntax.lean represents the selected
abstract syntax. Link the source file and explain the correspondence here.

Covers:
- `req~model-shape~1`
```

Proof artifacts can use the same structure with type `proof`, naming the actual
theorem and its source. State `Needs: impl, proof` on requirements that require
both, rather than labeling documentation as proof. Use `utest` for actual tests.
Maintain these artifact declarations, source links, theorem statements, and
requirements together. Keep source references precise as declarations move.

These are checked OFT artifacts whose locations are in Markdown. Review must
follow their links into the Lean implementation and proofs. Neither a source
link nor an artifact named `proof` establishes the theorem; Lean checks the
declaration, and review assesses whether its statement matches the requirement
and the cited paper. Command-level evidence records the configured check's
result; it does not associate individual theorem executions with artifacts.

## Scope selection

[CI](../.github/workflows/ci.yml) selects the PR base (or the previous commit for
pushes) and uses its scope. If that base has no scope, the initial-adoption check
uses the candidate as baseline and explicitly leaves adoption to PR review.

With an existing scope, [ci_scope.py](../scripts/ci_scope.py) accepts identical
baseline/candidate bytes, the exact recognized public-root expansion, or the
exact project-name migration from `clafer-lean` to `clafer-semantics`. For
that expansion it derives `inputs: ["."]` and `review_paths: ["."]` from the
recognized historical baseline, requires the pinned resulting bytes, and retains
the actual Git baseline. These layout-independent paths capture both historical
and sibling-root sources. Specification/test paths, coverage floors,
revision/skipped-test policy, command and timeout remain baseline obligations.
The project-name migration starts only from the pinned expanded scope and
changes only `name`, requiring the exact resulting bytes. It leaves all source
selection, coverage and execution obligations unchanged.
For scope changes, unknown baselines, partial migrations, reversions and unrelated
policy edits are rejected by the selector and exercised in
[regression tests](../tests/test_ci_scope.py).
Candidate policy changes cannot authorize themselves; other changes need separate
review. Local checks against the historical baseline use the independently
approved expanded scope via `--scope`; the project-name migration likewise uses
its reviewed scope when validating the new metadata.

CI retains baseline, candidate and selected scope byte identities, canonical
policy identities and the transformation alongside check evidence. Byte hashes
identify exact files; canonical policy hashes identify parsed policy values.
Authorization history belongs in PR context and external factory evidence.
Frozen task snapshots retain historical paths and are not current architecture
or scope-selection guidance.

## Documentation validation selection

[The validation wrapper](../scripts/validation.py) captures both source manifests
using the pinned IntentBond implementation, compares every path's contents and
mode, and retains the selection outside source. [The shared check](../scripts/check.sh)
compares the complete actual snapshot with the recorded candidate before running
the documentation path. Only changes to regular, nonexecutable `README.md` or
Markdown under `docs/` qualify; uncertainty selects full validation.

This selects the checks run by the existing baseline command; it does not change
`scope.json`, coverage requirements or review paths. The selection record contains
the baseline commit, source identities and reason; IntentBond's test log records
the actual path and results. Keep both with the evidence. Documentation checks do
not supply fresh Lean execution evidence or semantic approval. See
[setup and checks](../CONTRIBUTING.md#setup-and-checks) for commands and prerequisites.

## Behavioral contract and future proofs

The [behavioral contract](behavioral-profile.md) and its
[source ledger](sources.md#behavioral-profile-sources) are implementation artifacts
for **documentation** requirements: the profile requirement
(`req~behavioral-profile~1`) and structural boundary requirement
(`req~behavioral-structural-boundary~1`). Feature-matrix rows, reserved module names
and fixture recipes are obligations, not Lean declarations or proof artifacts.
When an implementation ticket is accepted, link its actual definitions/theorems
and positive/negative witnesses using the convention above, preserving exact
source locators and all structural, environment, definedness and finite-bound
assumptions. Record unresolved semantic choices publicly before implementing them.

Feature validation uses the captured behavioral integration baseline and its
trusted scope. Behavioral PR/push CI requires full validation; main keeps the
manifest-selected path. Retain evidence outside source and verify each accepted
commit against it before downstream pinning. Independent semantic review remains
required even when all coverage/build/kernel gates pass. The final qualification
must close every required feature row; checking the first slice is insufficient.
