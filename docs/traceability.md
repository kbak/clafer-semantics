# Tracing Lean definitions and proofs

The pinned IntentBond imports OFT coverage tags from actual Lean line, nested
block and documentation comments. Its temporary comment view lets OpenFastTrace
4.9.0 parse the tags while retaining original `.lean` paths and physical line
numbers. Strings and escaped identifiers do not supply coverage. Lean source
remains captured by `scope.json`, built, kernel checked and selected for review.

## Lean artifacts

Put implementation tags beside the relevant definitions, proof tags beside the
actual theorems, and test tags beside assertions or witnesses. Use a line comment
for a single tag; reserve block comments for groups of tags. A module comment may
group tags when its declarations jointly implement the linked contract.
For example, an existing requirement can have these source links:

```lean
-- [impl->req~formula-translation~1]
-- [proof->req~formula-translation~1]
```

Keep the named Markdown artifacts in [DPGraph](dpgraph-trace.md),
[FormalCD](formalcd-trace.md) and [Clafer](clafer-trace.md) as readable accounts of
source correspondence, declaration names and theorem assumptions. Their stable
IDs and existing links remain useful; inline tags add direct source locations.
Use `Needs: impl, proof` on requirements that require both. Use `utest` or `itest`
for actual checks rather than labeling executable test code as a proof.
Maintain requirements, source tags, these explanations and assertions together.
Pure import aggregators and unrelated helper declarations need no arbitrary tags.

OFT checks the declared links, including requirement revisions. A tag or artifact
named `proof` does not establish a theorem: Lean checks the declaration, and
review assesses whether its statement matches the requirement and paper. The
configured command still supplies command-level evidence rather than individual
theorem-execution associations. Markdown artifacts do not replace source tags
when the corresponding implementation or proof lives in Lean.

The source-import regression checks a real annotated Lean module through the
installed IntentBond importer, so a future pin that silently drops Lean artifacts
fails the repository check. Parser tests and broken-reference regressions belong
to IntentBond; build, kernel, axiom and semantic checks remain here.

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
