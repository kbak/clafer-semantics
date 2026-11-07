# Tracing Lean definitions and proofs

The pinned IntentBond imports OFT coverage tags from actual Lean line, nested
block and documentation comments. Its temporary comment view lets OpenFastTrace
4.9.0 parse the tags while retaining original `.lean` paths and physical line
numbers. Strings and escaped identifiers do not supply coverage. Lean source
remains captured by `scope.json`, built, kernel checked and selected for review.

## Lean artifacts

Put implementation tags immediately before the relevant definitions, proof tags
before the actual theorems, and test tags before assertions or test entry points.
Use ordinary `--` line comments, including when one declaration supports several
requirements. Place tags before an existing declaration doc comment so that its
attachment is preserved. Do not collect a file's links in its module header.

One tag can introduce a contiguous group of declarations for the same requirement,
such as the unary predicate definitions. Repeat it for a separate group only when
that gives a useful source location; helpers need no tag merely because they share
a file with an implementation. Keep implementation and proof links at their
respective declarations. For example:

```lean
-- [impl->req~formula-translation~1]
def translate ... := ...

-- [proof->req~formula-translation~1]
theorem translate_id ... := ...
```

Only add a link when the declaration or group supplies evidence for that contract.
Read the actual declaration and its assumptions before annotating it; a document's
mention of a module does not establish coverage of every requirement it discusses.

Source annotations are the authoritative implementation, proof and test links.
Keep mathematical explanations, theorem assumptions and limitations in the relevant
[topic contracts](intent.md#documentation-map), and exact paper correspondence in
the [source map](sources.md). Link directly to the relevant source modules when
explaining a result. Do not maintain a second requirement-to-declaration inventory
in Markdown. Documentation that itself fulfills a documentation requirement may
carry its own implementation annotation beside the relevant text.

Use `Needs: impl, proof` on requirements that require both. A theorem can supply
both when stating and proving a mathematical result is the implementation.
Use `utest` or `itest` for actual checks rather than labeling executable test code
as a proof. Maintain requirements, source tags, explanations and assertions
together. Pure import aggregators and unrelated helpers need no arbitrary tags.

OFT checks the declared links, including requirement revisions. A tag or artifact
named `proof` does not establish a theorem: Lean checks the declaration, and
review assesses whether its statement matches the requirement and paper. The
configured command still supplies command-level evidence rather than individual
theorem-execution associations.

To inspect the links imported for a requirement, use an existing IntentBond
evidence bundle from the [validation workflow](../CONTRIBUTING.md#setup-and-checks):

```sh
ib explain 'req~behavioral-snapshot-bridge~1' --compact --evidence /path/to/evidence.json
```

This reports the captured links and source locations. It does not rerun checks
or establish that the evidence matches later edits; inspect the linked source
and use the workflow's source verification when reusing validation evidence.

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

<a id="behavioral-contract-and-future-proofs"></a>

## Behavioral contract and proofs

The [behavioral contract](behavioral-profile.md) and its
[source ledger](sources.md#behavioral-profile-sources) are implementation artifacts
for **documentation** requirements: the profile requirement
(`req~behavioral-profile~1`) and structural boundary requirement
(`req~behavioral-structural-boundary~1`). Feature-matrix rows and API summaries
are distinct from the annotated Lean declarations and proof artifacts they describe.
The [trace foundation](behavioral-traces.md) explains the implemented identity,
lifetime and snapshot contracts and links to their annotated Lean definitions.
For each implementation ticket, link its actual definitions/theorems
and positive/negative witnesses using the convention above, preserving exact
source locators and all structural, environment, definedness and finite-bound
assumptions. Record unresolved semantic choices publicly before implementing them.

Current feature validation uses the captured main baseline and its trusted
scope, with the manifest-selected validation path. The completed behavioral
integration required full validation against its explicit integration baseline. Retain evidence outside source and verify each accepted
commit against it before downstream pinning. Independent semantic review remains
required even when all coverage/build/kernel gates pass. The final qualification
must close every required feature row; checking the first slice is insufficient.
