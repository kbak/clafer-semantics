# Contributing

<!-- [impl->req~public-foundation~1] -->

Start with an [existing issue](https://github.com/kbak/clafer-semantics/issues) or
propose a small, scoped one. Maintainers also track issues in a
[private GitHub Project](https://github.com/users/kbak/projects/2); contributors
can use the public issues and pull requests without Project access. Semantic work should
identify the paper sections, intended definitions/theorems, ambiguities, and
acceptance criteria before implementation. See [AGENTS.md](AGENTS.md).

## Setup and checks

<!-- [impl->req~intentbond-workflow~1] -->

Repository `kbak/clafer-semantics` contains the single Lake package `clafer`.
Place modules beneath their owning public root and preserve
`Clafer -> FormalCD -> DPGraph -> Mathlib`; `import DPGraph` remains independent.
The [product overview and documentation map](docs/intent.md) identify delivered
scope and authoritative documents; [architecture](docs/architecture.md) explains
module boundaries. Use those references when updating summaries, retaining
artifact IDs, trace links, source citations and existing link destinations.

For a first look, use the [README build](README.md#get-started) and
[Lean walkthrough](docs/getting-started.md). Building Lean examples requires
Git and Lean; it does not provision the Haskell exporter or Alloy.

For contribution checks, install Python 3.11+, Git, Java 17+ and Bash 4+.
The [GitHub CLI](https://cli.github.com/) is needed only for the ticket helper and
command-line GitHub operations. Full validation is exercised in CI on Linux
x86_64 (Ubuntu 24.04); automatic Haskell exporter setup supports that platform.
On other platforms, supply the pinned exporter and build manifest as described
below, or use a Linux x86_64 environment.
For full validation, also install Lean with [elan](https://lean-lang.org/install/)
and prepare the [pinned importer prerequisites](#pinned-import-validation-prerequisites).
Documentation-only checks do not need Lean, the Haskell compiler or Alloy. Then:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements/intentbond.txt -r requirements/documentation.txt
ib install-oft
```

Before editing, retain the baseline commit (`git merge-base HEAD origin/main` on
a feature branch; the starting `HEAD` on main). Keep the affected intent,
requirements, source/proof references, and checks consistent. Run:

```sh
python3 scripts/validation.py check --base BASE_COMMIT --candidate worktree --out /tmp/clafer-check
```

Choose a fresh external output directory for each run. The wrapper invokes
`ib check`, using `scope.json` from that baseline and running `scripts/check.sh`
on a captured source snapshot. It retains `/tmp/clafer-check-selection.json`
beside the evidence directory, with both source manifests, baseline identity and
selection reason. Add `--full` to require all validation gates. Direct
`ib check` or `bash scripts/check.sh` without a selection plan also runs full validation.

Exit 0 passes automation; exit 4 passes automation with
semantic review pending. Other exits fail. Keep the reported evidence directory
outside the repository and summarize it in the PR. After committing, match the
commit against that evidence with `ib verify --base BASE_COMMIT --candidate HEAD
--evidence /path/to/evidence.json`. Use `--allow-pending-review` only when review
will be enforced before acceptance.

For quick feedback while editing, run `bash scripts/check.sh --preflight`.
This checks module discovery and its Python regressions without requiring Lean;
it does not replace the full check. The full command runs this preflight before
toolchain/dependency setup and prints elapsed seconds for each validation step.
CI streams the retained test log during validation and includes stage timings in
the job summary, so compilation and kernel replay progress are visible while running.

The installed IntentBond skill is at `intentbond/skills/intentbond/SKILL.md`
inside the Python package. It can be located with:

```sh
python -c 'from importlib.resources import files; print(files("intentbond") / "skills/intentbond/SKILL.md")'
```

### Validation paths

The wrapper and CI select documentation checks only for regular, nonexecutable
`README.md` or Markdown under `docs/`. Changes to `CONTRIBUTING.md`, scripts,
tests, dependencies, workflows, agent instructions or `scope.json` require full
validation, as do empty diffs and uncertain comparisons. The
[selection contract](docs/traceability.md#documentation-validation-selection)
explains source capture, snapshot verification and retained evidence.

Documentation checks cover module inventory, its Python regressions, validation
selection, topic filenames, and local document links and heading anchors. They
do not run Lean examples or provision Haskell and Alloy. IntentBond coverage,
source matching and independent review still apply, including review of
mathematical claims. Frozen change records remain under their retention policy;
link checks cover living documentation.

CI selects documentation or full validation before expensive toolchain setup,
and runs IntentBond on pull requests and main. Follow the
[scope-selection rules](docs/traceability.md#scope-selection) for baseline policy,
first adoption and the exact public-root expansion. Local checks against the
historical baseline require the independently approved scope via `--scope`.
Candidate policy changes cannot authorize themselves; other scope changes
require separate review.

### Full validation and caching

The shared check discovers every project module, rejects reverse dependencies
(including through root/helper modules), builds and runs `leanchecker` on each,
including examples. It batches library/module builds in one Lake invocation and
passes the three public roots to one verbose `leanchecker` invocation, which
enumerates their compiled descendants, including unimported helpers/examples.
This avoids repeated directory scans and overlapping module replay. The checker
thread pool defaults to four threads; set `LEAN_NUM_THREADS` to choose its size.
It generates an `import all` audit from
`tests/axiom_audit.lean`. After the build, it runs that audit, the independent public-import test, all Lean
validation tests and Python tests, including dependency/scope/audit rejection cases.
These gates precede the expensive kernel replay so failures return earlier.
Every successful full check still replays the complete discovered module inventory.
Unowned Lean sources are errors; keep validation harnesses under `tests/`.
The audit permits only Lean's standard logical axioms (`propext`, `Quot.sound`,
`Classical.choice`) and reports which are used; it rejects new axioms, unsafe or
partial project declarations, including private/generated declarations selected
by module origin. The audit rejects empty/missing DPGraph coverage; zero
FormalCD/Clafer declarations mean scaffolding only. Mathlib is pinned in the Lake files. The check
first tries Mathlib's normal cache for the imports discovered across every project
module and Lean test, including helpers/examples outside the public entrypoints.
Mathlib fetches their transitive dependencies; the generated inventory is
`.lake/validation/mathlib-imports.txt`. An empty inventory skips prefetch, and an
unavailable cache falls back to source compilation. Ordinary `lake build` also builds
from source. Cache availability never waives the build or kernel check.

The shared check defaults Lake artifact caching to disabled. CI and factory
profiles may enable native caching for project modules and pinned dependencies;
keep that cache outside captured source and preserve the complete validation
gates. Lake checks source, compiler-option and transitive-import traces before
reusing a module, rebuilding changed modules and their dependents. CI saves Lake
artifacts and Mathlib downloads in separate caches after successful checks, keyed
by OS, architecture, toolchain and dependency manifest. Lake's cache retains a
commit suffix so new builds can populate it. Mathlib's download key includes the
discovered import inventory, avoiding repeated uploads when only project proofs
change while allowing newly imported dependencies to populate a new cache.
`LAKE_CACHE_DIR` and `MATHLIB_CACHE_DIR` locate these caches outside the checkout
so IntentBond's fresh snapshots inherit them. `LAKE_ARTIFACT_CACHE=true` enables
incremental compilation; use `false` for fresh compilation in an isolated snapshot.
The shared check sets `LAKE_RESTORE_ARTIFACTS=true` so all outputs are restored to
the paths used by the audit, tests and kernel checker. A warm cache still runs
the complete module build, fresh kernel replay, axiom audit and regression tests.

CI also caches Python package downloads and pinned OFT/Alloy jars; installation
and jar verification still run. Before restoring Haskell build dependencies,
CI probes a small exporter cache containing only the executable, build manifest
and recipe digest. `scripts/verification/runtime.py --check-cache WORK` checks
these identities without provisioning. `--github-env WORK` prepares or rechecks
the exporter and appends its paths to `GITHUB_ENV`; `WORK` must be external.
A verified hit skips the compiler dependency restore and build prerequisites.
Changed or missing exporter inputs take the pinned build path. Cache keys include
the exporter, builder, runtime and protocol sources and runner platform. All live
compiler/solver comparisons still execute and produce new evidence.

On a miss in the separate Lake cache, CI also tries the previous combined cache
layout. This seeds the new caches during rollout; Lake still validates every
restored artifact, and missing artifacts take the normal build path.

Set `CLAFER_TEST_JOBS=2` to run the discovered Python suite in two isolated
processes, as CI does; the default is sequential and the maximum is four.
`scripts/run_tests.py` partitions test identities and requires every assigned test
to execute exactly once. Missing receipts, worker failures, skips and discovery
errors fail the stage before kernel replay. Logs, assignments and aggregate
execution receipts go beneath `CLAFER_TEST_EVIDENCE` (default system temporary
directory), outside source; CI retains them with IntentBond evidence. Writable
Alloy runtimes and comparison outputs are isolated per worker. This parallelizes
execution without caching test verdicts or reducing candidate enumeration.

## Tickets and pull requests

Public contributors can use the GitHub website throughout; private Project
access is not required:

1. Find or open a public issue with the intended outcome and validation criteria.
2. Fork the repository and create a topic branch. Retain the starting commit
   before editing; add `upstream` pointing to `https://github.com/kbak/clafer-semantics.git`
   if you need to compare with the project's main branch.
3. Make the change, keeping affected requirements and trace links consistent, and
   run the validation wrapper above against that retained baseline.
4. Open a PR from the fork to `kbak/clafer-semantics:main`, linking the issue and
   reporting the actual validation result and evidence. A maintainer handles
   Project membership and status.

Agents use the same public route. Authenticate `gh` for public issue operations
and use the helper's explicit `--no-project` mode when Project access is absent:

```sh
python3 scripts/tickets.py list
python3 scripts/tickets.py create --title 'Explain a worked model' --body-file /tmp/issue.md --no-project
python3 scripts/tickets.py comment 1 --body-file /tmp/progress.md
```

Replace the example issue number with the actual one. `close --no-project` is
also available when the caller has permission to close the issue and its
acceptance criteria are met. Public-operation errors still fail the command.

Maintainers with Project access use the default helper mode, which adds issues
to the Project and updates its Status field. For that mode, authenticate `gh`
with repository and Project permissions. Use `track N --status in-progress`
when starting, and `track` to reconcile a public-only issue or repair membership
after a partial creation failure. A Project failure in default mode is still
reported as a failure. GitHub-hosted issue/PR status and the Project should agree;
link implementation PRs with `Closes #N`.

Use a topic branch, keep changes focused, and explain what changed and how it was
checked. Include paper references and affected requirement IDs for semantic work.
Follow the [documentation policy](AGENTS.md#documentation): keep living docs
current, change comparisons in the PR, and factory evidence outside the repository.
Use the [Lean trace-link convention](docs/traceability.md) for implementation and
proof artifacts. The pinned IntentBond imports tags in Lean line, nested block
and documentation comments, preserving their source paths and physical lines.
Review must assess whether definitions match the intended semantics and whether
proofs establish the stated results; trace coverage and a successful build alone
do not establish that correspondence. The [source map](docs/sources.md) owns exact
paper correspondences, accepted corrections and audit limits; the
[product overview](docs/intent.md) owns current scope. Keep focused contracts and
trace indexes separate from those summaries, and preserve frozen change records
under their retention policy.

Contributions use the existing [MIT license](LICENSE). Preserve attribution and
check licenses before incorporating upstream code or publication material.

### Ticket readiness

Use **Todo → Ready → In Progress → Done**. Todo includes blocked or insufficiently
specified work. Ready is an actionable ticket whose hard dependencies are completed
and accepted, including dependencies in the other repository; a roadmap container
is not actionable work. Ready does not select or start a task. In Progress means
selected work has actually started. Done requires fulfilled acceptance criteria,
required review and accepted integration. A prerequisite closed as not planned is
not accepted completion.

```sh
python3 scripts/tickets.py track 123 --status ready
python3 scripts/tickets.py track 123 --status in-progress
```

The helper uses the Project's current Status/option IDs. It does not create a
missing Ready option or calculate readiness. Reconciliation is **manual**: after
acceptance, reopening, hard-dependency changes or scope decisions, inspect affected
unstarted tickets in both repositories. Promote eligible Todo tickets to Ready;
return blocked Ready tickets to Todo. Coordinate active work with its owner rather
than silently resetting In Progress. Parent/sub-issue membership groups scope;
only hard dependencies block intake. Independent Ready tasks may proceed together
with shared-file/API coordination. Without Project access, record the assessment
in public issue comments and leave board changes to a maintainer.

### Behavioral integration

The [behavioral profile contract](docs/behavioral-profile.md) owns the versioned
surface, source decisions, repository interfaces and final acceptance gates.
Start selected feature branches from `behavioral`, using `codex/behavioral-...`;
feature PRs target `behavioral` and include `Closes #N`. Capture that integration
baseline SHA explicitly for validation. CI runs full validation on PRs targeting
and pushes to `behavioral`, including documentation changes. The main branch's
existing selection policy remains unchanged.

Dependencies deliver an accepted immutable SHA, actual APIs/theorems/assumptions,
fixtures and source-matched evidence before downstream intake. Never substitute
a moving upstream branch or successful CI for semantic acceptance. Preserve the
static oracle and historical source profiles. Reconcile changes from main
deliberately and refresh affected evidence.

Require independent semantic review of the concrete diff and explicit acceptance
of profile/scope changes. Review the actual [branch controls](docs/maintenance.md#behavioral-integration-controls);
CI configuration does not install protection. After an accepted feature PR lands
on this non-default branch, close its issue explicitly with the ticket helper and
mark Done; do not assume `Closes` performed closure. Refresh affected readiness
in both repositories. The final semantics main PR waits for semantic qualification
and complete compiler qualification; the compiler then pins the actual merged
upstream SHA and requalifies. Obtain final merge authorization for those concrete
PRs. No feature ticket authorizes an early main merge or release.

## Documentation filenames

Use lowercase ASCII words or numbers separated by hyphens for maintained topic
filenames under `docs/`, with a `.md` extension: `architecture.md`, `sources.md`,
`spec.md` and `constraint-denotation.md`. The documentation checker enforces this
convention. Document titles and the [documentation map](docs/intent.md#documentation-map)
describe each document's role.

Retain conventional repository entry points and tooling names: `README.md`,
`CONTRIBUTING.md`, `SECURITY.md`, `AGENTS.md` and `CLAUDE.md`. Fixture directories
also retain their `README.md` entry points. Frozen `docs/changes/` records retain
their original names and contents; read them through the historical revision
linked from the documentation map when their relative links use former paths.

When moving a document, update maintained links and source comments together,
preserve heading anchors, artifact IDs and trace relationships, and leave
commit-pinned citations intact. Avoid aliases that differ only in case, since
those paths collide on case-insensitive filesystems. Old branch-based external
links need the current path; a commit-pinned URL retains the historical document.

## Pinned import validation prerequisites

The importer tests execute the pinned Haskell exporter as well as Lean. On Linux
x86_64, `bash scripts/check.sh` prepares it automatically in an external cache when
no exporter is configured. Install GMP headers (`libgmp-dev` on Debian/Ubuntu)
and allow the first build to download the pinned Stack, GHC and dependencies.
For explicit provisioning, build in external scratch and set `CLAFER_CAPTURE`
and `CLAFER_CAPTURE_BUILD` as described in
[the import guide](docs/resolved-import.md#build-and-replay).
Keep source archives, GHC/Stack caches, binaries and evidence outside the repository.
Setup failures fail the check; saved JSON fixtures do not substitute for compiler
execution. The shared check retains all existing module, kernel, axiom, layer and
independent-import checks.

The same Python suite runs [bounded comparison](docs/bounded-comparison.md) against
hash-pinned Alloy 6.2.0 with SAT4J and Java 17. Provisioning and bridge compilation
use an external cache; explicit tool settings are checked, with no missing-tool
skip. Comparison artifacts and minimized replays are retained externally under
`CLAFER_COMPARISON_EVIDENCE` (temporary directory by default). CI retains them
with validation evidence. Read the relation/domain and arithmetic limits before
interpreting a bounded solver result.
CI builds the same exporter from verified source/Stack archives before the check,
retaining its build identities and log with the validation evidence.
