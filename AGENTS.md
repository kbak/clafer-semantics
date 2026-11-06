# Working on Clafer Semantics

The repository is `kbak/clafer-semantics`; its single Lake package is `clafer`.
The sibling public roots are `DPGraph`, `FormalCD` and `Clafer`, with permitted
dependencies `Clafer -> FormalCD -> DPGraph -> Mathlib`. Keep DPGraph independently
importable and new Lean modules under their owning root.

Read the canonical [intent and documentation map](docs/intent.md),
[architecture](docs/architecture.md), affected [requirements](docs/spec.md), and
[source map](docs/sources.md) before extending a layer. They own current scope,
contracts, paper correspondences and accepted corrections. [Roadmap #2](https://github.com/kbak/clafer-semantics/issues/2)
and [design #13](https://github.com/kbak/clafer-semantics/issues/13) retain decision history.

Preserve the semantic boundaries: full graph bindings, literal bag keys and
argument totality are separate; bounded syntactic self-description does not imply
semantic self-instantiation; VC is a FormalCD extension. Role identities,
resolved referents and names are distinct. Gluing uses equal referents with
incidence/metadata consistency and complete effective defaults for FormalCD
validity. Follow the [Compile contract](docs/compile.md), including positive map
support, and the focused contracts linked from intent for groups, inherited
realization, constraint meanings and finite verification.

Every agent must use [IntentBond](https://github.com/kbak/intentbond) for planning,
implementation, and review. Read the development skill and its relevant references
from the revision pinned in [requirements/intentbond.txt](requirements/intentbond.txt):
[IntentBond skill](https://github.com/kbak/intentbond/blob/f9b4f9e40722dc6a83067ac9e62480159322dd09/intentbond/skills/intentbond/SKILL.md).
Use the installed package's matching skill when available. If tooling is missing,
follow [CONTRIBUTING.md](CONTRIBUTING.md); report a concrete blocker instead of
silently skipping IntentBond.

Read [intent](docs/intent.md), the affected [requirements](docs/spec.md), and
[scope.json](scope.json). Capture the starting Git commit before editing. Maintain
affected requirements, source references, implementation, proofs/tests, and trace
links together. Run `ib check` before handoff and retain its evidence. Exit 4
means automated checks passed with semantic review pending; it is not approval.
For Lean definitions and proofs, follow [the Lean trace-link convention](docs/traceability.md).
The pinned IntentBond imports OFT tags from Lean comments with original source
locations. Keep tags beside the relevant implementation/proofs/tests and retain
Markdown explanations of their assumptions; review the actual declarations.
Do not weaken scope or coverage to make a change pass. Scope changes need explicit
review in the PR.

Plan work as public issues; maintainers track them in
[the private GitHub Project](https://github.com/users/kbak/projects/2).
Search existing issues before creating one. Use `python3 scripts/tickets.py` to
create, track, update, and comment on issues; `--help` lists commands. Record
scope, acceptance criteria, source sections, affected requirement IDs, dependencies,
and validation. With Project access, set In Progress when starting. Without it,
use `create --no-project` and public issue comments; leave Project updates to a
maintainer. `close --no-project` likewise leaves Project reconciliation to the
maintainer. This public contribution route also applies to agents working in forks;
private Project access is not a prerequisite. Link PRs with `Closes #N`.
Close tickets and mark Done only after their acceptance criteria are met.
In IntentMade, the credential-bearing coordinator uses its deployment ticket
wrapper. Workers return ticket updates to the coordinator; never copy GitHub
credentials into a worker.
If public GitHub access is unavailable, preserve the proposed ticket locally and
report the blocker. A planning issue alone does not authorize semantic implementation.

The SoSyM paper is the primary semantic reference; cite section/definition numbers
when adding definitions and theorems. Record ambiguities and deliberate departures
in issues before choosing a meaning. The Haskell compiler is supplementary context;
pin a commit when using it as evidence. Do not copy third-party material without
checking its license. Keep the README brief.

Use `python3 scripts/validation.py check --base BASE_COMMIT --candidate worktree
--out /external/evidence` for IntentBond validation. The wrapper selects document
checks only after comparing all source contents and modes with the frozen baseline;
the shared check revalidates the captured snapshot. Only regular Markdown changes
in `README.md` and `docs/` qualify. Other changes or uncertain comparisons require
the full check. Keep the selection record beside IntentBond evidence. Do not select
the short path by judgment, hand-write its plan, or edit scope to obtain it.
Use `--full` to require full validation; `bash scripts/check.sh` without a selection
plan also runs the full check with the pinned Lean toolchain. See
[the validation workflow](CONTRIBUTING.md#setup-and-checks).
Keep proofs kernel checked. Do not introduce `sorry`, `admit`, disabled warning checks, or unchecked
axioms as completed proofs; discuss intentional additional axioms explicitly.
Keep private deployment paths, credentials, and runtime state outside this repo.
Place new Lean modules under their owning public root. The shared check discovers
all modules (including examples and helpers) for builds, kernel checks and
import-all audits, and rejects reverse layer imports or unowned source modules.

## Documentation

Follow the [documentation filename convention](CONTRIBUTING.md#documentation-filenames)
when adding or moving maintained documents.

Maintain current product intent, architecture, mathematical explanations, source
citations, requirements and reusable agent guidance. Use [docs/intent.md](docs/intent.md)
as the canonical overview and link to authoritative documents rather than
duplicating them. Put before/after explanations in PR descriptions and acceptance
and execution evidence in external factory artifacts. Keep transcripts, conversation
and run IDs, execution diaries and handoff reports out of living docs; preserve
source commits and hashes used as citations. Obey controller retention requirements:
keep frozen package snapshots unchanged and required plans concise and current
until the retention policy permits removal.
