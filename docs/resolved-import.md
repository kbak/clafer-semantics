# Pinned resolved import

The importer checks resolved compiler JSON inside
`Clafer/Verification/`, with external capture/protocol code under
`scripts/verification/`, as specified in the
[resolved-import issue](https://github.com/kbak/clafer-semantics/issues/51). It targets the accepted S fragment in the
[comparison contract](resolved-ir-comparison.md), using the
[effective core and finite checker](structural-checker.md). The [bounded comparison
harness](bounded-comparison.md) supplies candidate pinning, scoped solver execution,
command replacement and replay; these remain outside the importer theorem. Broader Appendix 6
realization does not enlarge the import whitelist.

## Build and replay

Use Python 3.11+, the pinned Lean toolchain, Stack 3.11.1, GHC 9.6.7 and GMP headers.
On Linux x86_64, the full `bash scripts/check.sh` command provisions the pinned
exporter before running Python tests when neither `CLAFER_CAPTURE` nor a
`clafer-capture` executable on `PATH` is supplied. Install `libgmp-dev` first on
Debian/Ubuntu. Automatic setup downloads hash-checked compiler and Stack archives
and runs the builder below, which obtains the pinned GHC and dependencies.

It uses `$XDG_CACHE_HOME/clafer-capture` (default `~/.cache/clafer-capture`);
`CLAFER_CAPTURE_CACHE` selects another directory outside the repository.
Build logs and identities remain there. Fresh validation snapshots use the same
cache, checking exporter source/binary and compiler/dependency identities before
reuse; a changed builder or exporter rebuilds it. Setup failure stops validation.

The wrapper passes the exporter and build record to the test process, so it does
not depend on environment variables exported by an earlier interactive session.
Explicit exporter settings are checked and take precedence; an invalid explicit
setting fails rather than selecting another producer. Other platforms require
explicit provisioning.

To build explicitly or use the capture commands independently:

Obtain the compiler source archive for
`gsdlab/clafer@6750e6f591b2131549122c13dee94d3d2257eaea`, SHA-256
`2b9e111e21d979ff331816161738df9b07417658f788e0939f31b84292cae74f`.
Build outside the checkout:

```sh
python3 scripts/verification/build.py --archive /path/to/compiler.tar.gz \
  --stack /path/to/stack --work /path/to/scratch
export CLAFER_CAPTURE=/path/to/scratch/clafer-capture
export CLAFER_CAPTURE_BUILD=/path/to/scratch/build.json
```

The builder checks the archive, every original source before and after building,
GHC/Stack versions, original `lts-22.44` resolver and Git dependency pins. It
retains the source-tree digest, original generated lockfile digest, exporter
source/binary digests and build log. The compiler library sources remain unchanged.
An observational copy of `Generator/Alloy.hs` exposes its private helpers by
changing only the module header; its MIT header remains intact. The exporter
compares the complete assembly of that observer's fragments with the original
library's emitted Alloy. This is executable extraction validation, not a proof
of the Haskell generator.

Supply a JSON bounds object mapping **every** user UID to a natural bound and
`root` to 1. Bounds are explicit experiment metadata; they are not inferred from
`_glCard`, and no claim of their adequacy for a solver follows.

```sh
python3 scripts/verification/capture.py capture model.cfr /path/to/new-bundle \
  --exporter "$CLAFER_CAPTURE" --build "$CLAFER_CAPTURE_BUILD" \
  --bounds bounds.json
python3 scripts/verification/capture.py import /path/to/new-bundle
python3 scripts/verification/capture.py import /path/to/new-bundle --candidate candidate.json
bash scripts/check.sh
```

Full validation prepares or checks the exporter above. Python tests run actual pinned
exports and Lean admission, plus deterministic malformed/unsupported mutations;
no missing-compiler skip is treated as a pass. Test fixtures retain upstream MIT
attribution. The cached ordinary compiler CLI can additionally exercise exports;
its separate output files cannot establish a generation receipt.

## Artifacts and deterministic admission

`manifest.json` uses schema `clafer-import/1`, export schema
`generic-aeson-0.5.4/1`, compiler version `0.5.4` and the exact commit above.
Older compiler/export identities are rejected. Replay historical bundles with
their original source-matched adapter/runtime, or capture new bundles with 0.5.4;
do not relabel historical evidence as a new compiler run.
It hashes raw bytes of `input.cfr`, `analyzed.json`, `model.als`, `generation.json`
and `build.json`, and carries explicit bounds. It does not hash itself.
The receipt retains post-analysis/post-string-pass IR, actual backend-consumed
UID map, fixed implicit registry, effective options, AST constructor/token audit,
empty string maps/scopes, generated fragments and per-declaration backend facts.
Canonical SHA-256 hashes also identify both IR states, the consumed map,
implicit registry and source audit inside the raw-byte-hashed receipt.
Original Alloy bytes and its inert `run show for 1` command are retained.

`Export.hs` parses once, audits the typed AST and non-parser tokens before
desugaring, compiles once, and requests `[JSON, Alloy]` in one `generate` call.
It rejects enums, initializers, assertions/goals/constraints, temporal forms,
escapes, source option directives and non-direct type expressions. The decoder
checks every constructor/field, duplicate JSON keys, scalar types, bindings and
type hierarchies, source/receipt options, root conventions and output ownership.
Unknown forms are rejected. Reference cycles do not trigger hierarchy traversal.
Parent/super cycles, dangling/reserved IDs and backend-symbol collisions fail.
Display names may repeat.
Latin-1 letters and apostrophes permitted by the pinned lexer remain intact in
display names. The compiler replaces UID apostrophes with `__prime__` and assigns
distinct counters when that spelling collides with a literal name. The importer
preserves those emitted UIDs and backend symbols without deriving them from names.
Alloy parser/solver acceptance remains outside the import claim.

Positions are either `null` for generated syntax or exact `{start, end}` objects
with positive integer `line`/`column` coordinates and a nondecreasing exclusive end.
They are checked metadata retained in the raw IR/receipt, not semantic bounds or
identity. The single-file library API used here does not populate `inputFiles`,
so its JSON and internal IR share spans without filenames. The compiler CLI's
file-qualified spans are outside this capture schema. Import-related options
must be empty/default and source `//# OPTIONS` directives remain rejected;
multi-file loading is outside this profile.

Compiler `root`, base `clafer` and six primitive IDs remain distinct. Concrete
top-level parents become the synthetic root; abstract top-level `clafer` parents
become absent. Primitive targets are unsupported. Required effective cards use
exact integer endpoints, with only upper `-1` denoting infinity. `_glCard` and
`_isKeyword` remain compiler metadata, never authored/default evidence.

The consumed map predates optimization. Its topology, type bindings, names,
modifiers, groups and child inventories must match the emitted IR. The recorded
exceptions are the compiler's `_glCard` calculation and zeroing an unused
abstract's `[0,-1]` card to `[0,0]`; the latter is admitted only when the guarded
core has no concrete descendant. The receipt retains both records. These
exceptions identify the actual pipeline, without asserting optimizer correctness.

External failure categories are `malformed`, `unsupported`, `compiler_rejected`
and `error`. No failed import gets a semantic verdict. Lean independently checks
field preservation, UID uniqueness, interval encodings, ranks and the supported-fragment
certificate before `verify`. Candidate failures retain the [checker](structural-checker.md)'s `malformed`,
`satisfies` and `violates` distinction.

## Representation and proof boundary

`Import.Row` retains UIDs as strings and names as separate metadata. The imported
inventory inserts exactly one synthetic root at index zero. Numeric `DeclId`s
are finite indices; the UID dictionary is explicit and checked injective.
`Represents` relates every ID, root, parent, super, reference mode/target,
abstract flag, name and interval to a semantic `EffectiveCore`. It requires exact
recovery of original UID edges and bound encodings, so failed lookups or invalid
sentinels cannot disappear during normalization.

`admit` checks `bindingChecks`, `coreChecks` and `supportChecks` as data. Successful
admission yields `Accepted.wellFormed`, `Accepted.supported` and
`Accepted.represents`. `uid_identity` proves that distinct UIDs cannot merge even
when names repeat. `representation_unique` proves fieldwise representation
uniquely determines the effective core. `normalization_correspondence` then
preserves independent `StructuralSatisfies` for arbitrary configurations.
`imported_check_correct` and `imported_verify_correct` compose this with
[checker correctness](structural-checker.md). These are semantic statements, not serialization roundtrips.
The existing span and compiled-bank bridges identify the selected interpretation.

Candidate JSON uses natural object labels and string class UIDs. `members` rows
are `[uid, object]`; containment/reference rows are `[uid, [source, target]]`.
`translate_represents` proves a fieldwise `CandidateRepresents` relation using
ordered row correspondence. The translation keeps object labels, including distinct reference
head occurrences with equal parent/target pairs. It never resolves display names
or turns a repeated target into one occurrence. Malformed ordinary duplicate rows
are rejected by the existing protocol; typed structural failures are violations.

The unproved boundary includes the source parser/default/resolver/optimizer,
Haskell capture and observer, Python JSON decoder/protocol/SHA-256 operations,
Lean JSON parsing, compiler/runtime execution and extraction from bytes to typed
records. Hashes bind artifact bytes, not producer authenticity. A forged bundle
is not evidence of a genuine compiler execution merely because its hashes agree.
The reviewed capture program and source-matched execution evidence establish
that provenance. No source-program preservation, authored provenance, native
per-verdict proof certificate, Alloy equivalence or solver result is claimed.

The supported command is `capture.py`. `ImportMain.lean` is its internal adapter
for canonical decoded records, not an alternative compiler-JSON entry point.
Duplicate-key rejection happens in the Python byte parser before canonical
serialization; direct use of Lean's JSON parser does not provide that guarantee.
