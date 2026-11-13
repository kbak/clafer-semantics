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

Use Python 3.11+, the pinned Lean toolchain, Stack 3.11.1, GHC 9.12.4 and GMP headers.
On Linux x86_64, the full `bash scripts/check.sh` command provisions the pinned
0.5.8 exporter before running Python tests when neither `CLAFER_CAPTURE` nor a
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
`gsdlab/clafer@fca0deb9c766261f5c0d2ae57af4ba9b07e1279a`, SHA-256
`fcf7bf883723e7eb22ff2f3c1b6538f0c967cb5eace3a00a89f5fcd2e4a4edc5`, and
the matching claferIG archive identified below. This exact 0.5.8 revision is
marked unreleased; neither a moving branch nor a later release is admitted automatically.
Build outside the checkout:

```sh
python3 scripts/verification/build.py --archive /path/to/compiler.tar.gz \
  --ig-archive /path/to/claferIG.tar.gz \
  --stack /path/to/stack --work /path/to/scratch
export CLAFER_CAPTURE=/path/to/scratch/clafer-capture
export CLAFER_CAPTURE_BUILD=/path/to/scratch/build.json
```

The builder checks the archive, every original source before and after building,
GHC/Stack versions, original `nightly-2026-11-11` resolver and dependency lock. It
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

## Candidate build qualification

[Build/exporter qualification](https://github.com/kbak/clafer-semantics/issues/167)
supplies the selected 0.5.8 build, now used by default import and bounded
comparison. The original `0.5.8-candidate` selector remains a build alias for the
same immutable identity; its name grants no additional source admission. The
[source/profile disposition](sources.md#qualified-058-source-and-comparison-profile)
records the adopted boundaries and retained semantic differences.
Historical receipts remain unchanged; `Export057.hs` preserves the original
0.5.7 exporter bytes. `Export.hs` uses `Data.Map.Strict.toList` for the candidate's
source, consumed and implicit maps, retaining ascending UID order and the same
`clafer-generation/2` representation.

| Build input | Qualified identity |
| --- | --- |
| Compiler | `gsdlab/clafer@fca0deb9c766261f5c0d2ae57af4ba9b07e1279a` (0.5.8, marked unreleased) |
| Compiler archive SHA-256 | `fcf7bf883723e7eb22ff2f3c1b6538f0c967cb5eace3a00a89f5fcd2e4a4edc5` |
| Original source-tree SHA-256 | `c9009d0fa8fb3d834b307b6d481a0ac99aa02994ac65200a3f25a0391281be8a` |
| Stack / GHC | `3.11.1` / `9.12.4` |
| Resolver | `nightly-2026-11-11` |
| Snapshot SHA-256 | `d128a107636f374493c7cea23dde8ba9fb2235a0ba9eff15be208c43f64a4033` |
| Generated Stack lock SHA-256 | `4176b38a3b52684cb49761cfa8f98ee251c3a82ed6f03ce7c80c45125dc67b32` |
| JSON instance boundary | `gsdlab/claferIG@7942789d84939e98da38d4219cefbbd5b9e0d184` |
| claferIG archive SHA-256 | `bf8e409c6612d81545eb300a7773448faa35b1ccd20d61875f66fba73e903cdd` |

The selected Stack route uses the upstream source configuration unchanged. The
snapshot pins the remaining dependencies, including the probe's HaXml and
polyparse packages; neither `data-stringmap` nor `json-builder` is needed.
Cabal/GHC 9.6.7 support is an upstream claim, not a locally qualified build route.
The builder checks source archives/trees, Stack/GHC versions and the generated
lock before adapter compilation and checks original sources and the lock again
afterwards. Stack's archive and executable retain their existing hash checks.

The candidate build also compiles `Metadata.hs` against the unchanged claferIG
JSON generator, model and XML data modules. This exercises the real encoding
boundary without launching its solver. The build receipt includes both source
archives, the exporter and probe source/binary identities. Cache reuse checks
these identities, executable permissions and the selected build recipe. Default
settings use `CLAFER_CAPTURE` and `CLAFER_CAPTURE_BUILD`. The
original candidate selector retains `CLAFER_058_CAPTURE` and
`CLAFER_058_CAPTURE_BUILD`; both validate the same exact producer and probe.
Historical `--profile 0.5.7` uses `CLAFER_057_CAPTURE` and
`CLAFER_057_CAPTURE_BUILD` and a separate cache identity. A legacy or unreviewed
producer supplied as the current exporter fails before capture.

For automatic provisioning and qualification on Linux x86_64:

```sh
python3 scripts/verification/runtime.py \
  python3 -m unittest discover -s tests -p test_candidate_capture.py -v
```

The tests also prepare the historical 0.5.7 exporter for paired fixture comparisons.
For an explicit build, use the candidate compiler and claferIG archives above:

```sh
python3 scripts/verification/build.py --profile 0.5.8 \
  --archive /path/to/compiler.tar.gz --ig-archive /path/to/claferIG.tar.gz \
  --stack /path/to/stack --work /path/to/candidate-scratch
```

The resulting `clafer-capture input.cfr` emits the raw generation receipt;
`metadata-probe input.cfr` emits metadata, and `metadata-probe --synthetic` checks
encoder-only cases. Current `capture.py` accepts only the selected 0.5.8
manifest/build/schema combination, including the exact metadata source and IG
archive identities. The full validation suite executes live qualification and
retains fresh raw captures and metadata externally; `CLAFER_CANDIDATE_EVIDENCE`
selects their parent directory. CI retains these with the build and IntentBond
results. Missing tools or qualification failures fail validation.

The common structural fixtures compare JSON, Alloy and all UID-map lists with
live 0.5.7 exports, check deterministic repetition and validate the same strict
receipt relation. Negative cases preserve unsupported source audits and compiler
rejections. An incomplete expression can throw an upstream `ErrorCall`; the
candidate exporter forces the receipt before writing and reports `status=error`,
never a compiler rejection or a semantic verdict. The group-layout regression
checks effective bounds and exact satisfying/violating candidates without
changing Lean defaults. Qualified super paths remain rejected by the source audit;
concrete supers retain the Haskell rejection and the richer Lean source meaning.

The metadata checks preserve `.cfr-map` fields `fqName`, `lpqName`, `uid`,
`.cfr-scope` fields `lpqName`, `scope`, sorted entries, and claferIG's ordered
`ident`, `uid`, optional `super`/`reference`, `cardMin`, `cardMax`, optional `value`,
`elements` fields. Nested instances, empty collections, signed integers, alias
strings, Unicode and escaping are exercised against independent expected JSON.
Local legacy/candidate metadata comparisons match on the common source fixtures.
For arbitrary encoder inputs, backspace/form-feed change from `\b`/`\f` to
`\u0008`/`\u000c`; decoded strings are identical, but unrestricted byte equivalence
is false. Synthetic encoder cases do not extend the accepted identifier grammar,
primitive support or instance-generation scope. The [source assessment](sources.md#compiler-058-adapter-sources)
separates these local observations from upstream equivalence reports.

## Artifacts and deterministic admission

`manifest.json` uses schema `clafer-import/1`. The current adapter supports only
the following exact compiler identity; all fields must match:

| Profile | Compiler commit | Export schema | Generation receipt |
| --- | --- | --- | --- |
| 0.5.8 prerelease | `fca0deb9c766261f5c0d2ae57af4ba9b07e1279a` | `generic-aeson-0.5.8/1` | `clafer-generation/2` |

Other revisions, including 0.5.7 and 0.5.4, and mixed schemas are rejected. Historical
evidence keeps its original compiler, adapter and runtime identities. To import
or replay a historical bundle, use the repository revision and matching tools
recorded with that evidence; the [pre-upgrade adapter](https://github.com/kbak/clafer-semantics/tree/c183c1c2e4cc22cc9f41ea78733a20fc3610b50b/scripts/verification)
retains the 0.5.4 implementation. Do not relabel old captures as current evidence.
The last 0.5.7 adapter is retained at [the pre-upgrade revision](https://github.com/kbak/clafer-semantics/tree/a18890612e38872f3fb5842ed323042aea34e1ed);
replay additionally requires the exact original source snapshot recorded with
each bundle, which may predate that revision. Current regression tests execute fresh 0.5.8 captures and
reject legacy identities; paired producer checks keep the historical exporter
bytes unchanged. The downstream compiler adopts this immutable semantics API and
its comparison tools under [compiler issue #128](https://github.com/kbak/clafer-compiler-lean/issues/128),
with initializer/absence qualification remaining separately owned.
The capture manifest hashes raw bytes of `input.cfr`, `analyzed.json`, `model.als`, `generation.json`
and `build.json`, and carries explicit bounds. It does not hash itself.
The receipt retains post-analysis/post-string-pass IR, actual backend-consumed
UID map, fixed implicit registry, effective options, AST constructor/token audit,
empty string maps, exact recorded scopes, generated fragments and per-declaration backend facts.
Canonical SHA-256 hashes also identify both IR states, the consumed map,
implicit registry and source audit inside the raw-byte-hashed receipt.
Original Alloy bytes and the generated `run show for 1` command are retained,
including 0.5.7's mandatory `but 0 Name` scopes for unused abstracts. Under S,
these are precisely abstract leaf declarations without concrete descendants;
all other inferred scopes remain unsupported. Requested comparison bounds stay
independent experiment metadata.

`Export057.hs` parses once, audits the typed AST and non-parser tokens before
desugaring, compiles once, and requests `[JSON, Alloy]` in one `generate` call.
It rejects enums, initializers, assertions/goals/constraints, temporal forms,
escapes, source option directives and non-direct type expressions. The decoder
checks every constructor/field, duplicate JSON keys, scalar types, bindings and
type hierarchies, source/receipt options, root conventions and output ownership.
Unknown forms are rejected. Reference cycles do not trigger hierarchy traversal.
Parent/super cycles, dangling/reserved IDs and backend-symbol collisions fail.
Display names may repeat.
Latin-1 letters and apostrophes permitted by the pinned lexer remain intact in
display names. The adapter preserves emitted, collision-distinct UIDs,
including escaped apostrophes. UIDs use names and lexical qualification;
the receipt separately records a total UID-to-Alloy-name map, including identity
entries and the fixed registry. The adapter checks coverage, injectivity, reserved
and derived symbol collisions, and exact transport of identity-bearing IR slots.
It never reconstructs a UID from a display name or guesses a removed suffix.
The renamed backend IR, actual consumed map and source map have separate hashes.
Alloy parser/solver acceptance remains outside the import claim.

Positions are either `null` for generated syntax or exact `{start, end}` objects
with positive integer `line`/`column` coordinates and a nondecreasing exclusive end.
They are checked metadata retained in the raw IR/receipt, not semantic bounds or
identity. The single-file library API used here does not populate `inputFiles`,
so its JSON and internal IR share spans without filenames. The compiler CLI's
file-qualified spans are outside this capture schema. Import-related options
must be empty/default and source `//# OPTIONS` directives remain rejected;
multi-file loading is outside this profile.

Compiler `root`, base `clafer` and the primitive registry remain distinct.
The registry includes seven primitive IDs and routes the integer/int hierarchy
through decimal to real. This is checked registry metadata;
it does not admit primitive values. The 0.5.7 declaration modifiers include
`_finalReferences`, and references use `_refModifiers` instead of `_refModifier`.
Both new fields must be lists: known nonempty modifiers are unsupported, unknown
enums or malformed types are malformed, and mixed/extra fields are rejected.
The two additional options are fixed to `explicit_model=false` and
`decimal_digits=null`. Concrete
top-level parents become the synthetic root; abstract top-level `clafer` parents
become absent. Primitive targets are unsupported. Required effective cards use
exact integer endpoints, with only upper `-1` denoting infinity. `_glCard` and
`_isKeyword` remain compiler metadata, never authored/default evidence.

The captured source map predates optimization. Its topology, type bindings, names,
modifiers, groups and child inventories must match the emitted IR. The recorded
exceptions are the compiler's `_glCard` calculation and zeroing an unused
abstract's `[0,-1]` card to `[0,0]`; the latter is admitted only when the guarded
core has no concrete descendant. The receipt retains both records. These
exceptions identify the actual pipeline, without asserting optimizer correctness.
In 0.5.7, `generate` keeps that map when no Alloy names change, but rebuilds it
from the optimized, renamed module when any name changes. The adapter validates
this exact branch, including the synthetic root and registry. Backend observations
use the actual consumed map, while imported core rows retain source UIDs.

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
