# Try the Lean formalization

<!-- [impl->req~public-foundation~1] -->

Use [clafer.org's examples](https://www.clafer.org/p/examples.html) and
[language documentation](https://www.clafer.org/p/documentation.html) to learn
Clafer. This short walkthrough explains the Lean connection for one small model.
The formalization targets the [published SoSyM language](sources.md#primary-source);
later language extensions are outside its scope.

## Check one model

Complete the [README setup](../README.md#get-started), then run:

```sh
lake env lean Clafer/Examples/Walkthrough.lean
```

Successful checking exits without errors or output. Open the same file in VS Code
with the Lean 4 extension to inspect definitions and proof states.

The example represents:

```clafer
phone
    camera ?
```

There is one phone, with zero or one camera. In
[Walkthrough.lean](../Clafer/Examples/Walkthrough.lean), `model : EffectiveCore 3`
encodes the synthetic root, phone and camera as declaration IDs 0, 1 and 2.
The parent map records nesting; `one` and `optional` give the local cardinalities.
There are no references, inheritance or additional group restrictions.
This is a manually resolved input, not the output of a verified parser.

`configuration n` supplies a root object, one phone object and `n` distinct camera
objects with their containment links. Declaration IDs and object IDs have separate
roles even when their numbers coincide. Try the following in a temporary Lean
file under `tests/`, then remove that file after experimenting:

```lean
import Clafer.Examples.Walkthrough

open Clafer.Examples.Walkthrough Clafer.Verification

#eval check model (configuration 0) -- true
#eval check model (configuration 1) -- true
#eval check model (configuration 2) -- false
```

The file proves the three results with `by decide`, which Lean's kernel checks.
`model_valid` and `model_supported` establish the input conditions of
[`check_correct`](../Clafer/Verification/Finite.lean). Applying that theorem gives
`no_camera_satisfies`, `one_camera_satisfies` and `two_cameras_violate`: statements
about the independent `StructuralSatisfies` definition, not just Boolean outputs.
The rejected configuration has two cameras where the upper bound is one.

This checks supplied finite configurations; it does not generate configurations
or establish source-text compiler correctness. `#eval` runs the algorithm without
creating a new kernel proof of its result. Continue with the
[checker contract](structural-checker.md), or the
[complete telematics model](telematics.md) for compilation and authored constraints.

## Use as a Lake dependency

Here is a minimal separate project using a published immutable commit. This pin
provides the three public libraries; it is not a supported release. The walkthrough
above lives in this checkout and is not needed by the downstream example.

Create a directory outside this repository with these three files:

`lean-toolchain`:

```text
leanprover/lean4:v4.36.0
```

`lakefile.toml`:

```toml
name = "clafer_demo"
defaultTargets = ["Demo"]

[[require]]
name = "clafer"
git = "https://github.com/kbak/clafer-semantics.git"
rev = "9074c09e93e5e2062c8b039fb987bd8707b76727"

[[lean_lib]]
name = "Demo"
```

`Demo.lean`:

```lean
import DPGraph
import FormalCD
import Clafer

#check DPGraph.Span.red_comp
#check FormalCD.Hom
#check Clafer.Verification.check_correct
```

Run `lake update`, then `lake build` in that directory. Keep the generated
`lake-manifest.json` to retain transitive dependency identities. Mathlib's update
hook fetches its cache; if that download fails, retry `lake exe cache get` before
building, or allow a slower source build. Changing the Clafer pin may also require
changing the toolchain: read `lean-toolchain` at the selected commit.
Import only the roots needed by your project; `DPGraph` remains independent of
`FormalCD` and `Clafer`.
