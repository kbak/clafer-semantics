# Clafer Semantics

<!-- [impl->req~public-foundation~1] -->

[![CI](https://github.com/kbak/clafer-semantics/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/kbak/clafer-semantics/actions/workflows/ci.yml)
[![Ask DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/kbak/clafer-semantics)

**A [Lean 4](https://lean-lang.org/) formalization of Clafer's modeling semantics.**
[Clafer](https://www.clafer.org/) combines class modeling, feature modeling, and
constraints in one language for describing families of systems, their valid
configurations, and their behavior over time. This project turns definitions from
the structural and behavioral Clafer papers, with the documented corrections,
into precise mathematical objects and machine-checked proofs.

Use it to study the semantics, inspect worked models, or build on reusable graph
and class-diagram foundations. The focus is the connection between a model's
structure, its constraints, and the configurations and histories that satisfy them.
Start with [From structure to behavior](docs/structure-and-behavior.md) for a
conceptual guide with diagrams, shared identities, lifetimes, and temporal obligations.

[Overview and documentation](docs/intent.md) · [Contributing](CONTRIBUTING.md) ·
[Roadmap](docs/architecture.md#roadmap-and-validation-accounting) · [MIT license](LICENSE)

## What is here?

The `clafer` Lake package provides three public Lean libraries:

| Import | What it provides |
| --- | --- |
| `DPGraph` | Graphs with predicates, link-preserving spans, model restriction, and conditional model transport and amalgamation results |
| `FormalCD` | Class diagrams with names and defaults, structure-preserving mappings, and the paper's metamodel and telematics example |
| `Clafer` | Resolved syntax, typed constraints and their core meanings, structural compilation and gluing, and a verified finite structural candidate checker |

Dependencies flow `Clafer → FormalCD → DPGraph → Mathlib`; `DPGraph` is independently
importable. The [architecture](docs/architecture.md) explains these boundaries.
The optional `Clafer.Behavioral` entry point adds infinite traces, temporal
constraint meanings, and their structural correspondence.

The [Telematics case study](docs/telematics.md) connects a complete, manually resolved
telematics model to compilation and a concrete satisfying interpretation,
including all twelve constraint bodies. Its proof establishes that particular
model under the documented formalization choices. General source-text compiler
correctness, a production parser, configuration generation, and general solver
integration are outside the delivered scope. A [bounded Alloy comparison harness](docs/bounded-comparison.md)
tests the [finite checker's supported fragment](docs/structural-checker.md);
it does not establish universal compiler correctness. See the [current scope](docs/intent.md).

## Get started

Install Git and [Lean via elan](https://lean-lang.org/install/), then:

```sh
git clone https://github.com/kbak/clafer-semantics.git
cd clafer-semantics
lake exe cache get
lake build
```

Elan selects the pinned [Lean toolchain](lean-toolchain); Lake fetches the pinned
Mathlib dependency. The cache command downloads precompiled Mathlib files; allow
disk space and time for that first download. If the cache is unavailable,
`lake build` can compile the pinned sources instead, which takes longer.
For editor support, open the checkout with the Lean 4 extension for VS Code.

Follow the [small Lean walkthrough](docs/getting-started.md): a phone with an
optional camera, two satisfying configurations and one rejected configuration.
After building, check its proofs with:

```sh
lake env lean Clafer/Examples/Walkthrough.lean
```

For language syntax and more models, use [clafer.org's examples](https://www.clafer.org/p/examples.html).
Then explore [spans](DPGraph/Span/Examples.lean), [class diagrams](FormalCD/Examples.lean),
[compilation and gluing](docs/representative-models.md), or the
[complete telematics model](docs/telematics.md). The
[documentation map](docs/intent.md#documentation-map) leads to detailed contracts,
source citations, and proof indexes. The walkthrough also shows
[use from another Lake project](docs/getting-started.md#use-as-a-lake-dependency).
Full validation has additional [prerequisites](CONTRIBUTING.md#setup-and-checks);
building these Lean examples does not require Java, Haskell or Alloy.

## Contribute

Questions, bug reports, documentation improvements, and small proof contributions
are welcome. Start with the [issues](https://github.com/kbak/clafer-semantics/issues)
and [contribution guide](CONTRIBUTING.md). Discuss semantic changes in an issue
before implementation, identifying the relevant paper sections and acceptance criteria.

The full validation command is `bash scripts/check.sh`; follow the
[setup instructions](CONTRIBUTING.md#setup-and-checks) for its prerequisites and
the required [IntentBond](https://github.com/kbak/intentbond) check. Validation
builds every project module, replays proofs through Lean's kernel checker, audits
axioms, and runs regression tests. IntentBond connects requirements to artifacts
and retains evidence; semantic review remains necessary.

[AGENTS.md](AGENTS.md) also applies to agent contributions. Work is tracked in the
public issues; maintainers also use a
[private GitHub Project](https://github.com/users/kbak/projects/2).
For sensitive reports, follow the [security policy](SECURITY.md).

## References and license

To cite the formalization, use [CITATION.cff](CITATION.cff) and include the Git
commit used. The [snapshot and review policy](docs/maintenance.md#research-snapshots)
describes how reviewed source revisions are recorded.

The primary semantic references are:

- *Clafer: unifying class and feature modeling*, Software & Systems Modeling
  **15, 811–845 (2016)**; published online in 2014,
  [DOI: 10.1007/s10270-014-0441-1](https://doi.org/10.1007/s10270-014-0441-1)
  ([author preprint for free access](https://gsd.uwaterloo.ca/sites/default/files/2014-Bak-Clafer-Unifying-Class-Feature-Modeling%28SOSYM%29.pdf)).
- *Clafer: Lightweight Modeling of Structure, Behaviour, and Variability*,
  The Art, Science, and Engineering of Programming **3(1), article 2 (2019)**,
  [DOI: 10.22152/programming-journal.org/2019/3/2](https://doi.org/10.22152/programming-journal.org/2019/3/2)
  ([free article](https://arxiv.org/abs/1807.08576v1)).

Read the [structural corrections and clarifications](docs/sosym-errata.md) and
the [behavioral profile](docs/behavioral-profile.md) alongside the papers;
the [source map](docs/sources.md) records exact correspondences and accepted choices.
The maintained [Haskell implementation](https://github.com/gsdlab/clafer/)
provides supplementary context and the existing Clafer toolchain.

[MIT licensed](LICENSE). Referenced publications and upstream code retain their
own licenses.
