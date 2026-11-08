# Bounded comparison fixtures

These small structural sources are original MIT-licensed repository fixtures.
They isolate the [comparison contract](../../../docs/resolved-ir-comparison.md)
E1–E14 obligations. Existing imported upstream examples retain their separate
[MIT notice](../importer/LICENSE-upstream). Compiler release notes motivate tests;
injected mutations are not allegations of compiler defects.

`bag.cfr` and `set.cfr` differ only in reference mode. Distinct reference heads
pointing at one target test occurrence identity. `overlap.cfr` retains a raw candidate with the same object in both extents.
Both Clafer declaration disjointness and Alloy signature disjointness reject it
(`agree_violates`). No candidate admission or enumeration rule removes it.
Runtime captures, hashes, seeds, witnesses and minimized replays are retained
outside the repository by the executable tests.
`predicate_name.cfr` checks that a supported name containing `ib_candidate`
compares and replays without being mistaken for the added predicate itself.
`collisions.cfr` exercises the 0.5.7 name map for reserved Alloy words, names
derived for fields/lifetimes, assertion names and the harness's own auxiliary
names, plus the escaped-name collision `a'` versus `a_prime`. Candidates retain
source UIDs through renamed Alloy signatures and fields.

The JSON candidates are stable, original MIT-licensed regression inputs:
`unrelated-overlap.json` preserves the #52 counterexample as a shared semantic
violation after #87;
`omit_set_uniqueness.json`, `collapse_bag_heads.json` and `drop_cardinality.json`
are the deterministic deletion-minimal sensitivity cases paired respectively
with `set.cfr`, `bag.cfr` and `optional.cfr`. The live tests apply only the named
injected mutation, compare the original checker candidate, shrink, check equality
with these fixtures and replay the external result bundle. These fixtures contain
no execution logs or private paths. Their current UID spellings match 0.5.7;
object identities, row incidence and semantic expectations are unchanged. The
original 0.5.4 fixtures remain in the pre-upgrade repository revision.
