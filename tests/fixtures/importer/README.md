# Pinned compiler import fixtures

`set_and_bag_references.cfr` is copied unchanged from
[gsdlab/clafer@6750e6f591b2131549122c13dee94d3d2257eaea](https://github.com/gsdlab/clafer/blob/6750e6f591b2131549122c13dee94d3d2257eaea/test/positive/set_and_bag_references.cfr).
Its MIT attribution is retained in `LICENSE-upstream`. Other source fixtures are
original examples for this repository. Tests execute the pinned exporter; saved
JSON files are schema/mutation examples, not substitutes for those executions.

`identities` combines duplicate display names, nesting, inheritance, an unused
abstract and a bag reference. `groups` counts child occurrences under effective
numeric bounds. `cycles` keeps reference cycles; `empty` imports only the root.
`spellings` retains Latin-1 letters and apostrophes in display names, with escaped
UIDs and collisions between apostrophes and literal `__prime__` names.
`analyzed.json` is recaptured from 0.5.4; a live-export assertion keeps it aligned.
See [the import protocol](../../../docs/resolved-import.md) for replay and trust
boundaries. Malformed/unsupported cases are deterministic mutations in
`tests/test_resolved_import.py`, including every rejected tag/modifier family.
