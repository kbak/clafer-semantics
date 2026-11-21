"""Exercise exact approved scope migrations; reject unrelated policy drift."""

from copy import deepcopy
import json
from pathlib import Path
import unittest

from scripts.ci_scope import (
    canonical, digest, MIGRATED_SHA256, ORIGINAL_SHA256, RENAMED_SHA256, select_scope,
)

# Historical bytes are intentional: the migration must cover the original layout.
BASELINE = b'{\n  "schema_version": 1,\n  "name": "clafer-lean",\n  "inputs": ["README.md", "AGENTS.md", "CLAUDE.md", "CONTRIBUTING.md", "SECURITY.md", "docs", "ClaferLean.lean", "ClaferLean", "lakefile.toml", "lake-manifest.json", "lean-toolchain", "scripts", "tests", "requirements", ".github", "scope.json"],\n  "specification_paths": ["docs", "README.md", "CONTRIBUTING.md", "AGENTS.md", "CLAUDE.md", "SECURITY.md"],\n  "test_paths": ["scripts/check.sh", "tests"],\n  "review_paths": ["ClaferLean.lean", "ClaferLean", "lakefile.toml", "lake-manifest.json", "lean-toolchain", "scripts", "requirements", ".github", "scope.json"],\n  "required_coverage": {"intent": ["req"], "req": ["impl"]},\n  "policy": {"require_revision_increase": false, "allow_skipped_tests": false},\n  "tests": {\n    "format": "command",\n    "command": ["bash", "scripts/check.sh"],\n    "timeout_seconds": 900\n  }\n}\n'


class ScopeMigrationTest(unittest.TestCase):
    def setUp(self):
        self.original = json.loads(BASELINE)
        self.expanded = deepcopy(self.original)
        self.expanded.update(inputs=["."], review_paths=["."])
        self.candidate = (json.dumps(self.expanded, indent=2) + "\n").encode()
        self.renamed = dict(self.expanded, name="clafer-semantics")
        self.renamed_bytes = (json.dumps(self.renamed, indent=2) + "\n").encode()

    def test_exact_migration_preserves_all_other_fields(self):
        self.assertEqual(digest(BASELINE), ORIGINAL_SHA256)
        selected = select_scope(BASELINE, self.candidate)
        self.assertEqual(digest(selected), MIGRATED_SHA256)
        self.assertEqual(canonical(selected), "4547b647f0892bd3c354c0c55ab4bd65f0ce54827fe810534206dd8a49448895")
        for key in self.original.keys() - {"inputs", "review_paths"}:
            self.assertEqual(json.loads(selected)[key], self.original[key])

    def test_exact_project_rename_preserves_all_validation_obligations(self):
        selected = select_scope(self.candidate, self.renamed_bytes)
        self.assertEqual(digest(selected), RENAMED_SHA256)
        for key in self.expanded.keys() - {"name"}:
            self.assertEqual(json.loads(selected)[key], self.expanded[key])
        self.assertEqual(selected, (Path(__file__).resolve().parent.parent / ".intentbond/scope.json").read_bytes())

    def test_project_rename_rejects_each_additional_policy_change(self):
        for key in self.renamed:
            with self.subTest(key=key):
                changed = deepcopy(self.renamed)
                del changed[key]
                with self.assertRaisesRegex(ValueError, "unapproved scope change"):
                    select_scope(self.candidate, (json.dumps(changed, indent=2) + "\n").encode())
        for key, value in [("timeout_seconds", 901), ("command", ["true"]),
                           ("format", "junit")]:
            with self.subTest(test_policy=key):
                changed = deepcopy(self.renamed)
                changed["tests"][key] = value
                with self.assertRaises(ValueError):
                    select_scope(self.candidate, (json.dumps(changed, indent=2) + "\n").encode())
        for baseline, candidate in [
            (self.candidate + b"\n", self.renamed_bytes),
            (self.candidate, self.renamed_bytes + b"\n"),
            (self.renamed_bytes, self.candidate),
            (BASELINE, self.renamed_bytes),
        ]:
            with self.subTest(baseline_digest=digest(baseline)), self.assertRaises(ValueError):
                select_scope(baseline, candidate)

    def test_unchanged_baseline_policy_and_post_migration_are_retained(self):
        for policy in [BASELINE, self.candidate, self.renamed_bytes]:
            self.assertEqual(select_scope(policy, policy), policy)

    def test_each_unapproved_field_change_is_rejected(self):
        for key in self.expanded:
            with self.subTest(key=key):
                changed = deepcopy(self.expanded)
                del changed[key]
                with self.assertRaisesRegex(ValueError, "unapproved scope change"):
                    select_scope(BASELINE, json.dumps(changed).encode())
        for key, value in [("timeout_seconds", 901), ("command", ["true"]), ("format", "junit")]:
            with self.subTest(test_policy=key):
                changed = deepcopy(self.expanded)
                changed["tests"][key] = value
                with self.assertRaises(ValueError):
                    select_scope(BASELINE, (json.dumps(changed, indent=2) + "\n").encode())
        for policy in [{"require_revision_increase": False, "allow_skipped_tests": True}, {}]:
            changed = deepcopy(self.expanded)
            changed["policy"] = policy
            with self.assertRaises(ValueError):
                select_scope(BASELINE, (json.dumps(changed, indent=2) + "\n").encode())

    def test_unknown_baseline_partial_migration_and_reversion_are_rejected(self):
        for baseline, candidate in [(BASELINE + b"\n", self.candidate),
                                    (self.candidate, BASELINE),
                                    (BASELINE, json.dumps(dict(self.original, inputs=["."])).encode())]:
            with self.subTest(baseline_digest=digest(baseline)), self.assertRaises(ValueError):
                select_scope(baseline, candidate)


if __name__ == "__main__":
    unittest.main()
