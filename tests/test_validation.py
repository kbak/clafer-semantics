"""Docs may skip Lean only with a complete, matching source comparison."""

import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
import validation


# [itest->req~lean-validation~1]
class ValidationTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.out = Path(self.temp.name)
        self.repo = self.out / "repo"
        self.repo.mkdir()
        self.git("init", "-q")
        self.git("config", "user.name", "Validation tests")
        self.git("config", "user.email", "validation@example.invalid")
        self.write("README.md", "# Example\n")
        self.write("docs/intent.md", "# Intent\n")
        self.write("DPGraph.lean", "-- source\n")
        self.write(".gitignore", ".lake/\n")
        self.git("add", ".")
        self.git("commit", "-qm", "Baseline")
        self.base = self.git("rev-parse", "HEAD").strip()

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.repo), *args], text=True)

    def write(self, name, contents):
        path = self.repo / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(contents)
        return path

    def prepare(self, **kwargs):
        return validation.prepare(self.repo, self.base, "worktree", **kwargs)

    def test_document_edits_additions_deletions_and_renames_qualify(self):
        self.write("README.md", "# Revised\n")
        self.write("docs/nested/λ.md", "# Unicode path\n")
        (self.repo / "docs/intent.md").rename(self.repo / "docs/overview.md")
        plan = self.prepare()
        self.assertEqual(plan["mode"], "docs")
        self.assertEqual(plan["changed"], ["README.md", "docs/intent.md", "docs/nested/λ.md", "docs/overview.md"])
        self.assertEqual(plan["base"]["commit"], self.base)
        self.assertEqual(plan["candidate"]["sha256"], validation.digest(plan["candidate_manifest"]))

    def test_every_non_doc_change_requires_full_validation(self):
        # Exercise representative runtime, test, policy, dependency and asset paths;
        # additions and deletions must be treated just like edits.
        self.write("README.md", "Documentation changed\n")
        for path in ["DPGraph.lean", "tests/new.lean", "tests/new.py", "scripts/check.sh",
                     ".intentbond/scope.json", "AGENTS.md", "CONTRIBUTING.md", ".github/workflows/ci.yml",
                     "lake-manifest.json", "lean-toolchain", "docs/image.png", "docs/run.py"]:
            with self.subTest(path=path):
                target = self.repo / path
                old = target.read_bytes() if target.exists() else None
                self.write(path, "changed\n")
                self.assertEqual(self.prepare()["mode"], "full")
                target.unlink()
                if old is not None:
                    self.assertEqual(self.prepare()["mode"], "full")
                    target.write_bytes(old)

    def test_modes_symlinks_and_uncertainty_require_full_validation(self):
        target = self.write("docs/new.md", "# New\n")
        target.chmod(0o755)
        self.assertEqual(self.prepare()["mode"], "full")
        target.unlink()
        target.symlink_to("intent.md")
        self.assertEqual(self.prepare()["mode"], "full")
        target.unlink()
        self.assertEqual(self.prepare()["mode"], "full")  # Empty diff / manual CI.
        self.write("README.md", "Changed\n")
        self.assertEqual(self.prepare(force_full=True)["mode"], "full")
        self.assertEqual(validation.prepare(self.repo, "missing-ref", "worktree")["mode"], "full")
        self.assertEqual(validation.prepare(self.repo, "worktree", "worktree")["mode"], "full")
        # A changed mode alone must not disappear from the comparison.
        (self.repo / "docs/intent.md").chmod(0o755)
        self.assertEqual(self.prepare()["mode"], "full")

    def test_ignored_build_outputs_are_not_source(self):
        self.write("README.md", "Changed\n")
        self.write(".lake/generated.lean", "build artifact\n")
        self.assertEqual(self.prepare()["mode"], "docs")

    def test_snapshot_rechecks_complete_contents_and_plan_integrity(self):
        from intentbond.snapshot import snapshot
        self.write("README.md", "Changed\n")
        self.write("docs/λ.md", "Unicode path\n")
        plan = self.prepare()
        plan_path = self.out / "plan.json"
        plan_path.write_text(json.dumps(plan))
        captured = snapshot(self.repo, "worktree", self.out / "captured").root
        self.assertEqual(validation.select_snapshot(captured, plan_path)[0], "docs")
        # Changes after the initial comparison cannot reuse a docs selection.
        for name in ("DPGraph.lean", "untracked.py", "README.md"):
            with self.subTest(name=name):
                path = captured / name
                old = path.read_bytes() if path.exists() else None
                path.write_text("changed after capture\n")
                self.assertEqual(validation.select_snapshot(captured, plan_path)[0], "full")
                path.unlink()
                if old is not None:
                    path.write_bytes(old)
        (captured / "README.md").chmod(0o755)
        self.assertEqual(validation.select_snapshot(captured, plan_path)[0], "full")
        (captured / "README.md").chmod(0o644)
        for field, value in [("base_manifest", []), ("candidate_manifest", []), ("version", 42)]:
            broken = copy.deepcopy(plan)
            broken[field] = value
            plan_path.write_text(json.dumps(broken))
            self.assertEqual(validation.select_snapshot(captured, plan_path)[0], "full")
        plan_path.write_text("invalid json")
        self.assertEqual(validation.select_snapshot(captured, plan_path)[0], "full")
        self.assertEqual(validation.select_snapshot(captured, self.out / "missing")[0], "full")

    def test_plan_must_be_external_and_cli_requires_snapshot(self):
        self.write("README.md", "Changed\n")
        plan = self.prepare()
        with self.assertRaises(ValueError):
            validation.write_plan(self.repo / "plan.json", plan, self.repo)
        plan_path = self.out / "plan.json"
        validation.write_plan(plan_path, plan, self.repo)
        result = subprocess.run([sys.executable, validation.__file__, "select", "--plan", str(plan_path)],
                                cwd=self.repo, env=dict(os.environ, PROJECT_DIR=str(self.repo)),
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "full")


if __name__ == "__main__":
    unittest.main()
