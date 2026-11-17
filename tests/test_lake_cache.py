"""Exercise native cache reuse and invalidation across fresh source snapshots."""

import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest


REPO = Path(__file__).resolve().parent.parent


# [itest->req~lean-validation~1]
class LakeCacheTest(unittest.TestCase):
    def test_unchanged_reuse_changed_dependency_rejection_and_fresh_override(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            env = dict(os.environ, LAKE_CACHE_DIR=str(root / "cache"),
                       LAKE_ARTIFACT_CACHE="true", LAKE_RESTORE_ARTIFACTS="true",
                       LEAN_NUM_THREADS="2")
            # The suite itself runs under `lake env`; keep its project modules
            # out of the fixture's search path and recursive kernel inventory.
            env.pop("LEAN_PATH", None)
            env.pop("LEAN_SRC_PATH", None)
            # Use the production package/options/cache policy, without fetching
            # Mathlib: this small fixture only needs the pinned Lean toolchain.
            config = re.sub(r"\[\[require\]\].*?(?=\[\[lean_lib\]\])", "",
                            (REPO / "lakefile.toml").read_text(), flags=re.S)

            def snapshot(name, value=1):
                repo = root / name
                repo.mkdir()
                (repo / "lean-toolchain").write_text((REPO / "lean-toolchain").read_text())
                (repo / "lakefile.toml").write_text(config)
                for module in ("DPGraph", "FormalCD", "Clafer"):
                    (repo / module).mkdir()
                (repo / "DPGraph.lean").write_text(
                    f"module\n@[expose] public def cacheFixture : Nat := {value}\n")
                (repo / "FormalCD.lean").write_text(
                    "module\npublic import DPGraph\n"
                    "public theorem cacheFixture_correct : cacheFixture = 1 := rfl\n")
                (repo / "Clafer.lean").write_text("module\npublic import FormalCD\n")
                return repo

            def run(repo, *args, cache=True):
                return subprocess.run(
                    ["lake", *args], cwd=repo,
                    env=dict(env, LAKE_ARTIFACT_CACHE="true" if cache else "false"),
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    text=True, check=False, timeout=60,
                )

            cold = run(snapshot("cold"), "build")
            self.assertEqual(cold.returncode, 0, cold.stdout)
            self.assertIn("Built FormalCD", cold.stdout)

            warm_repo = snapshot("warm")
            warm = run(warm_repo, "build")
            self.assertEqual(warm.returncode, 0, warm.stdout)
            for module in ("DPGraph", "FormalCD", "Clafer"):
                self.assertNotIn(f"Built {module}", warm.stdout)
                self.assertTrue((warm_repo / f".lake/build/lib/lean/{module}.olean").is_file())
            kernel = run(warm_repo, "env", "lean", "-j", "2", "--run", str(REPO / "tests/leanchecker.lean"), "--verbose",
                         "DPGraph", "FormalCD", "Clafer")
            self.assertEqual(kernel.returncode, 0, kernel.stdout)
            self.assertEqual(set(re.findall(r"^replaying (\S+)$", kernel.stdout, re.M)),
                             {"DPGraph", "FormalCD", "Clafer"})

            # Same dependent source, changed imported definition: an old valid
            # artifact must not hide that rfl is now an invalid proof.
            changed = run(snapshot("changed", value=2), "build")
            self.assertNotEqual(changed.returncode, 0, changed.stdout)
            self.assertIn("Built DPGraph", changed.stdout)
            self.assertIn("FormalCD.lean", changed.stdout)

            options_repo = snapshot("options")
            (options_repo / "lakefile.toml").write_text(
                config.replace("warningAsError = true", "warningAsError = false"))
            options = run(options_repo, "build")
            self.assertEqual(options.returncode, 0, options.stdout)
            self.assertIn("Built DPGraph", options.stdout)

            fresh = run(snapshot("fresh"), "build", cache=False)
            self.assertEqual(fresh.returncode, 0, fresh.stdout)
            for module in ("DPGraph", "FormalCD", "Clafer"):
                self.assertIn(f"Built {module}", fresh.stdout)


if __name__ == "__main__":
    unittest.main()
