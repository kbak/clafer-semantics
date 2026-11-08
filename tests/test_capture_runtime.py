"""Exporter provisioning regressions; actual exports remain in test_resolved_import."""
import hashlib
import io
import os
from pathlib import Path
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts/verification"))
import runtime as r
from protocol import encoded


# [itest->req~lean-validation~1]
class CaptureRuntimeTests(unittest.TestCase):
    def setUp(self):
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        self.root = Path(scratch.name)
        self.here = self.root / "checkout/scripts/verification"
        self.here.mkdir(parents=True)
        (self.here / r.EXPORTER).write_text("exporter source")
        (self.here / "build.py").write_text("builder source")
        self.cache = self.root / "cache"
        self.work = self.cache / r.PIN
        for mock in [patch.object(r, "HERE", self.here),
                     patch.dict(os.environ, {"CLAFER_CAPTURE_CACHE": str(self.cache)}, clear=True),
                     patch.object(r.shutil, "which", return_value=None),
                     patch.object(r.platform, "system", return_value="Linux"),
                     patch.object(r.platform, "machine", return_value="x86_64")]:
            mock.start()
            self.addCleanup(mock.stop)

    def write_runtime(self, directory):
        directory.mkdir(parents=True, exist_ok=True)
        executable, build = directory / "clafer-capture", directory / "build.json"
        executable.write_text("test executable")
        executable.chmod(0o755)
        build.write_bytes(encoded(dict(schema="clafer-capture-build/1", compiler_commit=r.PIN,
            compiler_archive_sha256=r.ARCHIVE, source_tree_sha256=r.SOURCE_TREE,
            resolver="lts-22.44", ghc_version="9.6.7", stack_version="3.11.1",
            stack_lock=r.STACK_LOCK, compiler_sources_unchanged=True,
            exporter_source=r.digest((self.here / r.EXPORTER).read_bytes()),
            exporter_binary=r.digest(executable.read_bytes()))))
        return executable, build

    def test_legacy_and_unreviewed_producers_are_rejected(self):
        executable, build = self.write_runtime(self.root / "explicit")
        original = r.loads(build.read_bytes())
        for commit in ("6750e6f591b2131549122c13dee94d3d2257eaea", "0" * 40):
            build.write_bytes(encoded(dict(original, compiler_commit=commit)))
            self.assertFalse(r.valid_runtime(executable, build))
            with patch.dict(os.environ, CLAFER_CAPTURE=str(executable), CLAFER_CAPTURE_BUILD=str(build)), \
                 patch.object(r, "download") as download:
                with self.assertRaisesRegex(RuntimeError, "Configured exporter"):
                    r.prepare()
                download.assert_not_called()

    def fake_download(self, url, path, sha256):
        if path.name == "stack.tar.gz":
            with tarfile.open(path, "w:gz") as archive:
                member = tarfile.TarInfo("stack-3.11.1-linux-x86_64/stack")
                member.size = len(b"test stack")
                archive.addfile(member, io.BytesIO(b"test stack"))
        else:
            path.write_bytes(b"test compiler archive")

    def test_fresh_setup_reuse_and_changed_inputs_rebuild(self):
        # Simulate downloads/builds only; exercise the real cache/identity checks.
        with patch.object(r, "download", side_effect=self.fake_download), \
             patch.object(r, "STACK_BINARY", hashlib.sha256(b"test stack").hexdigest()), \
             patch.object(r.subprocess, "run", side_effect=lambda *a, **kw: self.write_runtime(self.work)) as build:
            first = r.prepare()
            self.assertEqual(first, (self.work / "clafer-capture", self.work / "build.json"))
            build.assert_called_once()
            self.assertEqual(r.prepare(), first)
            self.assertEqual(build.call_count, 1)
            # Both a fresh snapshot's exporter and its builder must be current.
            (self.here / r.EXPORTER).write_text("new exporter source")
            r.prepare()
            self.assertEqual(build.call_count, 2)
            (self.here / "build.py").write_text("new builder source")
            r.prepare()
            self.assertEqual(build.call_count, 3)
            first[0].write_text("corrupt executable")
            r.prepare()
            self.assertEqual(build.call_count, 4)
            first[1].write_text("invalid receipt")
            r.prepare()
            self.assertEqual(build.call_count, 5)

    def test_explicit_runtime_takes_precedence_and_invalid_runtime_fails(self):
        executable, build = self.write_runtime(self.root / "explicit")
        with patch.dict(os.environ, CLAFER_CAPTURE=str(executable), CLAFER_CAPTURE_BUILD=str(build)), \
             patch.object(r, "download") as download:
            self.assertEqual(r.prepare(), (executable, build))
            executable.write_text("changed binary")
            with self.assertRaisesRegex(RuntimeError, "Configured exporter"):
                r.prepare()
            download.assert_not_called()
        with patch.dict(os.environ, CLAFER_CAPTURE_BUILD=str(build)):
            with self.assertRaisesRegex(RuntimeError, "requires CLAFER_CAPTURE"):
                r.prepare()

    def test_small_cache_reuses_without_build_dependencies(self):
        work = self.root / "ci work"
        expected = self.write_runtime(work)
        (work / "builder.sha256").write_text(hashlib.sha256((self.here / "build.py").read_bytes()).hexdigest())
        with patch.object(r, "download") as download, patch.object(r.subprocess, "run") as build:
            self.assertEqual(r.cached_runtime(work), expected)
            self.assertEqual(r.prepare(work), expected)
            download.assert_not_called()
            build.assert_not_called()
        self.assertFalse((work / "stack-root").exists())
        self.assertFalse((work / "compiler").exists())

    def test_cache_probe_rejects_missing_stale_and_corrupt_inputs_without_setup(self):
        work = self.root / "ci"
        with patch.object(r, "prepare") as prepare, \
             patch.object(sys, "argv", ["runtime.py", "--check-cache", str(work)]):
            self.assertEqual(r.main(), 1)
            self.assertFalse(work.exists())
            executable, build = self.write_runtime(work)
            stamp = work / "builder.sha256"
            self.assertEqual(r.main(), 1)
            recipe = hashlib.sha256((self.here / "build.py").read_bytes()).hexdigest()
            stamp.write_text(recipe)
            self.assertEqual(r.main(), 0)
            for path in (executable, build, stamp, self.here / r.EXPORTER, self.here / "build.py"):
                with self.subTest(path=path):
                    original = path.read_bytes()
                    path.write_bytes(original + b"changed")
                    self.assertEqual(r.main(), 1)
                    path.write_bytes(original)
            executable.chmod(0o644)
            self.assertEqual(r.main(), 1)
            prepare.assert_not_called()

    def test_github_env_prepares_and_exports_verified_paths(self):
        work = self.root / "ci work"
        expected = self.write_runtime(work)
        output = self.root / "github-env"
        output.write_text("EXISTING=retained\n")
        with patch.dict(os.environ, GITHUB_ENV=str(output)), \
             patch.object(sys, "argv", ["runtime.py", "--github-env", str(work)]), \
             patch.object(r, "prepare", return_value=expected) as prepare, \
             patch.object(r.subprocess, "call") as child:
            self.assertEqual(r.main(), 0)
            prepare.assert_called_once_with(work)
            self.assertEqual(output.read_text(), f"EXISTING=retained\nCLAFER_CAPTURE={expected[0]}\nCLAFER_CAPTURE_BUILD={expected[1]}\n")
            child.assert_not_called()
            prepare.side_effect = RuntimeError("build failed")
            with self.assertRaisesRegex(RuntimeError, "build failed"):
                r.main()
            self.assertEqual(output.read_text().count("CLAFER_CAPTURE="), 1)
            prepare.side_effect = None
            prepare.return_value = (Path("bad\nINJECTED=value"), expected[1])
            with self.assertRaisesRegex(RuntimeError, "newlines"):
                r.main()
            self.assertNotIn("INJECTED", output.read_text())

    def test_ci_commands_reject_in_tree_paths_and_missing_environment(self):
        for command in ("--check-cache", "--github-env"):
            with patch.object(sys, "argv", ["runtime.py", command, str(self.here / "cache")]):
                with self.assertRaisesRegex(RuntimeError, "outside the repository"):
                    r.main()
        with patch.object(sys, "argv", ["runtime.py", "--github-env", str(self.work)]), \
             patch.object(r, "prepare") as prepare:
            with self.assertRaisesRegex(RuntimeError, "requires GITHUB_ENV"):
                r.main()
            prepare.assert_not_called()

    def test_path_runtime_and_default_cache_without_exporter_variables(self):
        executable, build = self.write_runtime(self.root / "path")
        with patch.object(r.shutil, "which", return_value=str(executable)):
            self.assertEqual(r.prepare(), (executable, build))
        with patch.dict(os.environ, {"XDG_CACHE_HOME": str(self.root / "xdg")}, clear=True), \
             patch.object(r, "download", side_effect=RuntimeError("stop before network")):
            with self.assertRaisesRegex(RuntimeError, "stop before network"):
                r.prepare()
            self.assertTrue((self.root / "xdg/clafer-capture" / r.PIN).is_dir())

    def test_failed_build_and_in_tree_cache_do_not_run_tests(self):
        with patch.object(r, "download", side_effect=OSError("network failed")), \
             patch.object(r.subprocess, "call") as child, \
             patch.object(sys, "argv", ["runtime.py", "test-command"]):
            with self.assertRaisesRegex(OSError, "network failed"):
                r.main()
            child.assert_not_called()
        with patch.dict(os.environ, CLAFER_CAPTURE_CACHE=str(self.here / "cache")):
            with self.assertRaisesRegex(RuntimeError, "outside the repository"):
                r.prepare()

    def test_download_hash_failure_cannot_replace_cached_archive(self):
        archive = self.root / "archive"
        archive.write_bytes(b"old")
        expected = hashlib.sha256(b"good").hexdigest()
        with patch.object(r, "urlopen", return_value=io.BytesIO(b"wrong")):
            with self.assertRaisesRegex(RuntimeError, "Archive hash mismatch"):
                r.download("https://example.test/archive", archive, expected)
        self.assertEqual(archive.read_bytes(), b"old")
        with patch.object(r, "urlopen", return_value=io.BytesIO(b"good")):
            r.download("https://example.test/archive", archive, expected)
        with patch.object(r, "urlopen") as network:
            r.download("https://example.test/archive", archive, expected)
            network.assert_not_called()

    def test_runner_passes_paths_and_preserves_test_exit_status(self):
        executable, build = self.write_runtime(self.root / "explicit")
        with patch.object(r, "prepare", return_value=(executable, build)), \
             patch.object(sys, "argv", ["runtime.py", "runner", "arg with spaces"]), \
             patch.object(r.subprocess, "call", return_value=23) as child:
            self.assertEqual(r.main(), 23)
            self.assertEqual(child.call_args.args, (["runner", "arg with spaces"],))
            self.assertEqual(child.call_args.kwargs["env"]["CLAFER_CAPTURE"], str(executable))
            self.assertEqual(child.call_args.kwargs["env"]["CLAFER_CAPTURE_BUILD"], str(build))


if __name__ == "__main__":
    unittest.main()
