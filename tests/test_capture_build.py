"""Build qualification rejects wrong tools, sources and dependency locks."""
import hashlib
import io
from pathlib import Path
import sys
import tarfile
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts/verification"))
import build as b
import candidate_profile as candidate
from protocol import digest, encoded, loads


# [utest->req~clafer-compiler-capture~1]
class CaptureBuildTests(unittest.TestCase):
    def setUp(self):
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        self.root = Path(scratch.name)
        self.archive = self.root / "source.tar.gz"
        self.lock = b"pinned dependency lock"
        self.files = {"src/Language/Clafer/Generator/Alloy.hs":
                      b"module Language.Clafer.Generator.Alloy (genModule) where\n",
                      "stack.yaml.lock": self.lock}
        with tarfile.open(self.archive, "w:gz") as archive:
            for name, data in self.files.items():
                member = tarfile.TarInfo("compiler/" + name)
                member.size = len(data)
                archive.addfile(member, io.BytesIO(data))
        self.profile = SimpleNamespace(NAME="0.5.8-candidate", PIN=candidate.PIN,
            ARCHIVE=hashlib.sha256(self.archive.read_bytes()).hexdigest(),
            SOURCE_TREE=hashlib.sha256(encoded({n: digest(d) for n, d in self.files.items()})).hexdigest(),
            EXPORTER=candidate.EXPORTER, RESOLVER=candidate.RESOLVER,
            GHC_VERSION=candidate.GHC_VERSION, STACK_VERSION=candidate.STACK_VERSION,
            STACK_LOCK=digest(self.lock), PACKAGES=candidate.PACKAGES)
        self.work = self.root / "work"
        self.args = ["build.py", "--archive", str(self.archive), "--stack", str(self.root / "stack"),
                     "--work", str(self.work), "--profile", candidate.NAME]
        for mock in (patch.object(sys, "argv", self.args), patch.object(b, "select", return_value=self.profile)):
            mock.start()
            self.addCleanup(mock.stop)

    def run_build(self, command, cwd, env, log):
        if "-o" in command:
            Path(command[command.index("-o") + 1]).write_bytes(b"compiled adapter")

    def test_qualified_route_and_packages_are_recorded(self):
        with patch.object(b.subprocess, "check_output", side_effect=["3.11.1\n", "9.12.4\n"]), \
             patch.object(b, "run", side_effect=self.run_build) as run, patch("builtins.print"):
            b.main()
        receipt = loads((self.work / "build.json").read_bytes())
        self.assertEqual(receipt["resolver"], "nightly-2026-11-11")
        self.assertEqual(receipt["ghc_version"], "9.12.4")
        self.assertEqual(receipt["stack_lock"], digest(self.lock))
        compile_command = run.call_args_list[-1].args[0]
        self.assertIn("containers", compile_command)
        self.assertNotIn("data-stringmap", compile_command)
        for name, data in self.files.items():
            self.assertEqual((self.work / "compiler" / name).read_bytes(), data)

    def test_wrong_tools_or_lock_never_compile(self):
        for versions, lock in ((["3.11.0"], self.lock), (["3.11.1", "9.6.7"], self.lock),
                               (["3.11.1", "9.12.4"], b"different snapshot")):
            self.profile.STACK_LOCK = digest(lock)
            with self.subTest(versions=versions, lock=lock), \
                 patch.object(b.subprocess, "check_output", side_effect=versions), patch.object(b, "run") as run:
                with self.assertRaises(RuntimeError):
                    b.main()
                run.assert_not_called()
                self.assertFalse((self.work / "build.json").exists())

    def test_changed_sources_or_lock_cannot_produce_receipt(self):
        for name in self.files:
            with self.subTest(path=name):
                def mutate(*args):
                    self.run_build(*args)
                    (self.work / "compiler" / name).write_bytes(b"modified during compilation")
                with patch.object(b.subprocess, "check_output", side_effect=["3.11.1", "9.12.4"]), \
                     patch.object(b, "run", side_effect=mutate):
                    with self.assertRaisesRegex(RuntimeError, "sources changed"):
                        b.main()
                self.assertFalse((self.work / "build.json").exists())
                with self.assertRaisesRegex(RuntimeError, "modified compiler source"):
                    b.main()
                (self.work / "compiler" / name).write_bytes(self.files[name])

    def test_wrong_archive_or_tree_is_rejected_before_tools(self):
        for field in ("ARCHIVE", "SOURCE_TREE"):
            original = getattr(self.profile, field)
            setattr(self.profile, field, "0" * 64)
            with self.subTest(field=field), patch.object(b.subprocess, "check_output") as tool:
                with self.assertRaises(RuntimeError):
                    b.main()
                tool.assert_not_called()
            setattr(self.profile, field, original)


if __name__ == "__main__":
    unittest.main()
