"""Check preflight ordering and failure propagation without provisioning Lean."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


REPO = Path(__file__).resolve().parent.parent


# [itest->req~lean-validation~1]
class CheckScriptTest(unittest.TestCase):
    def run_check(self, *, preflight=False, fail="", selection="full", jobs="1", dependencies="Mathlib.Data.Set.Defs\nMathlib.Tactic.FinCases\n"):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "scripts").mkdir()
            shutil.copyfile(REPO / "scripts/check.sh", root / "scripts/check.sh")
            (root / "bin").mkdir()
            (root / "profile").mkdir()
            (root / "profile/lean-env.sh").write_text('echo profile >> "$CALLS"\n')
            stub = '''#!/usr/bin/env bash
echo "${0##*/} $*" >> "$CALLS"
if [[ "$1" == scripts/validation.py ]]; then
  echo "$SELECTED_MODE"
fi
if [[ "$1" == scripts/project_modules.py ]]; then
  mkdir -p .lake/validation
  printf 'DPGraph\\nDPGraph.Internal.New\\nFormalCD\\nClafer\\n' > .lake/validation/modules.txt
  printf 'tests/public_imports.lean\\n' > .lake/validation/tests.txt
  printf '%s' "$PREFETCH_MODULES" > .lake/validation/mathlib-imports.txt
fi
if [[ -n "$FAIL_STEP" && "$*" == *"$FAIL_STEP"* ]]; then exit 23; fi
if [[ "$1" == scripts/verification/runtime.py ]]; then
  shift
  "$@"
fi
'''
            for name in ("python3", "lake"):
                path = root / "bin" / name
                path.write_text(stub)
                path.chmod(0o755)
            result = subprocess.run(
                ["bash", str(root / "scripts/check.sh")] + (["--preflight"] if preflight else []),
                env=dict(os.environ, PATH=str(root / "bin") + os.pathsep + os.environ["PATH"],
                         FACTORY_TESTS=str(root / "profile"), CALLS=str(root / "calls"),
                         FAIL_STEP=fail, PREFETCH_MODULES=dependencies,
                         CLAFER_TEST_JOBS=jobs,
                         CLAFER_VALIDATION_PLAN=str(root / "plan.json"), SELECTED_MODE=selection),
                capture_output=True, text=True, check=False,
            )
            return result, (root / "calls").read_text().splitlines()

    def test_parallel_test_failure_still_prevents_kernel_replay(self):
        for fail, code in (("", 0), ("scripts/run_tests.py", 23)):
            with self.subTest(fail=fail):
                result, calls = self.run_check(jobs="2", fail=fail)
                self.assertEqual(result.returncode, code, result.stderr)
                self.assertTrue(any("runtime.py lake env python3 scripts/run_tests.py --jobs 2" in call for call in calls))
                self.assertEqual(any("leanchecker" in call for call in calls), code == 0)

    def test_preflight_and_module_failure_never_provision_or_invoke_lake(self):
        for preflight, fail, code in [(True, "", 0), (False, "test_project_modules.py", 23),
                                      (False, "scripts/project_modules.py", 23)]:
            with self.subTest(preflight=preflight, fail=fail):
                result, calls = self.run_check(preflight=preflight, fail=fail)
                self.assertEqual(result.returncode, code, result.stderr)
                self.assertNotIn("profile", calls)
                self.assertFalse(any(call.startswith("lake ") for call in calls))
                self.assertFalse(any("scripts/verification/runtime.py" in call for call in calls))
                self.assertIn(f"exit {code},", result.stdout)

    def test_cache_failure_preserves_every_build_kernel_audit_and_test_gate(self):
        result, calls = self.run_check(fail="exe cache get")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertLess(next(i for i, call in enumerate(calls) if "test_project_modules.py" in call),
                        calls.index("profile"))
        self.assertIn("building the pinned dependencies from source", result.stderr)
        self.assertEqual([call for call in calls if call.startswith("lake build")], [
            "lake build DPGraph FormalCD Clafer +DPGraph +DPGraph.Internal.New +FormalCD +Clafer",
        ])
        self.assertEqual([call for call in calls if "leanchecker" in call], [
            "lake env leanchecker --verbose DPGraph FormalCD Clafer",
        ])
        for source in (".lake/validation/axiom_audit.lean", "tests/public_imports.lean"):
            self.assertIn(f"lake env lean -DwarningAsError=true {source}", calls)
        self.assertIn("lake env python3 -m unittest discover -s tests -v", calls)
        self.assertIn("[check] Kernel checks (all discovered modules): exit 0,", result.stdout)
        kernel = next(i for i, call in enumerate(calls) if "leanchecker" in call)
        for gate in ("axiom_audit.lean", "tests/public_imports.lean", "unittest discover -s tests -v"):
            self.assertLess(next(i for i, call in enumerate(calls) if gate in call), kernel)
        self.assertEqual(kernel, len(calls) - 1)

    def test_prefetch_uses_inventory_and_empty_inventory_skips_download(self):
        result, calls = self.run_check()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual([call for call in calls if "exe cache get" in call], [
            "lake exe cache get Mathlib.Data.Set.Defs Mathlib.Tactic.FinCases",
        ])
        result, calls = self.run_check(dependencies="")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(any("exe cache get" in call for call in calls))
        self.assertTrue(any(call.startswith("lake build") for call in calls))
        self.assertTrue(any("leanchecker" in call for call in calls))

    def test_failed_kernel_check_preserves_prior_gates_and_reports_its_exit(self):
        result, calls = self.run_check(fail="env leanchecker --verbose DPGraph FormalCD Clafer")
        self.assertEqual(result.returncode, 23)
        self.assertTrue(any("axiom_audit.lean" in call for call in calls))
        self.assertIn("lake env python3 -m unittest discover -s tests -v", calls)
        self.assertIn("[check] Kernel checks (all discovered modules): exit 23,", result.stdout)

    def test_build_audit_and_test_failures_stop_later_stages(self):
        for failure, forbidden in [
            ("build DPGraph", "leanchecker"),
            ("axiom_audit.lean", "tests/public_imports.lean"),
            ("tests/public_imports.lean", "unittest discover -s tests -v"),
            ("scripts/verification/runtime.py", None),
            ("unittest discover -s tests -v", None),
        ]:
            with self.subTest(failure=failure):
                result, calls = self.run_check(fail=failure)
                self.assertEqual(result.returncode, 23, result.stdout + result.stderr)
                if forbidden:
                    self.assertFalse(any(forbidden in call for call in calls))
                self.assertFalse(any("leanchecker" in call for call in calls))
                self.assertIn("exit 23,", result.stdout)

    def test_exporter_setup_precedes_python_tests(self):
        result, calls = self.run_check()
        self.assertEqual(result.returncode, 0, result.stderr)
        setup = next(i for i, call in enumerate(calls) if "scripts/verification/runtime.py" in call)
        self.assertEqual(calls[setup + 1], "lake env python3 -m unittest discover -s tests -v")
        result, calls = self.run_check(fail="scripts/verification/runtime.py")
        self.assertEqual(result.returncode, 23)
        self.assertNotIn("lake env python3 -m unittest discover -s tests -v", calls)
        self.assertFalse(any("leanchecker" in call for call in calls))

    def test_documentation_selection_runs_checks_without_toolchain_setup(self):
        for failure in ("", "scripts/check_docs.py", "test_check_docs.py", "test_validation.py"):
            with self.subTest(failure=failure):
                result, calls = self.run_check(selection="docs", fail=failure)
                self.assertEqual(result.returncode, 23 if failure else 0, result.stderr)
                self.assertIn("python3 scripts/check_docs.py", calls)
                self.assertNotIn("profile", calls)
                self.assertFalse(any(call.startswith("lake ") for call in calls))
                self.assertFalse(any("scripts/verification/runtime.py" in call for call in calls))
                self.assertIn("test_project_modules.py", "\n".join(calls))
                if not failure:
                    self.assertIn("test_check_docs.py", "\n".join(calls))
                    self.assertIn("test_validation.py", "\n".join(calls))
                    self.assertIn("no new Lean validation claimed", result.stdout)


if __name__ == "__main__":
    unittest.main()
