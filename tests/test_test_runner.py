"""Exercise complete execution, worker isolation and failure/cancellation exits."""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest

RUNNER = Path(__file__).resolve().parents[1] / "scripts/run_tests.py"


# [itest->req~lean-validation~1]
class TestRunnerTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.tests = self.root / "tests"
        self.tests.mkdir()
        self.evidence = self.root / "evidence"

    def write(self, body):
        (self.tests / "test_example.py").write_text("import unittest, os\n" + body)

    def command(self, jobs=2):
        return [sys.executable, str(RUNNER), "--directory", str(self.tests),
                "--evidence", str(self.evidence), "--jobs", str(jobs)]

    def invoke(self, jobs=2):
        return subprocess.run(self.command(jobs), capture_output=True, text=True, timeout=20)

    def summary(self):
        return json.loads(next(self.evidence.glob("*/summary.json")).read_text())

    def test_every_discovered_test_runs_once_with_isolated_runtime_and_evidence(self):
        self.write('''from pathlib import Path
from scripts.project_modules import imports
class Example(unittest.TestCase):
    def record(self):
        cache = Path(os.environ['CLAFER_ALLOY_CACHE'])
        cache.mkdir(parents=True, exist_ok=True)
        marker = cache / self.id()
        self.assertFalse(marker.exists())
        marker.write_text('executed')
    test_a = record
    test_b = record
    test_c = record
    test_d = record
    test_e = record
''')
        result = self.invoke()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = self.summary()
        self.assertTrue(report["success"])
        self.assertEqual(len(report["inventory"]), 5)
        self.assertCountEqual(report["executed"], report["inventory"])
        markers = list(self.evidence.glob("*/*/alloy-runtime/test_example.*"))
        self.assertEqual(len(markers), 5)
        self.assertEqual(len({p.parent for p in markers}), 2)
        self.assertEqual(len(list(self.evidence.glob("*/*/output.log"))), 2)
        self.assertIn("[tests] 5/5 executed; success=True", result.stdout)

    def test_failures_skips_setup_errors_and_silent_worker_exit_fail(self):
        bodies = {
            "assertion": "class Example(unittest.TestCase):\n    def test_failure(self): self.fail('injected')\n",
            "skip": "class Example(unittest.TestCase):\n    @unittest.skip('injected')\n    def test_skip(self): pass\n",
            "setup": "class Example(unittest.TestCase):\n    @classmethod\n    def setUpClass(cls): raise RuntimeError('injected')\n    def test_never_run(self): pass\n",
            "exit": "class Example(unittest.TestCase):\n    def test_exit(self): os._exit(0)\n",
        }
        for name, body in bodies.items():
            with self.subTest(name=name):
                self.evidence = self.root / name
                self.write(body)
                result = self.invoke()
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertFalse(self.summary()["success"])

    def test_discovery_failure_empty_inventory_and_worker_bounds_fail(self):
        for body in ("raise RuntimeError('broken discovery')\n", ""):
            self.write(body)
            self.assertNotEqual(self.invoke().returncode, 0)
        self.write("class Example(unittest.TestCase):\n    def test_ok(self): pass\n")
        for jobs in (0, 5):
            self.assertNotEqual(self.invoke(jobs).returncode, 0)
        self.evidence = RUNNER.parent / "test-evidence"
        self.assertNotEqual(self.invoke().returncode, 0)
        self.assertFalse(self.evidence.exists())

    def test_stale_inventory_is_rejected_before_execution(self):
        self.write("class Example(unittest.TestCase):\n    def test_added(self): self.fail('must not execute')\n")
        plan = self.root / "plan.json"
        plan.write_text(json.dumps(dict(directory=str(self.tests), inventory=["test_example.Example.test_old"],
                                       selected=["test_example.Example.test_old"])))
        result = subprocess.run([sys.executable, str(RUNNER), "--worker", str(plan)],
                                capture_output=True, text=True, timeout=20)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Discovered tests changed", result.stderr)
        self.assertFalse((self.root / "result.json").exists())

    def test_cancellation_stops_workers(self):
        pid_file = self.root / "worker.pid"
        self.write(f'''from pathlib import Path
import time
class Example(unittest.TestCase):
    def test_wait(self):
        Path({str(pid_file)!r}).write_text(str(os.getpid()))
        time.sleep(20)
''')
        with (self.root / "cancel.log").open("w") as log:
            process = subprocess.Popen(self.command(), stdout=log, stderr=subprocess.STDOUT)
            try:
                deadline = time.monotonic() + 10
                while not pid_file.exists() and time.monotonic() < deadline:
                    time.sleep(0.02)
                self.assertTrue(pid_file.exists())
                child = int(pid_file.read_text())
                process.send_signal(signal.SIGTERM)
                self.assertNotEqual(process.wait(timeout=8), 0)
                with self.assertRaises(ProcessLookupError):
                    os.kill(child, 0)
            finally:
                if process.poll() is None:
                    process.kill()
                    process.wait()


if __name__ == "__main__":
    unittest.main()
