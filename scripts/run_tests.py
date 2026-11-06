#!/usr/bin/env python3
"""Run every discovered unittest in bounded processes with execution receipts."""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import threading
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
# Match `python -m unittest`'s repository imports in parent and worker processes.
sys.path.insert(0, str(ROOT))


def flatten(suite):
    for test in suite:
        if isinstance(test, unittest.TestSuite):
            yield from flatten(test)
        else:
            yield test


def discover(directory):
    loader = unittest.TestLoader()
    tests = list(flatten(loader.discover(str(directory))))
    if loader.errors:
        raise RuntimeError("Test discovery failed:\n" + "\n".join(loader.errors))
    identities = [test.id() for test in tests]
    if not identities or len(set(identities)) != len(identities):
        raise RuntimeError("Test discovery must produce nonempty, unique identities")
    return dict(zip(identities, tests))


class RecordingResult(unittest.TextTestResult):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.executed = []

    def startTest(self, test):
        self.executed.append(test.id())
        super().startTest(test)


def worker(plan_path):
    plan = json.loads(plan_path.read_text())
    tests = discover(plan["directory"])
    if sorted(tests) != plan["inventory"]:
        raise RuntimeError("Discovered tests changed after planning")
    selected = plan["selected"]
    if not selected or len(set(selected)) != len(selected):
        raise RuntimeError("Worker assignment must be nonempty and unique")
    # Each worker compiles its own Java bridge; solver runs and comparison
    # evidence already have unique directories. No writable runtime is shared.
    os.environ["CLAFER_ALLOY_CACHE"] = str(plan_path.parent / "alloy-runtime")
    result = unittest.TextTestRunner(verbosity=2, resultclass=RecordingResult).run(
        unittest.TestSuite(tests[name] for name in selected))
    success = (result.wasSuccessful() and not result.skipped
               and Counter(result.executed) == Counter(selected))
    report = dict(selected=selected, executed=result.executed, success=success,
                  skipped=len(result.skipped), failures=len(result.failures), errors=len(result.errors))
    (plan_path.parent / "result.json").write_text(json.dumps(report, indent=2) + "\n")
    return 0 if success else 1


# [impl->req~lean-validation~1]
def run(directory, jobs, evidence):
    if not 1 <= jobs <= 4:
        raise RuntimeError("Test workers must be between 1 and 4")
    directory = directory.resolve()
    inventory = sorted(discover(directory))
    evidence = evidence.resolve()
    if evidence.is_relative_to(ROOT):
        raise RuntimeError("Test evidence must be outside the repository")
    evidence.mkdir(parents=True, exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix="clafer-tests-", dir=evidence))
    print(f"[tests] {len(inventory)} tests; evidence: {output}", flush=True)
    children = []
    started = time.monotonic()
    lock = threading.Lock()

    def collect(index, process, work):
        with (work / "output.log").open("w") as log:
            for line in process.stdout:
                log.write(line)
                log.flush()
                with lock:
                    print(f"[tests:{index}] {line}", end="", flush=True)
        code = process.wait()
        process.stdout.close()
        try:
            report = json.loads((work / "result.json").read_text())
        except (OSError, ValueError):
            report = {}
        return dict(index=index, exit_code=code, report=report)

    pool = ThreadPoolExecutor(max_workers=jobs)
    try:
        futures = []
        for index in range(min(jobs, len(inventory))):
            work = output / str(index)
            work.mkdir()
            plan = dict(directory=str(directory), inventory=inventory, selected=inventory[index::jobs])
            plan_path = work / "plan.json"
            plan_path.write_text(json.dumps(plan, indent=2) + "\n")
            child = subprocess.Popen([sys.executable, str(Path(__file__).resolve()), "--worker", str(plan_path)],
                                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                                     start_new_session=True)
            children.append(child)
            futures.append(pool.submit(collect, index, child, work))
        results = [future.result() for future in futures]
    finally:
        # Forward cancellation so Python cleanup also stops each Lean checker.
        for child in children:
            if child.poll() is None:
                os.killpg(child.pid, signal.SIGTERM)
        for child in children:
            try:
                child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
        pool.shutdown(wait=True)
    executed = []
    success = True
    for result in results:
        report = result["report"]
        selected = inventory[result["index"]::jobs]
        valid = (result["exit_code"] == 0 and isinstance(report, dict)
                 and report.get("success") is True and report.get("selected") == selected
                 and report.get("executed") == selected and report.get("skipped") == 0)
        success = success and valid
        if valid:
            executed.extend(report["executed"])
    success = success and Counter(executed) == Counter(inventory)
    summary = dict(success=success, inventory=inventory, executed=executed, workers=results,
                   seconds=time.monotonic()-started)
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(f"[tests] {len(executed)}/{len(inventory)} executed; success={success}; {summary['seconds']:.1f}s", flush=True)
    return 0 if success else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--directory", type=Path, default=ROOT / "tests")
    parser.add_argument("--evidence", type=Path,
                        default=Path(os.environ.get("CLAFER_TEST_EVIDENCE", tempfile.gettempdir())))
    parser.add_argument("--worker", type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    return worker(args.worker) if args.worker else run(args.directory, args.jobs, args.evidence)


if __name__ == "__main__":
    def interrupted(signum, frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupted)
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError, KeyboardInterrupt) as error:
        print(f"[tests] Failed: {error or 'interrupted'}", file=sys.stderr)
        sys.exit(1)
