#!/usr/bin/env python3
"""Capture one analyzed invocation, or replay/import a previously captured bundle."""
import argparse
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from protocol import PIN, VERSION, EXPORT_SCHEMA, SCHEMA, Rejection, digest, encoded, import_bundle, loads, reject, seal_receipt, check_candidate_bounds, strict_boundary


@strict_boundary
def capture(source, exporter, build_file, bounds, output):
    source, exporter, build_file, output = map(Path, (source, exporter, build_file, output))
    build_bytes = build_file.read_bytes()
    build = loads(build_bytes)
    if build["exporter_binary"] != digest(exporter.read_bytes()):
        reject("exporter_binary_hash")
    before = source.read_bytes()
    with tempfile.TemporaryDirectory(prefix="clafer-capture-") as temp:
        snapshot = Path(temp) / "input.cfr"
        snapshot.write_bytes(before)
        result = subprocess.run([str(exporter.resolve()), str(snapshot)], capture_output=True, timeout=120, check=True)
    if build["exporter_binary"] != digest(exporter.read_bytes()) or build_file.read_bytes() != build_bytes:
        reject("capture_producer_changed")
    if before != source.read_bytes():
        reject("source_changed")
    receipt = loads(result.stdout)
    if receipt.get("status") != "captured":
        raise Rejection(receipt.get("status", "error"), "compiler_capture", str(receipt.get("errors", [])))
    receipt = seal_receipt(receipt)
    output.mkdir(parents=True, exist_ok=False)
    files = {"input.cfr": before, "analyzed.json": receipt["json"].encode(),
             "model.als": receipt["alloy"].encode(), "generation.json": encoded(receipt),
             "build.json": build_bytes}
    for name, data in files.items():
        (output / name).write_bytes(data)
    manifest = dict(schema=SCHEMA, compiler_commit=PIN, compiler_version=VERSION,
                    export_schema=EXPORT_SCHEMA, inputs={n: digest(d) for n, d in files.items()}, bounds=bounds)
    (output / "manifest.json").write_bytes(encoded(manifest))
    return import_bundle(output)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    c = sub.add_parser("capture")
    c.add_argument("source", type=Path)
    c.add_argument("output", type=Path)
    c.add_argument("--exporter", required=True, type=Path)
    c.add_argument("--build", required=True, type=Path)
    c.add_argument("--bounds", required=True, type=Path)
    r = sub.add_parser("import")
    r.add_argument("bundle", type=Path)
    r.add_argument("--candidate", type=Path)
    args = p.parse_args()
    try:
        if args.command == "capture":
            core, metadata = capture(args.source, args.exporter, args.build, loads(args.bounds.read_bytes()), args.output)
        else:
            core, metadata = import_bundle(args.bundle)
        # Both commands pass the checked external data to Lean admission. Replay
        # uses the existing checker; UID translation of candidate classes is Lean-side.
        candidate = loads(args.candidate.read_bytes()) if args.command == "import" and args.candidate else None
        check_candidate_bounds(candidate, metadata["bounds"])
        payload = dict(core, candidate=candidate)
        root = Path(__file__).resolve().parents[2]
        result = subprocess.run(["lake", "env", "lean", "--run", "Clafer/Verification/ImportMain.lean"],
            cwd=root, input=encoded(payload), capture_output=True, check=True, timeout=120)
        verdict = loads(result.stdout)
        print(encoded(dict(verdict, compiler_metadata=metadata)).decode(), end="")
    except Rejection as error:
        print(encoded(error.result()).decode(), end="")
        return 2
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        print(encoded(dict(status="error", code="protocol_runtime", detail=str(error))).decode(), end="")
        return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())
