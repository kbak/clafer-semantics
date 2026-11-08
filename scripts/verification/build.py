#!/usr/bin/env python3
"""Build the unchanged pinned compiler library and the receipt exporter in scratch."""
import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import tarfile
from protocol import digest, encoded
from profiles import CURRENT, by_version


def require(condition, detail):
    if not condition:
        raise RuntimeError(detail)


def run(cmd, cwd, env, log):
    subprocess.run(cmd, cwd=cwd, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--archive", required=True, type=Path)
    p.add_argument("--stack", required=True, type=Path)
    p.add_argument("--work", required=True, type=Path)
    p.add_argument("--profile", choices=("0.5.4", "0.5.7"), default=CURRENT.version)
    args = p.parse_args()
    profile = by_version(args.profile)
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    require(hashlib.sha256(args.archive.read_bytes()).hexdigest() == profile.archive, "wrong source archive")
    source = work / "compiler"
    with tarfile.open(args.archive) as archive:
        members = archive.getmembers()
        prefix = members[0].name.split('/')[0]
        originals = {}
        for member in members:
            if member.isfile():
                name = Path(member.name).relative_to(prefix)
                data = archive.extractfile(member).read()
                originals[str(name)] = digest(data)
                target = source / name
                if target.exists():
                    require(target.read_bytes() == data, f"modified compiler source: {name}")
                else:
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(data)
                    target.chmod(member.mode)
    env = dict(os.environ, STACK_ROOT=str(work / "stack-root"))
    stack = str(args.stack.resolve())
    exporter = Path(__file__).with_name(profile.exporter).resolve()
    output = work / "clafer-capture"
    obj = work / "exporter-objects"
    obj.mkdir(exist_ok=True)
    # Keep the pinned library unchanged. An observational copy exposes private
    # generator helpers; capture compares its complete output with generate's.
    observer_source = (source / "src/Language/Clafer/Generator/Alloy.hs").read_text()
    header = "module Language.Clafer.Generator.Alloy (genModule) where"
    require(observer_source.count(header) == 1, "unexpected observer source")
    observer = work / "Observer.hs"
    observer.write_text(observer_source.replace(header, "module Observer where"))
    with (work / "build.log").open('w') as log:
        run([stack, "build", "clafer:lib"], source, env, log)
        run([stack, "exec", "--", "ghc", "-package", "clafer", "-package", "aeson",
             "-package", "data-stringmap", "-Wall", "-i" + str(work), "-outputdir", str(obj),
             str(exporter), "-o", str(output)], source, env, log)
    require(all(digest((source / n).read_bytes()) == d for n, d in originals.items()), "compiler sources changed")
    ghc = subprocess.check_output([stack, "exec", "--", "ghc", "--numeric-version"], cwd=source, env=env, text=True).strip()
    stack_version = subprocess.check_output([stack, "--numeric-version"], text=True).strip()
    require(ghc == "9.6.7" and stack_version == "3.11.1", "wrong build tools")
    build = dict(schema="clafer-capture-build/1", compiler_commit=profile.commit, compiler_archive_sha256=profile.archive,
        source_tree_sha256=hashlib.sha256(encoded(originals)).hexdigest(), resolver="lts-22.44",
        ghc_version=ghc, stack_version=stack_version, stack_lock=digest((source / "stack.yaml.lock").read_bytes()),
        exporter_source=digest(exporter.read_bytes()), exporter_binary=digest(output.read_bytes()),
        compiler_sources_unchanged=True)
    (work / "build.json").write_bytes(encoded(build))
    print(output)


if __name__ == "__main__":
    main()
