#!/usr/bin/env python3
"""Build an unchanged pinned compiler and its observational adapter in scratch."""
import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import tarfile
from protocol import digest, encoded
from build_profiles import PROFILES, select


def require(condition, detail):
    if not condition:
        raise RuntimeError(detail)


def run(cmd, cwd, env, log):
    subprocess.run(cmd, cwd=cwd, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)


def extract(archive_path, sha256, source):
    require(hashlib.sha256(archive_path.read_bytes()).hexdigest() == sha256, "wrong source archive")
    originals = {}
    with tarfile.open(archive_path) as archive:
        members = archive.getmembers()
        prefix = members[0].name.split('/')[0]
        for member in members:
            if member.isfile():
                name = Path(member.name).relative_to(prefix)
                require(not name.is_absolute() and '..' not in name.parts, "invalid archive path")
                data = archive.extractfile(member).read()
                originals[str(name)] = digest(data)
                target = source / name
                if target.exists():
                    require(target.read_bytes() == data, f"modified compiler source: {name}")
                else:
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(data)
                    target.chmod(member.mode)
    return originals


def unchanged(source, originals):
    require(all(digest((source / n).read_bytes()) == d for n, d in originals.items()), "compiler sources changed")


# [impl->req~clafer-compiler-capture~1]
# [impl->req~clafer-resolved-import~1]
def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--profile", choices=PROFILES, default="0.5.7")
    p.add_argument("--archive", required=True, type=Path)
    p.add_argument("--ig-archive", type=Path)
    p.add_argument("--stack", required=True, type=Path)
    p.add_argument("--work", required=True, type=Path)
    args = p.parse_args()
    profile = select(args.profile)
    work = args.work.resolve()
    require(not work.is_relative_to(Path(__file__).resolve().parents[2]), "build must be outside the repository")
    work.mkdir(parents=True, exist_ok=True)
    source = work / "compiler"
    originals = extract(args.archive, profile.ARCHIVE, source)
    tree = hashlib.sha256(encoded(originals)).hexdigest()
    require(tree == profile.SOURCE_TREE, "wrong source tree")
    env = dict(os.environ, STACK_ROOT=str(work / "stack-root"))
    stack = str(args.stack.resolve())
    exporter = Path(__file__).with_name(profile.EXPORTER).resolve()
    output = work / "clafer-capture"
    obj = work / "exporter-objects"
    obj.mkdir(exist_ok=True)
    # Only the module header of this MIT-licensed observational copy changes.
    observer_source = (source / "src/Language/Clafer/Generator/Alloy.hs").read_text()
    header = "module Language.Clafer.Generator.Alloy (genModule) where"
    require(observer_source.count(header) == 1, "unexpected observer source")
    observer = work / "Observer.hs"
    observer.write_text(observer_source.replace(header, "module Observer where"))
    stack_version = subprocess.check_output([stack, "--numeric-version"], text=True).strip()
    require(stack_version == profile.STACK_VERSION, "wrong Stack version")
    with (work / "build.log").open('w') as log:
        # Check the resolved compiler before compiling either adapter.
        ghc = subprocess.check_output([stack, "exec", "--", "ghc", "--numeric-version"],
            cwd=source, env=env, text=True).strip()
        require(ghc == profile.GHC_VERSION, "wrong GHC version")
        require(digest((source / "stack.yaml.lock").read_bytes()) == profile.STACK_LOCK, "wrong resolver/dependency lock")
        run([stack, "build", "clafer:lib"], source, env, log)
        packages = [arg for package in profile.PACKAGES for arg in ("-package", package)]
        run([stack, "exec", "--", "ghc", *packages, "-Wall", "-i" + str(work),
             "-outputdir", str(obj), str(exporter), "-o", str(output)], source, env, log)
        extra = {}
        if hasattr(profile, "IG_PIN"):
            require(args.ig_archive is not None, "candidate requires --ig-archive")
            ig_source = work / "claferIG"
            ig_originals = extract(args.ig_archive, profile.IG_ARCHIVE, ig_source)
            # Compile the real IG JSON/model modules and their XML data dependency.
            # No stub, solver or instance generation is used by this boundary probe.
            run([stack, "build", "HaXml"], source, env, log)
            probe = Path(__file__).with_name(profile.METADATA_PROBE).resolve()
            probe_output = work / "metadata-probe"
            probe_obj = work / "metadata-objects"
            probe_obj.mkdir(exist_ok=True)
            run([stack, "exec", "--", "ghc", *packages, "-package", "HaXml",
                 "-package", "string-conversions", "-Wall", "-i" + str(ig_source / "src"),
                 "-outputdir", str(probe_obj), str(probe), "-o", str(probe_output)], source, env, log)
            unchanged(ig_source, ig_originals)
            extra = dict(instance_generator_commit=profile.IG_PIN,
                instance_generator_archive_sha256=profile.IG_ARCHIVE,
                metadata_source=digest(probe.read_bytes()), metadata_binary=digest(probe_output.read_bytes()))
    unchanged(source, originals)
    lock = digest((source / "stack.yaml.lock").read_bytes())
    require(lock == profile.STACK_LOCK, "dependency lock changed")
    build = dict(schema="clafer-capture-build/1", compiler_commit=profile.PIN,
        compiler_archive_sha256=profile.ARCHIVE, source_tree_sha256=tree, resolver=profile.RESOLVER,
        ghc_version=ghc, stack_version=stack_version, stack_lock=lock,
        exporter_source=digest(exporter.read_bytes()), exporter_binary=digest(output.read_bytes()),
        compiler_sources_unchanged=True, **extra)
    (work / "build.json").write_bytes(encoded(build))
    print(output)


if __name__ == "__main__":
    main()
