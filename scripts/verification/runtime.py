#!/usr/bin/env python3
"""Run validation with an explicit or automatically built pinned exporter."""
import hashlib
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tarfile
import tempfile
from urllib.request import urlopen

from protocol import ARCHIVE, PIN, SOURCE_TREE, STACK_LOCK, digest, loads

HERE = Path(__file__).resolve().parent
STACK_ARCHIVE = "1fda71e657cd8d355625cc66b61b352699279dfee2664c014a392163bd19a952"
STACK_BINARY = "67c66e918801c41ae4d286b1c91f9124f691c1c7d56071b53889cf4a5c667550"


def matches(path, sha256):
    return path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest() == sha256


def valid_runtime(executable, build_file):
    try:
        build = loads(build_file.read_bytes())
        expected = dict(schema="clafer-capture-build/1", compiler_commit=PIN,
            compiler_archive_sha256=ARCHIVE, source_tree_sha256=SOURCE_TREE,
            resolver="lts-22.44", ghc_version="9.6.7", stack_version="3.11.1",
            stack_lock=STACK_LOCK, compiler_sources_unchanged=True,
            exporter_source=digest((HERE / "Export.hs").read_bytes()),
            exporter_binary=digest(executable.read_bytes()))
        return build == expected and os.access(executable, os.X_OK)
    except (OSError, ValueError):
        return False


def download(url, path, sha256):
    if matches(path, sha256):
        return
    print(f"[capture] Downloading {url}", file=sys.stderr, flush=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as output:
        temporary = Path(output.name)
        try:
            with urlopen(url, timeout=60) as response:
                shutil.copyfileobj(response, output)
            output.close()
            if not matches(temporary, sha256):
                raise RuntimeError(f"Archive hash mismatch: {url}")
            temporary.replace(path)
        finally:
            temporary.unlink(missing_ok=True)


def work_directory(work=None):
    if work is None:
        default = Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache")) / "clafer-capture"
        work = Path(os.environ.get("CLAFER_CAPTURE_CACHE", default)) / PIN
    work = Path(work).resolve()
    if work.is_relative_to(HERE.parents[1]):
        raise RuntimeError("Exporter cache must be outside the repository")
    return work


# [impl->req~lean-validation~1]
def cached_runtime(work):
    """Probe without downloading or building; a cache key alone is insufficient."""
    executable, build = work / "clafer-capture", work / "build.json"
    try:
        recipe = hashlib.sha256((HERE / "build.py").read_bytes()).hexdigest()
        if valid_runtime(executable, build) and (work / "builder.sha256").read_text() == recipe:
            return executable, build
    except (OSError, ValueError):
        pass
    return None


def prepare(work=None):
    explicit = os.environ.get("CLAFER_CAPTURE") or shutil.which("clafer-capture")
    if explicit:
        executable = Path(explicit).resolve()
        build = Path(os.environ.get("CLAFER_CAPTURE_BUILD", str(executable.with_name("build.json")))).resolve()
        if not valid_runtime(executable, build):
            raise RuntimeError("Configured exporter/build identities do not match the pinned sources; rebuild with scripts/verification/build.py")
        return executable, build
    if os.environ.get("CLAFER_CAPTURE_BUILD"):
        raise RuntimeError("CLAFER_CAPTURE_BUILD requires CLAFER_CAPTURE or clafer-capture on PATH")
    if (platform.system(), platform.machine()) != ("Linux", "x86_64"):
        raise RuntimeError("Automatic exporter setup supports Linux x86_64; supply CLAFER_CAPTURE and CLAFER_CAPTURE_BUILD on other platforms")
    import fcntl

    work = work_directory(work)
    work.mkdir(parents=True, exist_ok=True)
    executable, build = work / "clafer-capture", work / "build.json"
    recipe = hashlib.sha256((HERE / "build.py").read_bytes()).hexdigest()
    stamp = work / "builder.sha256"
    # Independent source snapshots share dependencies, never concurrent writers.
    with (work / "build.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if cached_runtime(work):
            print(f"[capture] Reusing verified exporter: {executable}", file=sys.stderr, flush=True)
            return executable, build
        archive = work / "compiler.tar.gz"
        download(f"https://codeload.github.com/gsdlab/clafer/tar.gz/{PIN}", archive, ARCHIVE)
        stack_archive = work / "stack.tar.gz"
        download("https://github.com/commercialhaskell/stack/releases/download/v3.11.1/stack-3.11.1-linux-x86_64.tar.gz",
                 stack_archive, STACK_ARCHIVE)
        stack = work / "stack"
        if not matches(stack, STACK_BINARY):
            with tarfile.open(stack_archive) as packed:
                stack.write_bytes(packed.extractfile("stack-3.11.1-linux-x86_64/stack").read())
            stack.chmod(0o755)
        if not matches(stack, STACK_BINARY):
            raise RuntimeError("Stack binary hash mismatch")
        executable.unlink(missing_ok=True)
        build.unlink(missing_ok=True)
        print(f"[capture] Building pinned exporter; log: {work / 'build.log'}", file=sys.stderr, flush=True)
        subprocess.run([sys.executable, str(HERE / "build.py"), "--archive", str(archive),
                        "--stack", str(stack), "--work", str(work)], check=True)
        if not valid_runtime(executable, build):
            raise RuntimeError("Built exporter identities do not match the pinned sources")
        stamp.write_text(recipe)
        return executable, build


def main():
    if len(sys.argv) < 2:
        raise RuntimeError("Usage: runtime.py COMMAND [ARG ...] | --check-cache WORK | --github-env WORK")
    if sys.argv[1] in ("--check-cache", "--github-env"):
        if len(sys.argv) != 3:
            raise RuntimeError("Cache commands require exactly one external work directory")
        work = work_directory(sys.argv[2])
        if sys.argv[1] == "--check-cache":
            return 0 if cached_runtime(work) else 1
        destination = os.environ.get("GITHUB_ENV")
        if not destination:
            raise RuntimeError("--github-env requires GITHUB_ENV")
        executable, build = prepare(work)
        values = dict(CLAFER_CAPTURE=str(executable), CLAFER_CAPTURE_BUILD=str(build))
        if any("\n" in value or "\r" in value for value in values.values()):
            raise RuntimeError("GitHub environment paths must not contain newlines")
        with Path(destination).open("a") as output:
            output.writelines(f"{key}={value}\n" for key, value in values.items())
        return 0
    executable, build = prepare()
    env = dict(os.environ, CLAFER_CAPTURE=str(executable), CLAFER_CAPTURE_BUILD=str(build))
    return subprocess.call(sys.argv[1:], env=env)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print(f"[capture] Setup failed: {error}; see docs/resolved-import.md#build-and-replay", file=sys.stderr)
        sys.exit(1)
