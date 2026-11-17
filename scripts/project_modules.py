#!/usr/bin/env python3
"""Discover every project module and enforce the public library dependency DAG.

The same inventory drives explicit builds, kernel checking and import-all audit.
Unknown local roots fail closed: put reusable helpers inside their owning library.
Imports use the ordinary Lean header syntax; comments may be nested. A header
outside the supported, unambiguous form is rejected rather than ignored.
"""

import argparse
import os
from pathlib import Path
import re
import tomllib


ROOTS = ("DPGraph", "FormalCD", "Clafer")
LEVEL = {name: index for index, name in enumerate(ROOTS)}
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*")
AUDIT_MARKER = "-- PROJECT_IMPORTS"


def uncomment(source):
    """Preserve newlines; do not treat comment delimiters inside strings as code."""
    output, i, depth, string = [], 0, 0, False
    while i < len(source):
        pair = source[i:i + 2]
        char = source[i]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                output.append("\n" if char == "\n" else " ")
                i += 1
        elif string:
            output.append(char)
            i += 1
            if char == "\\" and i < len(source):
                output.append(source[i])
                i += 1
            elif char == '"':
                string = False
        elif pair == "/-":
            output.append(" ")
            depth = 1
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            i = end if end >= 0 else len(source)
        else:
            output.append(char)
            string = char == '"'
            i += 1
    if depth:
        raise ValueError("unterminated block comment")
    return "".join(output)


def imports(source):
    # Require one complete import per line (including public/meta/import all).
    # Lean rejects imports after declarations; we reject them here as well.
    found, body = [], False
    for line in uncomment(source).splitlines():
        words = line.split()
        if not words:
            continue
        if words == ["module"] and not body and not found:
            continue
        if "import" in words[:3]:
            match = re.fullmatch(
                r"\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)\s*", line
            )
            if body or not match or not MODULE.fullmatch(match[1]):
                raise ValueError(f"unsupported import header: {line.strip()}")
            found.append(match[1])
        else:
            body = True
    return found


def inventory(repo):
    modules, tests = {}, []
    # Ignore tool/dependency storage, but never silently omit a source in a
    # project root. Hidden project sources and symlinks are rejected below.
    for directory, dirs, files in os.walk(repo, followlinks=False):
        relative = Path(directory).relative_to(repo)
        if relative == Path("."):
            dirs[:] = [d for d in dirs if d not in {".git", ".lake", ".venv", ".tools", "__pycache__"}]
        for name in dirs:
            if (Path(directory) / name).is_symlink():
                raise ValueError(f"source directory symlink: {relative / name}")
        for name in files:
            if not name.endswith(".lean"):
                continue
            path = relative / name
            if (repo / path).is_symlink():
                raise ValueError(f"source symlink: {path}")
            if path.parts[0] == "tests":
                tests.append(path)
                continue
            module = ".".join(path.with_suffix("").parts)
            if not MODULE.fullmatch(module) or module.split(".")[0] not in LEVEL:
                raise ValueError(f"Lean source outside public libraries: {path}")
            modules[module] = path
    for root in ROOTS:
        if root not in modules:
            raise ValueError(f"missing public entrypoint: {root}.lean")
    return dict(sorted(modules.items())), sorted(tests)


def validate(repo):
    modules, tests = inventory(repo)
    config = tomllib.loads((repo / "lakefile.toml").read_text())
    if config.get("name") != "clafer" or config.get("defaultTargets") != list(ROOTS):
        raise ValueError("package/default targets must cover all three public libraries")
    if "enableArtifactCache" in config:
        raise ValueError("project artifact caching must inherit the validation environment")
    libraries = config.get("lean_lib", [])
    if len(libraries) != len(ROOTS):
        raise ValueError("expected exactly three public libraries")
    for lib, root in zip(libraries, ROOTS):
        if lib != {"name": root, "globs": [root, root + ".**"]}:
            raise ValueError(f"library discovery must cover every {root} module")
        if not (repo / root).is_dir():
            raise ValueError(f"missing library directory for recursive glob: {root}")
    edges = {}
    for module, path in modules.items():
        edges[module] = imports((repo / path).read_text())
        level = LEVEL[module.split(".")[0]]
        for dependency in edges[module]:
            dep_root = dependency.split(".")[0]
            if dep_root in LEVEL:
                if dependency not in modules:
                    raise ValueError(f"{module}: missing project dependency {dependency}")
                if LEVEL[dep_root] > level:
                    raise ValueError(f"reverse layer import: {module} -> {dependency}")
            # The runtime adapter calls the Lean toolchain's JSON parser directly.
            elif not dependency.startswith("Mathlib.") and (module, dependency) != (
                "Clafer.Verification.ImportMain", "Lean.Data.Json.Parser"
            ):
                raise ValueError(f"{module}: unsupported dependency {dependency}")
    # Check cycles, including root/helper paths. Per-edge layer checks imply
    # transitive layer independence even through arbitrarily many helpers.
    active, done = set(), set()

    def visit(module):
        if module in active:
            raise ValueError(f"import cycle at {module}")
        if module in done:
            return
        active.add(module)
        for dep in edges[module]:
            if dep in modules:
                visit(dep)
        active.remove(module)
        done.add(module)

    for module in modules:
        visit(module)
    return modules, tests


def audit_source(repo, modules):
    template = (repo / "tests/axiom_audit.lean").read_text()
    if template.count(AUDIT_MARKER) != 1:
        raise ValueError("audit must contain exactly one project import marker")
    return template.replace(AUDIT_MARKER, "\n".join(f"import all {m}" for m in modules))


# [impl->req~lean-validation~1]
def mathlib_imports(repo, modules, tests):
    """Prefetch every direct Mathlib import; its cache follows transitive imports.

    Include unimported helpers/examples and test-only dependencies. Reuse the
    validated header parser so comments cannot masquerade as imports and an
    unsupported test header cannot silently truncate the prefetch inventory.
    """
    return sorted({
        dependency
        for path in [*modules.values(), *tests]
        for dependency in imports((repo / path).read_text())
        if dependency.split(".")[0] == "Mathlib"
    })


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    modules, tests = validate(args.repo)
    dependencies = mathlib_imports(args.repo, modules, tests)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir / "modules.txt").write_text("".join(f"{m}\n" for m in modules))
    (args.output_dir / "tests.txt").write_text("".join(
        f"{p.as_posix()}\n" for p in tests if p != Path("tests/axiom_audit.lean")
    ))
    (args.output_dir / "axiom_audit.lean").write_text(audit_source(args.repo, modules))
    (args.output_dir / "mathlib-imports.txt").write_text("".join(f"{m}\n" for m in dependencies))
    print(f"Dependency direction checked; {len(modules)} project modules: {', '.join(modules)}")
    print(f"Mathlib prefetch roots ({len(dependencies)}): {', '.join(dependencies)}")


if __name__ == "__main__":
    main()
