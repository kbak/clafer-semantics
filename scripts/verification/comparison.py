#!/usr/bin/env python3
"""Compare or replay a supplied candidate against one paired compiler capture."""
import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import platform

import alloy_runtime
from protocol import IDENTIFIER, OPTIONS, Rejection, digest, encoded, exact, import_bundle, loads, reject, unsupported
from profiles import by_commit
from relation import canonical, decode, fresh_symbol, inventory, isomorphism, occurrences, pin, range_argument, validate_candidate

ROOT = Path(__file__).resolve().parents[2]
SCHEMA = "clafer-structural-comparison/v1"
PAPER = "56b1c18e74807fb7646c0e89cb2fc306f4178affb41fee52fcebde09b031b2fb"
CATEGORIES = {"agree_satisfies", "agree_violates", "alloy_accepts_lean_rejects", "lean_accepts_alloy_rejects"}


def source_commit():
    """Optional checkout metadata; source byte hashes remain authoritative."""
    metadata = ROOT / ".git"
    try:
        metadata.lstat()
    except FileNotFoundError:
        return None
    # Explicit metadata prevents discovery of an unrelated parent repository.
    # lstat keeps broken gitfiles/symlinks distinct from an absent .git entry;
    # Git and filesystem failures propagate to the execution diagnostic.
    return subprocess.check_output(
        ["git", "--git-dir", str(metadata), "--work-tree", str(ROOT),
         "rev-parse", "--verify", "HEAD^{commit}"],
        cwd=ROOT, text=True, stderr=subprocess.PIPE).strip()


def source_snapshot():
    source = {str(p.relative_to(ROOT)): digest(p.read_bytes()) for directory in ("Clafer", "FormalCD", "DPGraph", "scripts/verification")
              for p in sorted((ROOT / directory).rglob("*")) if p.is_file() and p.suffix in (".lean", ".py", ".java", ".hs")}
    for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
        path=ROOT/name
        if path.is_file(): source[name]=digest(path.read_bytes())
    return source


def lean(core, candidate):
    import checker_runtime
    return checker_runtime.execute(core,candidate,source_snapshot())[0]


def command(original, pin_text, bounds, bitwidth, overall, unpinned=False, observations=None,
            signatures=None, exact_command="run show for 1\n", label="ib_candidate"):
    signatures = signatures if signatures is not None else {u: u for u in bounds}
    # Use the imported S fragment's identifier grammar: a generated symbol such
    # as c0_ib_candidate does not collide with the added predicate.
    if original.count(exact_command) != 1 or label in re.findall(IDENTIFIER, original):
        reject("original_command")
    if type(overall) is not int or overall < 0:
        unsupported("global_scope")
    effective_bounds = command_bounds(bounds, observations or {})
    scope = ", ".join(f"{b} {signatures[u]}" for u, b in sorted(effective_bounds.items()))
    if unpinned: pin_text = "pred ib_candidate {}\n"
    if not pin_text.startswith("pred ib_candidate {"): reject("pin_syntax")
    pin_text = pin_text.replace("pred ib_candidate {", f"pred {label} {{", 1)
    guards = "\n".join(f"#{signatures[u]} <= {b}" for u,b in sorted(bounds.items()) if u != "root") or "no none"
    # These bounds preserve the manual domain even where Alloy requires scope 1
    # for a 'one sig', or silently derives scopes through abstract children.
    if not pin_text.endswith("}\n"): reject("pin_syntax")
    pin_text=pin_text[:-2]+guards+"\n}\n"
    cmd = f"run {label} for {overall} but {bitwidth} Int, 0 seq" + (", " + scope if scope else "") + "\n"
    return original.replace(exact_command, "", 1) + "\n" + pin_text + cmd, cmd


def command_bounds(bounds, observations):
    result={u:b for u,b in bounds.items() if u != "root"}
    for uid, o in observations.items():
        if o["signature_multiplicity"] == "one ": result[uid]=1
        elif o["signature_multiplicity"] == "lone ": result[uid]=min(result[uid],1)
        elif o["signature_multiplicity"] == "some ": result[uid]=max(result[uid],1)
    return result


def category(lean_verdict, solver, faithful):
    if solver == "sat" and not faithful:
        return "pin_decode_failure"
    if lean_verdict not in ("satisfies", "violates") or solver not in ("sat", "unsat"):
        return "inconclusive"
    return {("satisfies", "sat"): "agree_satisfies", ("violates", "unsat"): "agree_violates",
            ("violates", "sat"): "alloy_accepts_lean_rejects", ("satisfies", "unsat"): "lean_accepts_alloy_rejects"}[lean_verdict, solver]


# [impl->req~clafer-comparison-replay~1]
def compare(bundle, candidate, output, *, bitwidth, overall, runtime=None, timeout=30, heap_mb=512,
            search=None, unpinned=False, mutation=None, candidate_bytes=None):
    """All stages retain null verdicts until they actually run.

    Execution errors are not comparisons. Callers must fail required validation
    on inconclusive/pin_decode_failure. Expected negatives retain their category.
    """
    output, bundle = Path(output).resolve(), Path(bundle).resolve()
    if output.is_relative_to(ROOT):
        unsupported("evidence_in_repository")
    output.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    result = dict(schema=SCHEMA, admission=None, lean=None, solver=None, category="inconclusive",
                  diagnostics=[], faithful=None, complete=False, replay=["python3", "scripts/verification/comparison.py", "replay", str(output), str(output.with_name(output.name+"-replay"))])
    manifest = dict(schema=SCHEMA, contract_revision="52-S/v1", compiler_commit=None,
                    paper_sha256=PAPER, effective_options=None, fragment="S", decisions=[f"D{i}" for i in range(1,9)], inputs={})
    try:
        # Reuse the exact #51 capture, never independently recapture either side.
        shutil.copytree(bundle, output / "capture")
        core, metadata = import_bundle(output / "capture")
        generation = loads((output / "capture/generation.json").read_bytes())
        manifest["compiler_commit"] = metadata["compiler_commit"]
        manifest["effective_options"] = generation["effective_options"]
        metadata["observations"] = {o["uid"]: o for o in generation["observations"]}
        result["admission"] = "admitted"
        manifest["compiler_build_sha256"] = digest((output / "capture/build.json").read_bytes())["sha256"]
        manifest["generation_receipt"] = "capture/generation.json"
        manifest["lean_commit"] = source_commit()
        # Raw source identity is mandatory, including snapshots without .git.
        source = source_snapshot()
        (output / "source.json").write_bytes(encoded(source))
        (output / "language-runtime.json").write_bytes(encoded(dict(python=sys.version,implementation=platform.python_implementation())))
        (output / "core.json").write_bytes(encoded(core))
        # CLI/replay input retains its exact bytes, including malformed JSON.
        # Generated/dict callers use the canonical serialized API value.
        raw_candidate=encoded(candidate) if candidate_bytes is None else candidate_bytes
        (output / "candidate.json").write_bytes(raw_candidate)
        settings = dict(bitwidth=bitwidth, overall=overall, timeout=timeout, heap_mb=heap_mb,
                        search=search or dict(mode="supplied", complete_domain=False), unpinned=unpinned, mutation=mutation)
        (output / "settings.json").write_bytes(encoded(settings))
        candidate=loads(raw_candidate)
        if candidate is None and not unpinned: reject("missing_candidate")
        verdict = lean(core, None if unpinned else candidate)
        import checker_runtime
        (output / "checker-runtime.json").write_bytes(encoded(checker_runtime.worker.identity))
        (output / "lean.json").write_bytes(encoded(verdict))
        if verdict["status"] not in ("satisfies", "violates", "admitted"):
            result.update(admission=verdict["status"], category=verdict["status"])
            result["diagnostics"].append(dict(stage="lean", **verdict))
        else:
            if not unpinned:
                result["lean"] = verdict["status"]
                validate_candidate(candidate, core, metadata["bounds"])
            nodes, fields = inventory(core, metadata)
            signatures = metadata["signatures"]
            original_command = metadata["original_command"]
            original = (output / "capture/model.als").read_bytes().decode("utf-8")
            predicate = fresh_symbol("ib_candidate", set(re.findall(IDENTIFIER, original)))
            effective, pin_candidate = original, candidate
            if mutation:
                from mutations import inject
                if unpinned: unsupported("mutation_unpinned")
                effective, pin_candidate = inject(mutation, original, candidate, core, metadata)
                (output / "injected-mutation.json").write_bytes(encoded(dict(name=mutation, injected=True,
                    original_alloy=digest(original.encode()), effective_alloy=digest(effective.encode()),
                    original_candidate=digest(encoded(candidate)), pinned_candidate=digest(encoded(pin_candidate)))))
                (output / "injected.als").write_text(effective)
                (output / "injected-candidate.json").write_bytes(encoded(pin_candidate))
            pin_text = "" if unpinned else pin(pin_candidate, core, metadata)
            observations = metadata["observations"]
            if mutation == "drop_cardinality":
                observations = {u:dict(o, signature_multiplicity="") if o["signature_multiplicity"]=="lone " else o for u,o in observations.items()}
            effective_scopes=command_bounds(metadata["bounds"],observations)
            arithmetic = range_argument(original, dict(root=1,**{u:max(b,metadata["bounds"][u]) for u,b in effective_scopes.items()}), bitwidth)
            model, selected_command = command(effective, pin_text, metadata["bounds"], bitwidth, overall,
                unpinned, observations, signatures, original_command, predicate)
            # Include every added constraint, including manual scope guards.
            pin_text=model[len(effective.replace(original_command,"",1))+1:-len(selected_command)]
            (output / "original.als").write_bytes((output / "capture/model.als").read_bytes())
            (output / "comparison.als").write_text(model)
            (output / "pin.als").write_text(pin_text)
            (output / "command.json").write_bytes(encoded(dict(text=selected_command, original=original_command,
                signatures=signatures,
                bounds={u: dict(upper=b, exact=False) for u,b in metadata["bounds"].items() if u != "root"},
                command_bounds=command_bounds(metadata["bounds"],observations),
                scope_adjustments={u:dict(requested=metadata["bounds"][u],effective=b,reason="intrinsic generated signature multiplicity") for u,b in effective_scopes.items() if b!=metadata["bounds"][u]},
                overall=overall, bitwidth=bitwidth, arithmetic=arithmetic, pin=digest(pin_text.encode()),
                derived_occurrences=None if unpinned else occurrences(candidate))))
            runtime = runtime or alloy_runtime.prepare()
            # The bridge sees backend symbols; candidates and retained bounds use source UIDs.
            backend_nodes = {signatures[u]: dict(n, super=signatures.get(n["super"])) for u,n in nodes.items()}
            backend_fields = {s: dict(f, owner=signatures[f["owner"]], target=signatures[f["target"]]) for s,f in fields.items()}
            request = dict(nodes=backend_nodes, fields=backend_fields,
                           original_scopes={signatures[u]: b for u,b in generation["scopes"]},
                           bounds={signatures[u]: b for u,b in effective_scopes.items()},
                           command=predicate, overall=overall, bitwidth=bitwidth, maximum=arithmetic["maximum"])
            solved = alloy_runtime.solve(runtime, output, request, timeout=timeout, heap_mb=heap_mb)
            result["solver"] = solved["outcome"]
            bridge_failure=solved.get("status") not in (None,"ok")
            if bridge_failure:
                result["diagnostics"].append(dict(stage=solved.get("stage","solver"),
                    status=solved["status"],reason=solved.get("detail",solved["status"])))
            if solved["outcome"] == "sat" and not bridge_failure:
                try:
                    decoded = decode(solved["witness"], core, metadata)
                    (output / "decoded.json").write_bytes(encoded(decoded))
                    checked = lean(core, decoded)
                    (output / "decoded-lean.json").write_bytes(encoded(checked))
                    if checked["status"] not in ("satisfies", "violates"):
                        reject("decoded_candidate_rejected")
                    if unpinned:
                        result.update(lean=checked["status"], faithful=True)
                    else:
                        bijection = isomorphism(candidate, decoded)
                        result["faithful"] = bijection is not None
                        if bijection is not None and checked["status"] != result["lean"]:
                            reject("renamed_checker_verdict_changed")
                        (output / "bijection.json").write_bytes(encoded(bijection))
                except TimeoutError as error:
                    result["isomorphism_timeout"]=True
                    result["diagnostics"].append(dict(stage="isomorphism", reason=str(error)))
                except (Rejection, KeyError, TypeError, ValueError) as error:
                    result["faithful"] = False
                    result["diagnostics"].append(dict(stage="decode", reason=str(error)))
            elif solved["outcome"] != "unsat" and not bridge_failure:
                result["diagnostics"].append(dict(stage=solved.get("stage","solver"), reason=solved.get("detail", solved["outcome"])))
            result["category"] = "witness_unsat" if unpinned and result["solver"] == "unsat" else category(result["lean"], result["solver"], result["faithful"])
            if solved.get("unsupported"):result["category"]="unsupported"
            elif bridge_failure:
                result["category"]="pin_decode_failure" if result["solver"]=="sat" and solved["status"]=="error" else "inconclusive"
            if result.get("isomorphism_timeout"): result["category"]="inconclusive"
            result["complete"] = result["category"] in CATEGORIES or result["category"] == "witness_unsat"
    except Rejection as error:
        result["category"] = error.category if error.category in ("malformed", "unsupported", "compiler_rejected") else "inconclusive"
        if result["admission"] is None: result["admission"] = error.category
        result["diagnostics"].append(dict(stage="adapter", **error.result()))
    except KeyboardInterrupt:
        result["interrupted"]=True
        result["diagnostics"].append(dict(stage="execution",reason="interrupted"))
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.SubprocessError) as error:
        result["diagnostics"].append(dict(stage="execution", reason=str(error)))
    # An acyclic input manifest: solver outputs never feed its digest.
    output_names = {"solver.json", "stdout.log", "stderr.log", "execution.json", "witness.xml", "decoded.json", "bijection.json", "lean.json", "decoded-lean.json"}
    for p in sorted(output.rglob("*")):
        if p.is_file() and p.name not in output_names:
            manifest["inputs"][str(p.relative_to(output))] = digest(p.read_bytes())
    (output / "manifest.json").write_bytes(encoded(manifest))
    result["input_manifest"] = digest((output / "manifest.json").read_bytes())
    result["outputs"] = {p.name: digest(p.read_bytes()) for p in output.iterdir() if p.is_file() and p.name in output_names}
    result["elapsed_seconds"] = round(time.monotonic() - started, 6)
    if (output/"source.json").exists() and loads((output/"source.json").read_bytes()) != source_snapshot():
        result.update(category="inconclusive",complete=False)
        result["diagnostics"].append(dict(stage="source",reason="source changed during comparison"))
    reasons={"admission":"capture/import did not complete", "lean":"candidate admission or an earlier stage did not provide a checker input",
             "solver":"an earlier stage failed before a solver verdict was observed"}
    if unpinned:
        reasons["lean"]="no SAT witness exists to decode/check" if result["solver"]=="unsat" else "no successfully decoded SAT witness was available to check"
    result["not_run"] = [{"stage": k, "reason": reasons[k]} for k in ("admission", "lean", "solver") if result[k] is None]
    if not {"candidate.json","settings.json","source.json","core.json"}.issubset(manifest["inputs"]):
        result["replay"]=None
        result["diagnostics"].append(dict(stage="replay",reason="capture admission did not provide a complete comparison input; replay the retained capture through capture.py"))
    (output / "result.json").write_bytes(encoded(result))
    return result


# [impl->req~clafer-comparison-replay~1]
def replay(directory, output, runtime=None):
    directory = Path(directory)
    m = loads((directory / "manifest.json").read_bytes())
    if m.get("schema") != SCHEMA: unsupported("comparison_version")
    exact(m,{"schema","contract_revision","compiler_commit","paper_sha256","effective_options","fragment","decisions","inputs",
             "compiler_build_sha256","generation_receipt","lean_commit"},"comparison manifest")
    profile = by_commit(m["compiler_commit"])
    if profile is None: unsupported("replay_contract_identity")
    expected=dict(contract_revision="52-S/v1",paper_sha256=PAPER,
                  effective_options=OPTIONS | (dict(explicit_model=False, decimal_digits=None) if profile.modern else {}),
                  fragment="S",decisions=[f"D{i}" for i in range(1,9)],generation_receipt="capture/generation.json")
    if any(m[k]!=v for k,v in expected.items()):unsupported("replay_contract_identity")
    required={"source.json","core.json","candidate.json","settings.json","language-runtime.json"}
    required|={"capture/"+n for n in ("input.cfr","analyzed.json","model.als","generation.json","build.json","manifest.json")}
    optional={"injected-mutation.json","injected.als","injected-candidate.json"}
    encoded_inputs={"original.als","comparison.als","pin.als","command.json"}
    execution_inputs={"profile.json","request.json"}
    permitted=[required|enc|run|mut|checker for enc,run in ((set(),set()),(encoded_inputs,set()),(encoded_inputs,execution_inputs))
               for mut in (set(),optional) for checker in (set(),{"checker-runtime.json"})]
    if set(m["inputs"]) not in permitted:reject("replay_input_inventory")
    for name, identity in m["inputs"].items():
        if Path(name).is_absolute() or ".." in Path(name).parts or name in ("manifest.json", "result.json"):
            reject("manifest_reference")
        if digest((directory / name).read_bytes()) != identity: reject("replay_input_hash", name)
    if m["compiler_build_sha256"]!=m["inputs"]["capture/build.json"]["sha256"]:reject("replay_build_identity")
    captured = loads((directory/"capture/manifest.json").read_bytes())
    if type(captured) is not dict or captured.get("compiler_commit") != profile.commit:
        reject("replay_compiler_identity")
    if loads((directory/"source.json").read_bytes()) != source_snapshot(): unsupported("replay_source_changed")
    if loads((directory/"language-runtime.json").read_bytes()) != dict(python=sys.version,implementation=platform.python_implementation()):
        unsupported("replay_python_runtime_changed")
    if "profile.json" in m["inputs"]:
        runtime=runtime or alloy_runtime.prepare()
        profile=loads((directory/"profile.json").read_bytes())
        if any(profile.get(k)!=v for k,v in runtime["identity"].items()):unsupported("replay_alloy_runtime_changed")
    if "checker-runtime.json" in m["inputs"]:
        import checker_runtime
        _,identity=checker_runtime.execute(loads((directory/"core.json").read_bytes()),None,source_snapshot())
        if loads((directory/"checker-runtime.json").read_bytes())!=identity:unsupported("replay_lean_runtime_changed")
    settings = loads((directory / "settings.json").read_bytes())
    exact(settings,{"bitwidth","overall","timeout","heap_mb","search","unpinned","mutation"},"comparison settings")
    return compare(directory / "capture", None, output, runtime=runtime,
                   candidate_bytes=(directory / "candidate.json").read_bytes(), **settings)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="action", required=True)
    c = sub.add_parser("compare")
    c.add_argument("bundle", type=Path); c.add_argument("candidate", type=Path); c.add_argument("output", type=Path)
    c.add_argument("--bitwidth", required=True, type=int); c.add_argument("--overall", required=True, type=int)
    c.add_argument("--timeout", default=30, type=int); c.add_argument("--heap-mb", default=512, type=int)
    r = sub.add_parser("replay"); r.add_argument("directory", type=Path); r.add_argument("output", type=Path)
    args = p.parse_args()
    result = replay(args.directory, args.output) if args.action == "replay" else compare(args.bundle, None,
        args.output, candidate_bytes=args.candidate.read_bytes(), bitwidth=args.bitwidth, overall=args.overall,
        timeout=args.timeout, heap_mb=args.heap_mb)
    print(encoded(result).decode(), end="")
    return 0 if result["category"] in ("agree_satisfies", "agree_violates") else 1


if __name__ == "__main__":
    sys.exit(main())
