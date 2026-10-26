"""Strict external decoding for the pinned effective-core boundary.

This parser, hashing/capture protocol and upstream compiler are outside the Lean
proof boundary. Lean independently checks UID indexing and effective-core admission.
See docs/resolved-import.md. No solver is invoked.
"""
from __future__ import annotations

import functools
import hashlib
import json
import re
from pathlib import Path

PIN = "6750e6f591b2131549122c13dee94d3d2257eaea"
VERSION = "0.5.4"
EXPORT_SCHEMA = "generic-aeson-0.5.4/1"
ARCHIVE = "2b9e111e21d979ff331816161738df9b07417658f788e0939f31b84292cae74f"
SOURCE_TREE = "4312978c73cf593e7d12f02fc705b68e5b6e11e16da1ace08cb0ab40932f3a99"
STACK_LOCK = {"bytes": 1410, "sha256": "2bed95387bc9ad79df4f70de77a9c7e468125c10a09a68a42da233434b59acff"}
SCHEMA = "clafer-import/1"
REGISTRY = {"root", "clafer", "integer", "int", "string", "double", "real", "boolean"}
# LexClafer.x letters/identifier continuations; UID apostrophes become __prime__.
LETTER = r"[A-Za-zÀ-ÖØ-öø-ÿ]"
IDENTIFIER = LETTER + r"[A-Za-zÀ-ÖØ-öø-ÿ0-9_']*"
ALLOY_RESERVED = set("abstract after all always and as assert before but check disj else enum eventually exactly expect extends fact for fun historically iden iff implies in Int let lone module no none not once one open or pred private releases run seq set sig since some steps String sum this triggered univ until var".split())
OPTIONS = dict(mode=["JSON", "Alloy"], console_output=False,
    flatten_inheritance=False, timeout_analysis=0, no_layout=False,
    new_layout=False, check_duplicates=False, skip_resolver=False,
    keep_unused=True, no_stats=True, validate=False, tooldir=".",
    alloy_mapping=True, self_contained=False, add_graph=False,
    show_references=False, add_comments=False, ecore2clafer=False,
    trace_len=10, scope_strategy="None", afm=False, meta_data=True,
    minint=None, maxint=None, imports=[], import_root=[], public_imports=False,
    import_base="", file="input.cfr")
DECL_FIELDS = {"_cinPos", "_modifiers", "_gcard", "_ident", "_uid", "_parentUID",
               "_super", "_reference", "_card", "_glCard", "_elements"}


class Rejection(ValueError):
    def __init__(self, category, code, detail=""):
        self.category, self.code, self.detail = category, code, detail
        super().__init__(f"{category}:{code}: {detail}")

    def result(self):
        return dict(status=self.category, code=self.code, detail=self.detail)


def reject(code, detail="", category="malformed"):
    raise Rejection(category, code, str(detail))


def unsupported(code, detail=""):
    reject(code, detail, "unsupported")



def strict_boundary(function):
    @functools.wraps(function)
    def checked(*args, **kwargs):
        try:
            return function(*args, **kwargs)
        except Rejection:
            raise
        except (TypeError, AttributeError, KeyError, IndexError, UnicodeError, RecursionError, ValueError) as error:
            reject("schema_type", type(error).__name__)
        except FileNotFoundError as error:
            reject("missing_artifact", Path(error.filename).name)
    return checked

def exact(obj, fields, where):
    if type(obj) is not dict or set(obj) != set(fields):
        reject("fields", where)
    return obj


def array(value, where):
    if type(value) is not list:
        reject("type", where)
    return value


def string(value, where, nonempty=False):
    if type(value) is not str or (nonempty and not value):
        reject("type", where)
    return value


def boolean(value, where):
    if type(value) is not bool:
        reject("type", where)
    return value


def natural(value, where):
    if type(value) is not int or value < 0:
        reject("natural", where)
    return value


def interval(value, where):
    if type(value) is not list or len(value) != 2 or any(type(x) is not int for x in value):
        reject("interval", where)
    lo, hi = value
    if lo < 0 or (hi != -1 and hi < lo):
        reject("interval", where)
    return value


def position(value, where):
    """Library capture spans have no file map; generated syntax may have no span."""
    if value is None:
        return
    if type(value) is not dict or set(value) != {"start", "end"}:
        reject("position", where)
    points = []
    for key in ("start", "end"):
        point = value[key]
        if type(point) is not dict or set(point) != {"line", "column"}:
            reject("position", where)
        if any(type(point[k]) is not int or point[k] < 1 for k in ("line", "column")):
            reject("position", where)
        points.append((point["line"], point["column"]))
    if points[1] < points[0]:
        reject("position", where)


def loads(data):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                reject("duplicate_json_key", key)
            result[key] = value
        return result
    try:
        return json.loads(data, object_pairs_hook=pairs,
                          parse_constant=lambda x: reject("json_constant", x))
    except (UnicodeError, json.JSONDecodeError, RecursionError) as error:
        reject("json", error)


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode()


def digest(data):
    return dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())


def state_hashes(g):
    return {key: digest(encoded(g[key])) for key in
            ("post_analysis", "post_strings", "consumed_map", "implicit_template", "source_audit")}


def seal_receipt(g):
    return dict(g, state_hashes=state_hashes(g))


@strict_boundary
def check_candidate_bounds(candidate, bounds):
    if candidate is None:
        return
    exact(candidate, {"objects", "root", "members", "containment", "references"}, "candidate")
    members = array(candidate["members"], "members")
    for row in members:
        if type(row) is not list or len(row) != 2:
            reject("candidate_row")
        string(row[0], "candidate uid", True)
        natural(row[1], "object")
    for uid, limit in bounds.items():
        objects = {row[1] for row in members if type(row) is list and len(row) == 2 and row[0] == uid}
        if len(objects) > limit:
            unsupported("candidate_scope", uid)


def direct(exp, where):
    exact(exp, {"_iType", "_pid", "_inPos", "_exp"}, where)
    string(exp["_pid"], where)
    position(exp["_inPos"], where)
    e = exp["_exp"]
    if type(e) is not dict or e.get("tag") != "IClaferId":
        unsupported("expression", where)
    exact(e, {"tag", "_modName", "_sident", "_isTop", "_binding"}, where)
    if e["_modName"] != "":
        unsupported("qualified_id", where)
    uid = string(e["_sident"], where, True)
    boolean(e["_isTop"], where)
    b = e["_binding"]
    if type(b) is not dict or b.get("tag") != "GlobalBind":
        unsupported("binding", where)
    exact(b, {"tag", "contents"}, where)
    if b["contents"] != uid:
        reject("binding_identity", where)
    ty = exp["_iType"]
    if type(ty) is not dict or ty.get("tag") != "TClafer":
        unsupported("type_metadata", where)
    exact(ty, {"tag", "_hi"}, where)
    array(ty["_hi"], where)
    return uid


@strict_boundary
def decode_ir(document):
    """Preserve preorder and compiler UIDs; never index by display name."""
    if type(document) is not dict:
        reject("fields", "JSON envelope")
    if "objectives" in document and document["objectives"] not in ([], {}):
        unsupported("objectives")
    exact(document, {"iModule"} | ({"objectives"} if "objectives" in document else set()), "JSON envelope")
    module = exact(document["iModule"], {"_mName", "_mDecls"}, "module")
    string(module["_mName"], "module name")
    nodes, slots, metadata = [], [], []
    seen = set(REGISTRY)
    def visit(elements, parent):
        for element in array(elements, "elements"):
            if type(element) is not dict or element.get("tag") != "IEClafer":
                unsupported("element", element.get("tag") if type(element) is dict else "non-object")
            exact(element, {"tag", "_iClafer"}, "element")
            c = exact(element["_iClafer"], DECL_FIELDS, "declaration")
            uid = string(c["_uid"], "uid", True)
            if uid in seen:
                reject("duplicate_or_reserved_uid", uid)
            seen.add(uid)
            # Names and IDs remain separate; preserve the compiler's full spelling.
            if not re.fullmatch(IDENTIFIER, uid):
                reject("uid_syntax", uid)
            name = string(c["_ident"], "name", True)
            if not re.fullmatch(IDENTIFIER, name):
                reject("name_syntax", uid)
            mods = exact(c["_modifiers"], {"_abstract", "_initial", "_final"}, uid)
            for key in mods:
                boolean(mods[key], uid)
            if mods["_initial"] or mods["_final"]:
                unsupported("temporal_modifier", uid)
            abstract = mods["_abstract"]
            expected = parent if parent else ("clafer" if abstract else "root")
            if c["_parentUID"] != expected:
                reject("parent_incidence", uid)
            position(c["_cinPos"], uid)
            group = exact(c["_gcard"], {"_interval", "_isKeyword"}, uid)
            boolean(group["_isKeyword"], uid)
            interval(group["_interval"], uid)
            interval(c["_card"], uid)
            interval(c["_glCard"], uid)
            sup = None if c["_super"] is None else direct(c["_super"], uid)
            mode, target = "basic", None
            if c["_reference"] is not None:
                ref = exact(c["_reference"], {"_isSet", "_refModifier", "_ref"}, uid)
                boolean(ref["_isSet"], uid)
                if ref["_refModifier"] is not None:
                    unsupported("reference_modifier", uid)
                mode = "set" if ref["_isSet"] else "bag"
                target = direct(ref["_ref"], uid)
                slots.append((uid, ref["_ref"]))
            if sup is not None:
                slots.append((uid, c["_super"]))
            nodes.append(dict(uid=uid, name=name, parent=c["_parentUID"], abstract=abstract,
                              super=sup, mode=mode, target=target,
                              card=c["_card"], group=group["_interval"]))
            metadata.append(dict(uid=uid, global_card=c["_glCard"], keyword=group["_isKeyword"]))
            visit(c["_elements"], uid)
    visit(module["_mDecls"], None)
    by_id = {n["uid"]: n for n in nodes}
    symbols = {"show", *ALLOY_RESERVED, *REGISTRY}
    for n in nodes:
        for symbol in [n["uid"]] + (["r_" + n["uid"]] if n["parent"] in by_id else []) + ([n["uid"] + "_ref"] if n["target"] else []):
            if symbol in symbols:
                reject("backend_symbol_collision", symbol)
            symbols.add(symbol)
        for target in (n["super"], n["target"]):
            if target in REGISTRY:
                unsupported("predefined_target", target)
            if target is not None and target not in by_id:
                reject("dangling_id", target)
    ranks = {}
    def hierarchy(uid, path=()):
        if uid in path:
            reject("super_cycle", uid)
        sup = by_id[uid]["super"]
        result = [uid] + (hierarchy(sup, (*path, uid)) if sup is not None else [])
        ranks[uid] = len(result)
        return result
    hierarchies = {uid: hierarchy(uid) for uid in by_id}
    for owner, exp in slots:
        uid = exp["_exp"]["_sident"]
        if exp["_iType"]["_hi"] != hierarchies[uid]:
            reject("type_hierarchy", owner)
        if exp["_exp"]["_isTop"] != (by_id[uid]["parent"] in {"root", "clafer"}):
            reject("top_flag", owner)
    # #50's exact S guards, also checked by Lean after finite indexing.
    for n in nodes:
        children = [c for c in nodes if c["parent"] == n["uid"]]
        descendants = [c for c in nodes if n["uid"] in hierarchies[c["uid"]][1:]]
        unused = n["abstract"] and not any(not c["abstract"] for c in descendants)
        if n["abstract"] and (n["parent"] != "clafer" or n["mode"] != "basic" or children or n["group"] != [0, -1]
                or not (n["card"] == [0, -1] or (n["card"] == [0, 0] and unused))):
            unsupported("abstract_fragment", n["uid"])
        if n["super"] is not None and (not by_id[n["super"]]["abstract"] or n["mode"] != "basic"):
            unsupported("inheritance_fragment", n["uid"])
        if n["group"][0] > 0 and not children:
            unsupported("empty_positive_group", n["uid"])
        def depth(uid):
            p = by_id[uid]["parent"]
            return 1 if p in REGISTRY else 1 + depth(p)
        n.update(parentRank=depth(n["uid"]), superRank=ranks[n["uid"]], unused=unused)
    return nodes, metadata


def flatten_ir(module):
    out = {}
    def visit(es):
        for e in es:
            c = e["_iClafer"]
            out[c["_uid"]] = c
            visit(c["_elements"])
    visit(module["_mDecls"])
    return out


@strict_boundary
def validate_generation(g, source, ir, alloy):
    exact(g, {"status", "schema", "effective_options", "backend", "source_audit", "post_analysis",
        "post_strings", "strings", "output_strings", "scopes", "consumed_map", "implicit_template",
        "observations", "top_fragments", "header", "json", "alloy", "state_hashes"}, "generation")
    if g["schema"] != "clafer-generation/1":
        unsupported("generation_version")
    if encoded(g["state_hashes"]) != encoded(state_hashes(g)):
        reject("state_hash")
    if g["status"] != "captured" or g["backend"] != "als":
        unsupported("backend")
    # JSON true == 1 in Python; byte-canonical comparison preserves scalar types.
    if encoded(g["effective_options"]) != encoded(OPTIONS):
        unsupported("options")
    if g["json"].encode() != ir or g["alloy"].encode() != alloy:
        reject("paired_output")
    parsed = loads(ir)
    nodes, metadata = decode_ir(parsed)
    if encoded(g["post_analysis"]) != encoded(parsed["iModule"]) or encoded(g["post_strings"]) != encoded(g["post_analysis"]):
        unsupported("string_pass_changed_ir")
    if any(g[k] != [] for k in ("strings", "output_strings", "scopes")):
        unsupported("strings_or_inferred_scopes")
    audit = exact(g["source_audit"], {"errors", "constructors", "tokens", "ast"}, "source audit")
    string(audit["ast"], "source AST", True)
    if audit["errors"] != [] or not audit["constructors"] or not audit["ast"]:
        unsupported("source_features")
    forbidden = {"EnumDecl", "ClaferUse", "Subconstraint", "Subgoal", "SubAssertion",
                 "InitSome", "Transition", "Initial", "Final", "FinalRef", "FinalTarget"}
    for constructor, count in array(audit["constructors"], "source constructors"):
        string(constructor, "constructor", True)
        natural(count, "constructor count")
        if constructor in forbidden:
            unsupported("source_features", constructor)
    text = source.decode("utf-8")
    if re.search(r"(?m)^\s*//#\s*OPTIONS\b", text):
        unsupported("source_options")
    # The typed AST audit occurs before desugaring in Export.hs. This receipt is
    # extraction evidence, not a signature proving the origin of arbitrary bytes.
    for token in array(audit["tokens"], "tokens"):
        string(token, "source token")
        if "T_PosLineComment" not in token and "T_PosBlockComment" not in token:
            unsupported("source_token")
    consumed = {}
    for row in array(g["consumed_map"], "consumed map"):
        if type(row) is not list or len(row) != 2 or type(row[0]) is not str or row[0] in consumed:
            reject("consumed_map_keys")
        consumed[row[0]] = row[1]
    users = flatten_ir(parsed["iModule"])
    if set(consumed) != set(users) | REGISTRY:
        reject("consumed_inventory")
    template = dict(g["implicit_template"])
    if set(template) != REGISTRY or len(g["implicit_template"]) != len(REGISTRY):
        reject("implicit_registry")
    # The canonical registry is pinned independently of the submitted receipt.
    for uid in REGISTRY:
        expected = dict(_cinPos=None, _modifiers=dict(_abstract=False, _initial=True, _final=True),
            _gcard=dict(_isKeyword=False, _interval=[0, -1]), _ident=uid, _uid=uid,
            _parentUID="", _super=None, _reference=None, _card=[1, 1], _glCard=[1, 1], _elements=[])
        sup = {"integer": "double", "int": "double", "double": "real"}.get(uid)
        if sup:
            expected["_super"] = dict(_iType=None, _pid="", _inPos=None,
                _exp=dict(tag="IClaferId", _modName="", _sident=sup, _isTop=True,
                          _binding=dict(tag="GlobalBind", contents=sup)))
        if encoded(template[uid]) != encoded(expected):
            reject("implicit_registry", uid)
        actual = exact(consumed[uid], DECL_FIELDS, uid)
        if uid == "root":
            # Root's pre-optimization children are the actual consumed user records.
            expected["_elements"] = [dict(tag="IEClafer", _iClafer=consumed[e["_iClafer"]["_uid"]]) for e in parsed["iModule"]["_mDecls"]]
        if encoded(actual) != encoded(expected):
            reject("implicit_registry", uid)
    # Only optimizeModule's documented global card computation and zeroing of
    # unused abstracts may differ; every backend-consumed common field is checked.
    for uid, c in users.items():
        old = consumed[uid]
        exact(old, DECL_FIELDS, uid)
        for key in DECL_FIELDS - {"_glCard", "_card", "_elements"}:
            if encoded(old[key]) != encoded(c[key]):
                unsupported("stale_consumed_map", f"{uid}:{key}")
        if [e["_iClafer"]["_uid"] for e in old["_elements"]] != [e["_iClafer"]["_uid"] for e in c["_elements"]]:
            unsupported("stale_consumed_children", uid)
        if encoded(old["_glCard"]) != encoded([0, -1]):
            unsupported("stale_consumed_global_card", uid)
        # Replay the pinned product calculation as a receipt consistency check,
        # never as the source-semantic local bound.
        def product(uid):
            lo, hi = consumed[uid]["_card"]
            parent = consumed[uid]["_parentUID"]
            if parent in users:
                pl, ph = product(parent)
                lo *= pl
                hi = 0 if hi == 0 or ph == 0 else (-1 if hi == -1 or ph == -1 else hi * ph)
            return [lo, hi]
        if c["_glCard"] != product(uid):
            unsupported("global_card_processing", uid)
        interval(old["_card"], uid)
        n = next(n for n in nodes if n["uid"] == uid)
        if old["_card"] != c["_card"] and not (n["unused"] and old["_card"] == [0, -1] and c["_card"] == [0, 0]):
            unsupported("stale_consumed_card", uid)
        for e in old["_elements"]:
            if encoded(e) != encoded(dict(tag="IEClafer", _iClafer=consumed[e["_iClafer"]["_uid"]])):
                unsupported("stale_consumed_child_record", uid)
    if g["header"] != "open util/integer\npred show {}\nrun show for 1\n\n":
        reject("backend_header")
    if len(array(g["top_fragments"], "fragments")) != len(parsed["iModule"]["_mDecls"]):
        reject("top_fragment_inventory")
    if g["header"] + "".join(g["top_fragments"]) != g["alloy"]:
        reject("generation_fragments")
    observations = array(g["observations"], "observations")
    if [o.get("uid") for o in observations] != [n["uid"] for n in nodes]:
        reject("observations_inventory")
    # Validate all declarations and field owners in the emitted text. The grammar
    # accepted here is exactly the static signature/field grammar of this profile.
    signatures = re.findall(rf"\bsig\s+({IDENTIFIER})(?:\s+extends\s+({IDENTIFIER}))?\s*\{{([^}}]*)\}}", g["alloy"])
    if len(signatures) != len(nodes) or {s[0] for s in signatures} != set(users):
        reject("alloy_signature_inventory")
    ownership = {}
    for uid, sup, body in signatures:
        n = next(n for n in nodes if n["uid"] == uid)
        if sup != (n["super"] or ""):
            reject("alloy_extends", uid)
        fields = [f.strip() for f in body.split(",") if f.strip()]
        observation = next(o for o in observations if o["uid"] == uid)
        exact(observation, {"uid", "signature", "fields", "signature_multiplicity", "parent_fact", "group_fact", "reference_refinement", "set_uniqueness"}, "observation")
        if observation["signature"] != uid or fields != observation["fields"]:
            reject("alloy_fields", uid)
        expected = {}
        if n["target"]:
            expected[uid + "_ref"] = ("one", n["target"])
        for child in nodes:
            if child["parent"] == uid:
                lo, hi = child["card"]
                card = {(0, 1): "lone", (1, 1): "one", (1, -1): "some"}.get((lo, hi), "set")
                expected["r_" + child["uid"]] = (card, child["uid"])
        actual = {}
        for f in fields:
            match = re.fullmatch(rf"({IDENTIFIER})\s*:\s*(one|lone|some|set)\s+({IDENTIFIER})", f)
            if not match or match[1] in actual:
                reject("alloy_field_syntax", uid)
            actual[match[1]] = (match[2], match[3])
            ownership[match[1]] = dict(owner=uid, target=match[3], arity=2)
        if actual != expected:
            reject("alloy_field_ownership", uid)
        gl = users[uid]["_glCard"]
        crude = {(0, 1): "lone", (1, 1): "one", (1, -1): "some"}.get(tuple(gl), "")
        if observation["signature_multiplicity"] != (crude + " " if crude else ""):
            reject("signature_multiplicity", uid)
        prefix = (crude + " " if crude else "") + ("abstract " if n["abstract"] else "") + "sig " + uid + "\n"
        if sup:
            prefix = prefix[:-1] + " extends " + sup + "\n"
        if prefix not in g["alloy"]:
            reject("signature_modifiers", uid)
        expected_parent = "" if n["parent"] in REGISTRY or crude == "one" else (
            "one r_" + uid if crude == "lone" else "one @r_" + uid + ".this")
        if observation["parent_fact"] != expected_parent:
            reject("parent_fact", uid)
        children = [c for c in nodes if c["parent"] == uid]
        lo, hi = n["group"]
        simple = {(0, 0): "#children = 0", (0, -1): "", (0, 1): "lone children", (1, 1): "one children", (1, -1): "some children"}.get((lo, hi))
        if simple is None:
            clauses = ([f"{lo} <= #children"] if lo else []) + ([f"#children <= {hi}"] if hi != -1 else [])
            simple = " and ".join(clauses)
        group_fact = "" if n["abstract"] or not children or not simple else (
            "let children = (" + " + ".join("r_" + c["uid"] for c in children) + ") | " + simple)
        if observation["group_fact"] != group_fact:
            reject("group_fact", uid)
        lo, hi = n["card"]
        uniqueness = []
        if n["mode"] == "set" and (lo > 1 or hi > 1 or hi == -1):
            quantifier = " all disj x, y : " + uid if n["parent"] in REGISTRY else "all disj x, y : this.@r_" + uid
            uniqueness = [quantifier + " | (x.@" + uid + "_ref) != (y.@" + uid + "_ref) "]
        if observation["set_uniqueness"] != uniqueness:
            reject("set_uniqueness", uid)
        for fact in [expected_parent, group_fact, *uniqueness]:
            if fact and fact not in g["alloy"]:
                reject("missing_backend_fact", uid)
        if observation["reference_refinement"] != "":
            unsupported("backend_reference_refinement", uid)
    # Compare the complete restricted static output token stream. This external
    # adapter check accounts for all local/global facts and rejects injected
    # commands/facts even if an attacker recomputes the bundle hashes.
    def card_formula(name, bounds):
        lo, hi = bounds
        simple = {(0, -1): "", (0, 0): f"#{name} = 0", (0, 1): f"lone {name}",
                  (1, 1): f"one {name}", (1, -1): f"some {name}"}.get((lo, hi))
        if simple is not None:
            return simple
        return " and ".join(([f"{lo} <= #{name}"] if lo else []) + ([f"#{name} <= {hi}"] if hi != -1 else []))
    def fact(text):
        return "fact { " + text + " }" if text else ""
    obs = {o["uid"]: o for o in observations}
    def render(n, top):
        uid = n["uid"]
        o = obs[uid]
        children = [c for c in nodes if c["parent"] == uid]
        clauses = [o["parent_fact"], o["group_fact"]]
        for child in children:
            if child["card"] not in ([1, 1], [0, 1], [1, -1]):
                clauses.append(card_formula("r_" + child["uid"], child["card"]))
            clauses.extend(obs[child["uid"]]["set_uniqueness"])
        clauses = [c for c in clauses if c]
        declaration = o["signature_multiplicity"] + ("abstract " if n["abstract"] else "") + "sig " + uid
        if n["super"]:
            declaration += " extends " + n["super"]
        declaration += " { " + ", ".join(o["fields"]) + " }"
        if clauses:
            declaration += " { " + " ".join(clauses) + " }"
        before = fact(card_formula(uid, n["card"])) if top and not o["signature_multiplicity"] else ""
        return before + " " + declaration + " " + " ".join(render(c, False) for c in children)
    expected_fragments = [render(n, True) + " " + fact("".join(obs[n["uid"]]["set_uniqueness"]))
                          for n in nodes if n["parent"] in REGISTRY]
    def tokens(text):
        return re.findall(IDENTIFIER + r"|[0-9]+|<=|!=|[^\s]", text)
    for expected, actual in zip(expected_fragments, g["top_fragments"]):
        if tokens(expected) != tokens(actual):
            reject("backend_processing")
    return nodes, metadata, ownership


@strict_boundary
def import_bundle(directory):
    p = Path(directory)
    manifest = loads((p / "manifest.json").read_bytes())
    exact(manifest, {"schema", "compiler_commit", "compiler_version", "export_schema", "inputs", "bounds"}, "manifest")
    if (manifest["schema"], manifest["compiler_commit"], manifest["compiler_version"], manifest["export_schema"]) != (SCHEMA, PIN, VERSION, EXPORT_SCHEMA):
        unsupported("version")
    exact(manifest["inputs"], {"input.cfr", "analyzed.json", "model.als", "generation.json", "build.json"}, "artifacts")
    files = {}
    for name, identity in manifest["inputs"].items():
        data = (p / name).read_bytes()
        if encoded(digest(data)) != encoded(identity):
            reject("artifact_hash", name)
        files[name] = data
    build = loads(files["build.json"])
    exact(build, {"schema", "compiler_commit", "compiler_archive_sha256", "source_tree_sha256", "resolver", "ghc_version", "stack_version", "stack_lock", "exporter_source", "exporter_binary", "compiler_sources_unchanged"}, "build")
    if (build["schema"], build["compiler_commit"], build["compiler_archive_sha256"], build["resolver"], build["ghc_version"], build["stack_version"], build["compiler_sources_unchanged"]) != ("clafer-capture-build/1", PIN, ARCHIVE, "lts-22.44", "9.6.7", "3.11.1", True):
        unsupported("build_identity")
    boolean(build["compiler_sources_unchanged"], "source matching")
    if build["source_tree_sha256"] != SOURCE_TREE or build["stack_lock"] != STACK_LOCK:
        unsupported("source_or_dependency_pin")
    exporter = Path(__file__).with_name("Export.hs").read_bytes()
    if build["exporter_source"] != digest(exporter):
        unsupported("exporter_revision")
    for key in ("stack_lock", "exporter_binary"):
        exact(build[key], {"bytes", "sha256"}, key)
        natural(build[key]["bytes"], key)
        if not re.fullmatch("[0-9a-f]{64}", build[key]["sha256"]):
            reject("hash_syntax", key)
    nodes, metadata, ownership = validate_generation(loads(files["generation.json"]), files["input.cfr"], files["analyzed.json"], files["model.als"])
    exact(manifest["bounds"], {"root", *(n["uid"] for n in nodes)}, "explicit bounds")
    for uid, bound in manifest["bounds"].items():
        natural(bound, uid)
    if manifest["bounds"]["root"] != 1:
        reject("root_bound")
    return dict(schema=SCHEMA, declarations=nodes), dict(metadata=metadata, fields=ownership, bounds=manifest["bounds"])
