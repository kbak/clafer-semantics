"""Actual 0.5.7 exports and Alloy runs across the unchanged structural boundary.

Production transports identities using the captured, checked name map. Receipts
are mutated after capture to test rejection, never used as compiler evidence.
"""
import copy
import os
from pathlib import Path
import subprocess
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts/verification"))
import protocol as p
import comparison
import alloy_runtime
from capture import capture
from compiler_profile import PIN
from runtime import prepare
from relation import rename


def candidate(members, containment=(), references=()):
    rows = [["root", 0]] + [[u, o] for u, extent in members.items() for o in extent]
    return dict(objects=sorted({o for _, o in rows}), root=0, members=rows,
                containment=list(containment), references=list(references))


# [utest->req~clafer-resolved-import~1]
# [utest->req~clafer-compiler-capture~1]
# [utest->req~clafer-alloy-representation~1]
# [utest->req~clafer-bounded-comparison~1]
# [utest->req~clafer-comparison-replay~1]
class CompilerProfileTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.exporter, cls.build = prepare()
        cls.runtime = alloy_runtime.prepare()
        evidence = Path(os.environ.get("CLAFER_COMPARISON_EVIDENCE", tempfile.gettempdir())).resolve()
        if evidence.is_relative_to(ROOT):
            raise RuntimeError("comparison evidence must be external")
        evidence.mkdir(parents=True, exist_ok=True)
        cls.evidence = Path(tempfile.mkdtemp(prefix="clafer-profiles-", dir=evidence))
        print(f"Compiler profiles evidence: {cls.evidence}", flush=True)
        cls.captures = {}; cls.receipts = {}; cls.serial = 0
        paths = {p.stem: p for p in (ROOT / "tests/fixtures/importer").glob("*.cfr")}
        paths.update({p.stem: p for p in (ROOT / "tests/fixtures/comparison").glob("*.cfr")})
        cls.paths = paths
        for name, source in sorted(paths.items()):
            receipt = p.loads(subprocess.check_output([str(cls.exporter), str(source)], timeout=120))
            if receipt["status"] != "captured":
                raise AssertionError((name, receipt))
            receipt = p.seal_receipt(receipt)
            nodes, _ = p.decode_ir(p.loads(receipt["json"]))
            bounds = dict(root=1, **{n["uid"]: (3 if n["abstract"] or n["card"][1] == -1 else n["card"][1]) for n in nodes})
            if name == "optional": bounds["x"] = 2
            path = cls.evidence / ("capture-" + name)
            core, metadata = capture(source, cls.exporter, cls.build, bounds, path)
            cls.captures[name] = (path, core, metadata)
            cls.receipts[name] = receipt

    def run_case(self, name, value, expected="agree_satisfies", **options):
        type(self).serial += 1
        output = self.evidence / f"case-{self.serial}-{name}"
        total = sum(b for u,b in self.captures[name][2]["bounds"].items() if u != "root")
        bitwidth = max(4, (total * total).bit_length() + 1)
        result = comparison.compare(self.captures[name][0], value, output, bitwidth=bitwidth,
                                    overall=10, runtime=self.runtime, **options)
        self.assertEqual(expected, result["category"], (output, result))
        if result["solver"] == "sat" and expected == "agree_satisfies":
            self.assertTrue(result["faithful"])
        return result, output

    def test_positive_violating_empty_and_replay(self):
        for name in ("empty", "bag", "optional", "inheritance"):
            self.run_case(name, candidate({}))
        heads = [2, 3, 4]
        repeated = candidate({"Target": [1], "refs": heads},
            [["Target", [0, 1]]] + [["refs", [0, h]] for h in heads], [["refs", [h, 1]] for h in heads])
        _, path = self.run_case("bag", repeated)
        self.run_case("set", repeated, "agree_violates")
        replay = comparison.replay(path, self.evidence / "replay", runtime=self.runtime)
        self.assertEqual("agree_satisfies", replay["category"])
        self.assertEqual(PIN, p.loads((path / "manifest.json").read_bytes())["compiler_commit"])
        self.run_case("bag", rename(repeated, {0: 77, 1: 9, 2: 8, 3: 7, 4: 6}))
        bad = copy.deepcopy(repeated); bad["references"].pop()
        self.run_case("bag", bad, "agree_violates")
        nested = candidate({"box": [1], "child": [2]}, [["box", [0, 1]], ["child", [1, 2]]])
        self.run_case("nesting", nested)
        nested["containment"].pop()
        self.run_case("nesting", nested, "agree_violates")
        self.run_case("optional", candidate({"x": [1, 2]}, [["x", [0, 1]], ["x", [0, 2]]]), "agree_violates")
        self.run_case("cycles", candidate({"a": [1], "b": [2], "child": [3]},
            [["a", [0, 1]], ["b", [0, 2]], ["child", [1, 3]]], [["a", [1, 2]], ["b", [2, 1]]]))

    def test_names_fields_scopes_and_decoded_identities(self):
        _, core, meta = self.captures["collisions"]
        self.assertEqual("sig_1", meta["signatures"]["sig"])
        self.assertEqual(dict(owner="sig", target="x", arity=2), meta["fields"]["sig_1_ref"])
        escaped = [n["uid"] for n in core["declarations"] if n["name"] in ("a'", "a_prime")]
        self.assertEqual(2, len(set(escaped)))
        for uid in ("x_ref", "r_x", "p_x", "alive_x", "plus", "show", "assertAt_3_5"):
            self.assertNotEqual(uid, meta["signatures"][uid])
        members = {n["uid"]: [i + 1] for i,n in enumerate(core["declarations"])}
        links = [[n["uid"], [0 if n["parent"] == "root" else members[n["parent"]][0], members[n["uid"]][0]]] for n in core["declarations"]]
        refs = [["sig", [members["sig"][0], members["x"][0]]]]
        _, path = self.run_case("collisions", candidate(members, links, refs))
        decoded = p.loads((path / "decoded.json").read_bytes())
        self.assertEqual(set(members) | {"root"}, {u for u,_ in decoded["members"]})
        self.assertIn("pred ib_candidate__", (path / "pin.als").read_text())
        self.assertIn("ib_obj_0_", (path / "pin.als").read_text())
        for name in ("spellings", "identities", "inheritance", "predicate_name", "nested_inheritance", "groups", "bounds", "keywords"):
            self.run_case(name, None, unpinned=True)
        g = self.receipts["inheritance"]
        self.assertEqual([["Unused", 0]], g["scopes"])
        self.assertIn("run show for 1 but 0 Unused\n", g["alloy"])
        self.run_case("inheritance", candidate({"Unused": [1]}), "agree_violates")
        # Empty abstract + renamed signature exercises the rebuilt consumed map.
        source = self.evidence / "renamed-empty.cfr"
        source.write_text("abstract sig\nx 0..1\n")
        path = self.evidence / "capture-renamed-empty"
        core, meta = capture(source, self.exporter, self.build, {"root": 1, "sig": 1, "x": 1}, path)
        self.captures["renamed-empty"] = (path, core, meta)
        self.run_case("renamed-empty", candidate({}))
        # A renamed abstract is also a superclass and reference target: its
        # extent must share the subtype atom and preserve distinct bag heads.
        source = self.evidence / "renamed-inheritance.cfr"
        source.write_text("abstract Unused\nabstract sig\nx : sig 0..1\nrefs ->> sig 0..2\n")
        path = self.evidence / "capture-renamed-inheritance"
        core, meta = capture(source, self.exporter, self.build,
            {"root": 1, "Unused": 1, "sig": 2, "x": 1, "refs": 2}, path)
        self.captures["renamed-inheritance"] = (path, core, meta)
        value = candidate({"sig": [1], "x": [1], "refs": [2, 3]},
            [["x", [0, 1]], ["refs", [0, 2]], ["refs", [0, 3]]], [["refs", [2, 1]], ["refs", [3, 1]]])
        self.run_case("renamed-inheritance", value)
        value["references"].pop()
        self.run_case("renamed-inheritance", value, "agree_violates")

    def rejected_receipt(self, change, code, name="collisions"):
        g = copy.deepcopy(self.receipts[name]); change(g); g = p.seal_receipt(g)
        with self.assertRaises(p.Rejection) as error:
            p.validate_generation(g, self.paths[name].read_bytes(), g["json"].encode(), g["alloy"].encode())
        self.assertEqual(code, error.exception.code)

    def test_name_map_and_backend_receipt_tampering(self):
        self.rejected_receipt(lambda g: g["alloy_names"].pop(), "alloy_name_coverage")
        self.rejected_receipt(lambda g: g["alloy_names"].append(g["alloy_names"][0]), "alloy_name_mapping")
        def mapping(g, uid, value):
            next(row for row in g["alloy_names"] if row[0] == uid)[1] = value
        for uid, name, code in (("sig", "x", "alloy_name_injectivity"), ("sig", "sig", "backend_symbol_collision"),
                                ("sig", "r_x", "backend_symbol_collision"), ("sig", "bad/name", "alloy_name_syntax"),
                                ("root", "other", "alloy_name_registry"), ("sig", "free", "renamed_ir_correspondence")):
            with self.subTest(uid=uid, name=name):
                self.rejected_receipt(lambda g: mapping(g, uid, name), code)
        self.rejected_receipt(lambda g: g["backend_ir"]["_mDecls"][0]["_iClafer"].__setitem__("_ident", "changed"), "renamed_ir_correspondence")
        self.rejected_receipt(lambda g: g["consumed_map"].pop(), "backend_consumed_map")
        self.rejected_receipt(lambda g: g["source_map"].pop(), "consumed_inventory")
        self.rejected_receipt(lambda g: g["scopes"].clear(), "empty_abstract_scopes", "inheritance")
        self.rejected_receipt(lambda g: g["scopes"][0].__setitem__(1, 1), "empty_abstract_scopes", "inheritance")
        self.rejected_receipt(lambda g: g["effective_options"].pop("decimal_digits"), "options")
        self.rejected_receipt(lambda g: g.__setitem__("schema", "clafer-generation/1"), "generation_version")

    def test_strict_modifiers_and_profile_isolation(self):
        original = p.loads(self.receipts["bag"]["json"])
        for field in ("_finalReferences", "_refModifiers"):
            for value, category in ((None, "malformed"), ("FinalRef", "malformed"), (["Unknown"], "malformed"),
                                    ([True], "malformed"), (["FinalRef"], "unsupported"), (["FinalTarget"], "unsupported"),
                                    (["FinalRefTarget"], "unsupported")):
                with self.subTest(field=field, value=value):
                    doc = copy.deepcopy(original)
                    node = doc["iModule"]["_mDecls"][1]["_iClafer"]
                    node["_modifiers" if field == "_finalReferences" else "_reference"][field] = value
                    with self.assertRaises(p.Rejection) as error:
                        p.decode_ir(doc)
                    self.assertEqual(category, error.exception.category)
        doc = copy.deepcopy(original)
        node = doc["iModule"]["_mDecls"][1]["_iClafer"]
        node["_reference"]["_refModifier"] = None
        with self.assertRaises(p.Rejection): p.decode_ir(doc)
        for slot, field in (("_modifiers", "_finalReferences"), ("_reference", "_refModifiers")):
            doc = copy.deepcopy(original)
            del doc["iModule"]["_mDecls"][1]["_iClafer"][slot][field]
            with self.assertRaisesRegex(p.Rejection, "fields"):
                p.decode_ir(doc)

    def test_manifest_and_build_profile_mixing_is_rejected(self):
        for i, changes in enumerate((dict(compiler_commit="6750e6f591b2131549122c13dee94d3d2257eaea"), dict(compiler_version="0.5.4"),
                                     dict(export_schema="generic-aeson-0.5.4/1"), dict(compiler_commit="0" * 40))):
            path = self.evidence / f"mixed-profile-{i}"
            shutil.copytree(self.captures["bag"][0], path)
            manifest = p.loads((path / "manifest.json").read_bytes()) | changes
            (path / "manifest.json").write_bytes(p.encoded(manifest))
            with self.assertRaisesRegex(p.Rejection, "unsupported:version"):
                p.import_bundle(path)
        path = self.evidence / "mixed-build"
        shutil.copytree(self.captures["bag"][0], path)
        build = p.loads((path / "build.json").read_bytes())
        build["compiler_commit"] = "6750e6f591b2131549122c13dee94d3d2257eaea"
        data = p.encoded(build)
        (path / "build.json").write_bytes(data)
        manifest = p.loads((path / "manifest.json").read_bytes())
        manifest["inputs"]["build.json"] = p.digest(data)
        (path / "manifest.json").write_bytes(p.encoded(manifest))
        with self.assertRaisesRegex(p.Rejection, "unsupported:build_identity"):
            p.import_bundle(path)

    def test_excluded_source_forms_remain_excluded(self):
        for i, source in enumerate(("a\nb\nx -> a ++ b\n", "a -> integer\n", "a\n[a]\n", "initial a\n",
                                    "abstract A : B\nabstract B : A\n", "enum Color = red | blue\n")):
            path = self.evidence / f"excluded-{i}.cfr"; path.write_text(source)
            receipt = p.loads(subprocess.check_output([str(self.exporter), str(path)], timeout=120))
            if receipt["status"] == "captured":
                with self.assertRaises(p.Rejection): p.decode_ir(p.loads(receipt["json"]))
            else:
                self.assertIn(receipt["status"], ("unsupported", "compiler_rejected"))
