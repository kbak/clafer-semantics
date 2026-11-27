"""Same-generation candidate capture, rich/core correspondence and profile separation."""
import copy
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts/verification"))
import compiler_profile as current
import protocol as p
import release060_profile as release
from capture import capture
from runtime import prepare


# [utest->req~clafer-resolved-import~1]
# [utest->req~clafer-compiler-capture~1]
class ReleaseCaptureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.exporter, cls.build = prepare(profile=release)

    def receipt(self, source):
        return p.loads(subprocess.check_output([self.exporter, source], timeout=120))

    def test_guarded_captures_and_replay(self):
        fixtures = ROOT / "tests/fixtures"
        sources = sorted((fixtures / "importer").glob("*.cfr")) + sorted((fixtures / "comparison").glob("*.cfr"))
        for source in sources:
            with self.subTest(model=source.stem), tempfile.TemporaryDirectory() as tmp:
                receipt = self.receipt(source)
                nodes, _ = p.decode_ir(p.loads(receipt["json"]), profile=release)
                bundle = Path(tmp) / "bundle"
                bounds = {"root": 1, **{n["uid"]: 3 for n in nodes}}
                core, meta = capture(source, self.exporter, self.build, bounds, bundle, profile=release)
                self.assertEqual(meta["compiler_commit"], release.PIN)
                self.assertEqual((core, meta), p.import_bundle(bundle, profile=release))
                with self.assertRaisesRegex(p.Rejection, "unsupported:version"):
                    p.import_bundle(bundle)
                if source.stem == "identities":
                    unused = next(n for n in core["declarations"] if n["uid"] == "Unused")
                    self.assertEqual(unused["card"], [0, -1])
                    self.assertEqual(p.flatten_ir(receipt["backend_ir"])["Unused"]["_card"], [0, 0])
                    cli = subprocess.run([sys.executable, str(ROOT / "scripts/verification/capture.py"),
                                          "import", str(bundle), "--profile", release.NAME],
                                         capture_output=True, check=True, timeout=120)
                    self.assertEqual(p.loads(cli.stdout)["status"], "admitted")

    def test_enum_and_profile_boundaries(self):
        with tempfile.TemporaryDirectory() as tmp:
            source = Path(tmp) / "input.cfr"
            source.write_text("enum E = a | b\n")
            self.assertEqual(self.receipt(source)["status"], "unsupported")
            source.write_text("a\n")
            receipt = self.receipt(source)
            old, build = prepare()
            bundle = Path(tmp) / "old"
            capture(source, old, build, {"root": 1, "a": 1}, bundle)
            with self.assertRaisesRegex(p.Rejection, "unsupported:version"):
                p.import_bundle(bundle, profile=release)
        doc = p.loads(receipt["json"])
        mods = doc["iModule"]["_mDecls"][0]["_iClafer"]["_modifiers"]
        self.assertIs(mods["_enum"], False)
        with self.assertRaisesRegex(p.Rejection, "malformed:fields"):
            p.decode_ir(doc)
        for value, error in [(True, "unsupported:enum"), (0, "malformed:type")]:
            mods["_enum"] = value
            with self.assertRaisesRegex(p.Rejection, error):
                p.decode_ir(doc, profile=release)
        del mods["_enum"]
        with self.assertRaisesRegex(p.Rejection, "malformed:fields"):
            p.decode_ir(doc, profile=release)

        def check(change, expected):
            altered = copy.deepcopy(receipt)
            change(altered)
            with self.assertRaisesRegex(p.Rejection, expected):
                p.validate_generation(p.seal_receipt(altered), b"a\n", receipt["json"].encode(),
                                      receipt["alloy"].encode(), profile=release)
        check(lambda r: dict(r["implicit_template"])["root"]["_modifiers"].update(_enum=True),
              "implicit_registry")
        check(lambda r: r.update(consumed_map=r["source_map"]), "backend_consumed_map")
        check(lambda r: r["effective_options"].update(core=True), "unsupported:options")
        check(lambda r: r["effective_options"].update(record_provenance=True), "unsupported:options")
        check(lambda r: r.update(schema=current.GENERATION), "unsupported:generation_version")
        check(lambda r: r["post_strings"]["_mDecls"][0]["_iClafer"].update(_card=[0, 0]),
              "unsupported:string_pass_changed_ir")

    def test_metadata_probe_on_shared_fixture(self):
        source = ROOT / "tests/fixtures/importer/identities.cfr"
        old, _ = prepare()
        for argument in (source, "--synthetic"):
            with self.subTest(argument=argument):
                def probe(exporter):
                    return p.loads(subprocess.check_output([exporter.with_name("metadata-probe"), argument], timeout=120))
                self.assertEqual(probe(self.exporter), probe(old))
