"""Live build-only 0.5.8 qualification, without widening default import admission."""
import copy
import json
import os
import re
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts/verification"))
import candidate_profile as candidate
import compiler_profile as current
import protocol as p
from capture import capture
from runtime import prepare, valid_runtime

FIXTURES = ROOT / "tests/fixtures/importer"


def encoder_bytes(value):
    raw = json.dumps(value, ensure_ascii=False, separators=(",", ":"))
    # Aeson uses Unicode spellings for backspace/form-feed. Match complete
    # escape tokens so a literal backslash followed by b/f remains untouched.
    return re.sub(r'\\(?:["\\/bfnrt]|u[0-9a-f]{4})',
                  lambda m: {r"\b": r"\u0008", r"\f": r"\u000c"}.get(m[0], m[0]), raw)


# [utest->req~clafer-resolved-import~1]
# [utest->req~clafer-compiler-capture~1]
class CandidateCaptureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.exporter, cls.build = prepare(profile=candidate)
        cls.legacy, cls.legacy_build = prepare()
        cls.probe = cls.exporter.with_name("metadata-probe")
        parent = os.environ.get("CLAFER_CANDIDATE_EVIDENCE")
        if parent:
            Path(parent).mkdir(parents=True, exist_ok=True)
        cls.evidence = Path(tempfile.mkdtemp(prefix="clafer-058-", dir=parent))
        (cls.evidence / "build.json").write_bytes(cls.build.read_bytes())
        cls.receipts = {}
        for fixture in sorted(FIXTURES.glob("*.cfr")):
            data = subprocess.check_output([str(cls.exporter), str(fixture)], timeout=120)
            (cls.evidence / (fixture.stem + ".json")).write_bytes(data)
            (cls.evidence / fixture.name).write_bytes(fixture.read_bytes())
            receipt = p.loads(data)
            if receipt["status"] != "captured":
                raise AssertionError(receipt)
            cls.receipts[fixture.stem] = receipt

    def run_source(self, text, name):
        source = self.evidence / (name + ".cfr")
        source.write_text(text)
        data = subprocess.check_output([str(self.exporter), str(source)], timeout=120)
        (self.evidence / (name + ".json")).write_bytes(data)
        return p.loads(data)

    def test_live_receipt_representation_order_and_determinism(self):
        for name, receipt in self.receipts.items():
            source = FIXTURES / (name + ".cfr")
            with self.subTest(fixture=name):
                self.assertEqual(receipt, p.loads(subprocess.check_output(
                    [str(self.exporter), str(source)], timeout=120)))
                # Shared guarded fixtures validate with the same strict fieldwise
                # receipt relation; this does not admit a candidate manifest.
                p.validate_generation(p.seal_receipt(receipt), source.read_bytes(),
                    receipt["json"].encode(), receipt["alloy"].encode())
                legacy = p.loads(subprocess.check_output([str(self.legacy), str(source)], timeout=120))
                for field in ("source_map", "consumed_map", "implicit_template", "alloy_names"):
                    rows = receipt[field]
                    self.assertEqual([row[0] for row in rows], sorted(row[0] for row in rows))
                    self.assertEqual(rows, legacy[field], field)
                self.assertEqual(receipt["json"], legacy["json"])
                self.assertEqual(receipt["alloy"], legacy["alloy"])

    def test_negative_capture_and_source_audit(self):
        cases = [("constraint", "A\n[ some A ]\n", "unsupported"),
                 ("initializer", "value -> integer = 1\n", "unsupported"),
                 ("temporal", "initial A\n", "unsupported"),
                 ("syntax", "A ->\n", "error"),
                 ("missing", "A : Missing\n", "compiler_rejected"),
                 ("empty-group", "xor Empty\n", "compiler_rejected")]
        for name, text, expected in cases:
            with self.subTest(case=name):
                self.assertEqual(self.run_source(text, name)["status"], expected)

    def test_group_layout_observes_the_candidate_effective_bounds(self):
        text = "a\n2..3 b\n  c\n  d\n"
        receipt = self.run_source(text, "group-layout")
        self.assertEqual(receipt["status"], "captured")
        nodes, _ = p.decode_ir(p.loads(receipt["json"]))
        self.assertEqual([node["card"] for node in nodes], [[1, 1], [1, 1], [0, 1], [0, 1]])
        self.assertEqual(nodes[1]["group"], [2, 3])

    def test_candidate_does_not_replace_default_profile(self):
        self.assertEqual(current.PIN, "f6ca5b887d7bacc09915c6fc0278064c8371beac")
        self.assertTrue(valid_runtime(self.exporter, self.build, candidate))
        self.assertFalse(valid_runtime(self.exporter, self.build))
        self.assertFalse(valid_runtime(self.legacy, self.legacy_build, candidate))
        with self.assertRaisesRegex(p.Rejection, "build_identity"):
            capture(FIXTURES / "identities.cfr", self.exporter, self.build, {}, self.evidence / "not-admitted")
        self.assertFalse((self.evidence / "not-admitted").exists())

    def test_candidate_receipt_mutations_stay_rejected(self):
        receipt = self.receipts["set_and_bag_references"]
        source = (FIXTURES / "set_and_bag_references.cfr").read_bytes()
        for field in ("source_map", "consumed_map", "implicit_template", "alloy_names"):
            changed = copy.deepcopy(receipt)
            changed[field].pop()
            with self.subTest(field=field), self.assertRaises(p.Rejection):
                p.validate_generation(p.seal_receipt(changed), source,
                    changed["json"].encode(), changed["alloy"].encode())

    def metadata(self, arg, name):
        data = subprocess.check_output([str(self.probe), str(arg)], timeout=120)
        (self.evidence / (name + "-metadata.json")).write_bytes(data)
        return p.loads(data)

    def check_metadata(self, result):
        names = json.loads(result["name_map"])
        expected = [dict(fqName=fq, lpqName=lpq, uid=uid)
                    for fq, lpq, uid in sorted(result["triples"])]
        self.assertEqual(names, expected)
        self.assertTrue(all(list(row) == ["fqName", "lpqName", "uid"] for row in names))
        scopes = json.loads(result["scopes"])
        expected_scopes = [dict(lpqName=uid, scope=n) for uid, n in sorted(result["scope_input"])]
        self.assertEqual(scopes, expected_scopes)
        self.assertTrue(all(list(row) == ["lpqName", "scope"] for row in scopes))
        # Independent JSON encoding plus the upstream layout rule pins exact
        # output bytes, including field order and string escaping.
        def pretty(value):
            raw = encoder_bytes(value)
            return ''.join(c + '\n' if c in '[{,' else '\n' + c if c in ']}' else c for c in raw)
        self.assertEqual(result["name_map"], pretty(expected))
        self.assertEqual(result["scopes"], pretty(expected_scopes))

    def test_metadata_on_captured_models(self):
        for name in self.receipts:
            with self.subTest(fixture=name):
                self.check_metadata(self.metadata(FIXTURES / (name + ".cfr"), name))

    def test_metadata_and_instance_json_boundary(self):
        result = self.metadata("--synthetic", "synthetic")
        self.check_metadata(result["metadata"])
        self.check_metadata(result["empty_metadata"])
        instance = json.loads(result["instance"])
        name = 'quote"slash\\tab\tline\nreturn\rback\bform\fctrl\x01É🙂'
        expected = {"elements": [
            dict(ident=name, uid="Owner$0", super="Base", cardMin=0, cardMax=-1,
                 elements=[dict(ident="child'", uid="child$0", reference="Base", cardMin=1, cardMax=1,
                                value='target"\\\t\nÉ$1', elements=[])]),
            dict(ident="Base", uid="Base$0", cardMin=1, cardMax=1, value=-17, elements=[])]}
        self.assertEqual(instance, expected)
        self.assertEqual(result["instance"], encoder_bytes(expected))
        self.assertEqual(result["empty_instance"], '{"elements":[]}')


if __name__ == "__main__":
    unittest.main()
