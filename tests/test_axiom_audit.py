"""Run the actual Lean audit against isolated modules, including private names.

Run by `lake env python3 -m unittest discover -s tests`; fixtures never become
library sources. They use Lean's kernel and the production audit template.
"""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


TEMPLATE = (Path(__file__).parent / "axiom_audit.lean").read_text()


class AxiomAuditTest(unittest.TestCase):
    def audit(self, body, *, root="DPGraph", import_all=True):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            module = root + ".AuditFixture"
            source = path / root / "AuditFixture.lean"
            source.parent.mkdir()
            source.write_text("module\n" + body + "\n")
            env = dict(os.environ, LEAN_PATH=directory + os.pathsep + os.environ.get("LEAN_PATH", ""))
            compiled = subprocess.run(
                ["lean", "-DwarningAsError=true", "--root=" + directory,
                 "-o", str(source.with_suffix(".olean")), str(source)],
                env=env, capture_output=True, text=True, check=False,
            )
            self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
            audit = path / "Audit.lean"
            audit.write_text(TEMPLATE.replace("-- PROJECT_IMPORTS", "import " +
                                               ("all " if import_all else "") + module))
            return subprocess.run(["lean", "-DwarningAsError=true", str(audit)],
                                  env=env, capture_output=True, text=True, check=False)

    def test_private_and_generated_declarations_outside_namespace_are_counted(self):
        result = self.audit("namespace Unrelated\nprivate inductive Witness | point\nend Unrelated")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("New assumptions: none", result.stdout)
        self.assertNotIn("DPGraph: 0 declarations", result.stdout)

    def test_generated_constructor_tag_implementations(self):
        result = self.audit("public inductive Choice (α : Type) | empty | value (x : α)")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_mismatched_constructor_tag_implementations(self):
        for body, index in [("0", "fun | .left => 0 | .right => 1"),
                            ("getObjTagNat _x", "fun _ => 0")]:
            with self.subTest(body=body):
                result = self.audit(f"""set_option genCtorIdx false in
public inductive Choice | left | right
public unsafe def Choice.ctorIdx._impl (_x : Choice) : Nat := {body}
@[implemented_by Choice.ctorIdx._impl] public def Choice.ctorIdx : Choice → Nat := {index}""")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("unsafe or partial project declaration", result.stdout)

    def test_new_axioms_in_every_root_are_rejected(self):
        for root in ["DPGraph", "FormalCD", "Clafer"]:
            with self.subTest(root=root):
                result = self.audit("private axiom forbidden : False", root=root)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("new project axiom", result.stdout)

    def test_unsafe_and_partial_declarations_are_rejected(self):
        for body in ["private unsafe def bad : Nat := 0",
                     "private partial def bad (n : Nat) : Nat := bad n"]:
            with self.subTest(body=body):
                result = self.audit(body)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("unsafe or partial project declaration", result.stdout)

    def test_plain_import_cannot_hide_private_axiom(self):
        result = self.audit("private axiom forbidden : False", import_all=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("audit must import all", result.stdout)

    def test_empty_audit_is_rejected(self):
        result = self.audit("")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("audit found no project declarations", result.stdout)

    def test_upper_layer_declarations_cannot_satisfy_dpgraph_guard(self):
        result = self.audit("private def witness : Nat := 0", root="FormalCD")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("audit found no DPGraph declarations", result.stdout)


if __name__ == "__main__":
    unittest.main()
