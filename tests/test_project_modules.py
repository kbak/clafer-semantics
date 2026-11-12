"""Regression checks for permitted/rejected dependencies and complete discovery."""

from pathlib import Path
import tempfile
import unittest

from scripts.project_modules import audit_source, imports, mathlib_imports, validate


REPO = Path(__file__).resolve().parent.parent


class PublicLibrariesTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        self.write("lakefile.toml", (REPO / "lakefile.toml").read_text())
        self.write("DPGraph.lean", "module\npublic import DPGraph.Core\n")
        self.write("DPGraph/Core.lean", "module\npublic import Mathlib.Data.Set.Defs\n")
        self.write("FormalCD.lean", "module\npublic import DPGraph\n")
        self.write("Clafer.lean", "module\npublic import FormalCD\n")
        self.write("FormalCD/.gitkeep", "")
        self.write("Clafer/.gitkeep", "")
        self.write("tests/axiom_audit.lean", (REPO / "tests/axiom_audit.lean").read_text())

    def write(self, path, content):
        file = self.repo / path
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(content)

    def test_permitted_graph_and_unreachable_new_module_are_fully_enumerated(self):
        self.write("FormalCD/Internal/New.lean", "module\nimport DPGraph.Core\n")
        modules, _ = validate(self.repo)
        self.assertIn("FormalCD.Internal.New", modules)
        source = audit_source(self.repo, modules)
        for module in modules:
            self.assertIn(f"import all {module}\n", source)

    # [itest->req~lean-validation~1]
    def test_prefetch_includes_unimported_modules_and_test_only_dependencies(self):
        self.write("FormalCD/Internal/New.lean", "module\npublic import Mathlib.Data.Finset.Max\n")
        self.write("tests/extra.lean", "module\n/- import Mathlib.Unused /- nested -/ -/\n"
                   "meta import all Mathlib.Tactic.FinCases -- test-only dependency\n"
                   "import Mathlib.Data.Set.Defs\nimport Lean\n")
        modules, tests = validate(self.repo)
        self.assertEqual(mathlib_imports(self.repo, modules, tests), [
            "Mathlib.Data.Finset.Max", "Mathlib.Data.Set.Defs", "Mathlib.Tactic.FinCases",
        ])
        # An existing import changing must change the prefetch, without hand edits.
        self.write("FormalCD/Internal/New.lean", "module\nimport Mathlib.Data.Fintype.Card\n")
        self.assertIn("Mathlib.Data.Fintype.Card", mathlib_imports(self.repo, modules, tests))
        self.assertNotIn("Mathlib.Data.Finset.Max", mathlib_imports(self.repo, modules, tests))

    def test_prefetch_empty_inventory_and_explicit_whole_mathlib_import(self):
        self.write("DPGraph/Core.lean", "module\n")
        modules, tests = validate(self.repo)
        self.assertEqual(mathlib_imports(self.repo, modules, tests), [])
        self.write("tests/extra.lean", "import Mathlib\n")
        modules, tests = validate(self.repo)
        self.assertEqual(mathlib_imports(self.repo, modules, tests), ["Mathlib"])

    def test_prefetch_rejects_unsupported_test_import_headers(self):
        for source in ["import Mathlib.Data.Set.Defs Mathlib.Data.Finset.Max\n",
                       "import\n Mathlib.Data.Set.Defs\n"]:
            self.write("tests/extra.lean", source)
            modules, tests = validate(self.repo)
            with self.assertRaisesRegex(ValueError, "unsupported import header"):
                mathlib_imports(self.repo, modules, tests)

    def test_repository_includes_every_delivered_module_and_examples(self):
        modules, tests = validate(REPO)
        self.assertEqual(set(modules), {
            "DPGraph", "DPGraph.Signature", "DPGraph.Formula", "DPGraph.Basic",
            "DPGraph.Morphism", "DPGraph.Examples", "FormalCD", "Clafer",
            "DPGraph.Category", "DPGraph.Semantics", "DPGraph.SemanticsExamples",
            "DPGraph.ModelTransport", "DPGraph.Gluing", "DPGraph.Pushout.Basic",
            "DPGraph.Pushout.Universal", "DPGraph.Pushout.Models", "DPGraph.Span", "DPGraph.Span.Basic",
            "DPGraph.Span.IndexedFamily", "DPGraph.Span.Composition",
            "DPGraph.Span.Relation", "DPGraph.Span.Examples",
            "DPGraph.Predicates", "DPGraph.Predicates.Signature",
            "DPGraph.Predicates.SemanticGraph", "DPGraph.Predicates.Meaning",
            "DPGraph.Predicates.Interpretation", "DPGraph.Predicates.Examples",
            "DPGraph.Predicates.FunctionalKey", "DPGraph.Predicates.Examples.FunctionalKey",
            "DPGraph.Predicates.Relational", "DPGraph.Predicates.Navigation",
            "DPGraph.Predicates.Finite",
            "FormalCD.Basic", "FormalCD.Morphism", "FormalCD.Semantics",
            "FormalCD.Gluing", "FormalCD.Integer",
            "FormalCD.Examples", "FormalCD.SemanticsExamples", "FormalCD.Signature",
            "FormalCD.Metamodel.Shape", "FormalCD.Metamodel.Basic",
            "FormalCD.Metamodel.Binding", "FormalCD.Metamodel.Discipline",
            "FormalCD.Metamodel.Interpretation", "FormalCD.Metamodel.Examples",
            "FormalCD.Metamodel.InterpretationExamples", "FormalCD.Metamodel.NameExamples",
            "FormalCD.Metamodel.Realization.Encoding", "FormalCD.Metamodel.Realization.Context",
            "FormalCD.Metamodel.Realization.Correctness", "FormalCD.Metamodel.Realization.Reconstruction",
            "FormalCD.Metamodel.Realization.Self", "FormalCD.Metamodel.Realization.Examples",
            "FormalCD.SelfDescription", "FormalCD.Telematics.Basic",
            "FormalCD.Telematics.VC", "FormalCD.Telematics.Examples",
            "Clafer.Behavioral", "Clafer.Behavioral.Trace",
            "Clafer.Behavioral.Snapshot", "Clafer.Behavioral.Examples",
            "Clafer.Behavioral.Lifetime", "Clafer.Behavioral.Environment",
            "Clafer.Behavioral.Formula", "Clafer.Behavioral.Denotation",
            "Clafer.Behavioral.Normalization", "Clafer.Behavioral.Lowering",
            "Clafer.Behavioral.FormulaExamples",
            "Clafer.Behavioral.Orbit", "Clafer.Behavioral.Lasso",
            "Clafer.Behavioral.FiniteEvaluation", "Clafer.Behavioral.LassoValidation",
            "Clafer.Behavioral.FiniteSets", "Clafer.Behavioral.Verification",
            "Clafer.Behavioral.LassoExamples",
            "Clafer.Behavioral.GroupObservation", "Clafer.Semantics.Groups",
            "Clafer.Behavioral.ReferenceObservation", "Clafer.Behavioral.ReferenceObservationExamples",
            "Clafer.Behavioral.InheritedReference", "Clafer.Behavioral.InheritedReferenceExamples",
            "Clafer.Behavioral.IntegerObservation", "Clafer.Behavioral.IntegerObservationExamples",
            "Clafer.Behavioral.Arithmetic", "Clafer.Behavioral.ArithmeticExamples",
            "Clafer.Behavioral.Aggregate", "Clafer.Behavioral.AggregateExamples",
            "Clafer.Behavioral.Structural",
            "Clafer.Behavioral.StructuralCompatibility",
            "Clafer.Behavioral.StructuralExamples",
            "Clafer.Behavioral.ConcreteInheritanceExamples",
            "Clafer.Behavioral.StructuralObservation",
            "Clafer.Behavioral.StructuralSnapshot",
            "Clafer.Behavioral.StructuralBinding",
            "Clafer.Behavioral.StructuralBindingExamples",
            "Clafer.Behavioral.CapturedStatic",
            "Clafer.Behavioral.PrimitiveExpression",
            "Clafer.Behavioral.PrimitiveExpressionExamples",
            "Clafer.Behavioral.PartialObservation",
            "Clafer.Behavioral.PartialCompatibility",
            "Clafer.Behavioral.PartialExamples",
            "Clafer.Behavioral.PartialLowering", "Clafer.Behavioral.Composition",
            "Clafer.Behavioral.FinitePartial", "Clafer.Behavioral.FiniteComposition",
            "Clafer.Behavioral.QualificationExamples",
            "Clafer.Behavioral.StaticObservation",
            "Clafer.Behavioral.Initializers",
            "Clafer.Behavioral.InitializerCandidate",
            "Clafer.Behavioral.InitializerCandidateExamples",
            "Clafer.Behavioral.InitializerBounds",
            "Clafer.Behavioral.InitializerClassification",
            "Clafer.Behavioral.InitializerLifecycleExamples",
            "Clafer.Behavioral.InitializerContractExamples",
            "Clafer.Behavioral.InitializerCompatibility",
            "Clafer.Behavioral.InitializerFinality",
            "Clafer.Behavioral.InitializerLegacy",
            "Clafer.Behavioral.InitializerProductionExamples",
            "Clafer.Behavioral.InitializerReplacementExamples",
            "Clafer.Behavioral.InitializerSimultaneousExamples",
            "Clafer.Behavioral.InitializerSourceExamples",
            "Clafer.Behavioral.InitializerStatic",
            "Clafer.Behavioral.InitializerStructure",
            "Clafer.Behavioral.InitializerTransport",
            "Clafer.Behavioral.InitializerTransportExamples",
            "Clafer.Behavioral.AbsentReference", "Clafer.Behavioral.AbsentReferenceExamples",
            "Clafer.Behavioral.Anchors", "Clafer.Behavioral.AnchorExamples",
            "Clafer.Behavioral.Modifiers", "Clafer.Behavioral.ModifierExamples",
            "Clafer.Behavioral.ModifierBoundaryExamples",
            "Clafer.Behavioral.Transitions", "Clafer.Behavioral.TransitionExamples",
            "Clafer.Behavioral.Patterns", "Clafer.Behavioral.PatternExamples",
            "Clafer.Behavioral.Properties", "Clafer.Behavioral.PropertyExamples",
            "Clafer.Context", "Clafer.Syntax", "Clafer.Shape",
            "Clafer.Shape.Diagram", "Clafer.Examples",
            "Clafer.MCS.Basic", "Clafer.MCS.Laws", "Clafer.MCS.Metamodel",
            "Clafer.MCS.Examples",
            "Clafer.MCS.Gluing", "Clafer.MCS.Gluing.Origins",
            "Clafer.MCS.Gluing.Examples", "Clafer.MCS.Gluing.Boundaries",
            "Clafer.Constraints.Support", "Clafer.Constraints.Typing",
            "Clafer.Constraints.Examples", "Clafer.Constraints.Integer",
            "Clafer.Constraints.IntegerNavigation", "Clafer.Constraints.IntegerExamples",
            "Clafer.Constraints.Denotation", "Clafer.Constraints.DenotationLaws",
            "Clafer.Constraints.DenotationInvariance", "Clafer.Constraints.DenotationRenaming",
            "Clafer.Constraints.DenotationSupport", "Clafer.Constraints.CollectionMeaning",
            "Clafer.Constraints.Empty",
            "Clafer.Constraints.DenotationDefined", "Clafer.Constraints.DenotationExamples",
            "Clafer.Constraints.RepeatedDenotation", "Clafer.Constraints.Predicate",
            "Clafer.Examples.Telematics.Expressions", "Clafer.Examples.Telematics.ExpressionEnvironment",
            "Clafer.Examples.Telematics.Definedness", "Clafer.Examples.Telematics.ExpressionExamples",
            "Clafer.Examples.Telematics.Mutations", "Clafer.Examples.ConstraintPredicates",
            "Clafer.Examples.Telematics.Input", "Clafer.Examples.Telematics.Configuration",
            "Clafer.Examples.Telematics.Satisfaction", "Clafer.Examples.Telematics.Compiled",
            "Clafer.Examples.Telematics.Rejections",
            "Clafer.Examples.ConstraintBinding", "Clafer.Examples.VersionPreservation",
            "Clafer.Compile.Structure", "Clafer.Compile.Local",
            "Clafer.Compile.Binding", "Clafer.Compile.Basic", "Clafer.Compile.Examples",
            "Clafer.Compile.EffectiveCore", "Clafer.Compile.GroupSupport", "Clafer.Compile.Groups",
            "Clafer.Compile.GroupSemantics", "Clafer.Compile.GroupExamples",
            "Clafer.Compile.GroupOverlapExamples", "Clafer.Compile.EmptyGroupExamples",
            "Clafer.Semantics.EffectiveCore", "Clafer.Semantics.Structural",
            "Clafer.Semantics.Inheritance",
            "Clafer.Semantics.Interpretation", "Clafer.Semantics.Relational",
            "Clafer.Semantics.Bridge", "Clafer.Semantics.Abstracts",
            "Clafer.Semantics.Reachability", "Clafer.Semantics.Renaming",
            "Clafer.Semantics.Normalization",
            "Clafer.Semantics.Realization", "Clafer.Semantics.RealizationLocal",
            "Clafer.Semantics.RealizationCompatibility", "Clafer.Compile.Realization",
            "Clafer.Compile.ConstraintMeaning",
            "Clafer.Examples.Telematics.Structural", "Clafer.Examples.Telematics.StructuralRejections",
            "Clafer.Examples.Integration", "Clafer.Examples.VersionCompilation",
            "Clafer.Examples.Walkthrough",
            "Clafer.Verification.Finite", "Clafer.Verification.Protocol",
            "Clafer.Verification.ProtocolProofs", "Clafer.Verification.Admission",
            "Clafer.Verification.Representation", "Clafer.Verification.Examples",
            "Clafer.Verification.Import", "Clafer.Verification.ImportProofs",
            "Clafer.Verification.ImportMain", "Clafer.Verification.ImportExamples",
        })
        self.assertIn(Path("tests/public_imports.lean"), tests)
        self.assertIn(Path("tests/formalcd_imports.lean"), tests)
        self.assertIn(Path("tests/semantic_dependencies.lean"), tests)
        self.assertIn(Path("tests/behavioral_dependencies.lean"), tests)
        self.assertIn(Path("tests/behavioral_lasso.lean"), tests)
        self.assertIn(Path("tests/structural_without_behavioral.lean"), tests)
        self.assertIn(Path("tests/group_dependencies.lean"), tests)
        self.assertIn(Path("tests/structural_checker.lean"), tests)
        self.assertIn(Path("tests/resolved_import.lean"), tests)

    def test_project_artifact_cache_preserves_environment_control(self):
        config = (REPO / "lakefile.toml").read_text()
        for setting in ["true", "false"]:
            changed = f"enableArtifactCache = {setting}\n" + config
            with self.subTest(config=changed):
                self.write("lakefile.toml", changed)
                with self.assertRaisesRegex(ValueError, "project artifact caching"):
                    validate(self.repo)

    def test_reverse_edges_including_helper_and_root_imports_are_rejected(self):
        for path, dep in [("DPGraph/Core.lean", "FormalCD"),
                          ("DPGraph.lean", "Clafer"),
                          ("FormalCD/Helper.lean", "Clafer")]:
            with self.subTest(path=path, dep=dep):
                original = (self.repo / path).read_text() if (self.repo / path).exists() else None
                self.write(path, f"module\npublic import {dep}\n")
                with self.assertRaisesRegex(ValueError, "reverse layer import"):
                    validate(self.repo)
                if original is None:
                    (self.repo / path).unlink()
                else:
                    self.write(path, original)

    def test_transitive_helper_cannot_hide_reverse_dependency(self):
        self.write("DPGraph/Core.lean", "module\nimport DPGraph.Helper\n")
        self.write("DPGraph/Helper.lean", "module\nimport FormalCD\n")
        with self.assertRaisesRegex(ValueError, "DPGraph.Helper -> FormalCD"):
            validate(self.repo)

    def test_unknown_helpers_and_obsolete_roots_cannot_escape_coverage(self):
        for path in ["Helper.lean", "ClaferLean.lean", "Other/Unimported.lean"]:
            with self.subTest(path=path):
                self.write(path, "module\nimport Clafer\n")
                with self.assertRaisesRegex(ValueError, "outside public libraries"):
                    validate(self.repo)
                (self.repo / path).unlink()

    def test_import_of_unowned_or_missing_module_is_rejected(self):
        for dep in ["Helper", "ClaferLean.DPGraph", "DPGraph.Missing", "Mathlib"]:
            with self.subTest(dependency=dep):
                self.write("DPGraph/Core.lean", f"module\nimport {dep}\n")
                with self.assertRaises(ValueError):
                    validate(self.repo)

    def test_cycles_are_rejected(self):
        self.write("DPGraph/Core.lean", "module\nimport DPGraph\n")
        with self.assertRaisesRegex(ValueError, "cycle"):
            validate(self.repo)

    def test_empty_future_library_still_needs_directory_for_lake_glob(self):
        (self.repo / "FormalCD/.gitkeep").unlink()
        (self.repo / "FormalCD").rmdir()
        with self.assertRaisesRegex(ValueError, "missing library directory"):
            validate(self.repo)

    def test_headers_handle_comments_and_reject_unsupported_forms(self):
        self.assertEqual(imports("module\n/- import Clafer /- nested -/ -/\n"
                                 "public import DPGraph.Core -- comment\n"
                                 "meta import all Mathlib.Data.Set.Defs\n"),
                         ["DPGraph.Core", "Mathlib.Data.Set.Defs"])
        for source in ["import DPGraph Clafer", "import\n Clafer", "import «Clafer»",
                       "def x := 1\nimport Clafer", "/- unfinished"]:
            with self.subTest(source=source), self.assertRaises(ValueError):
                imports(source)

    def test_removed_glob_and_audit_marker_fail_closed(self):
        self.write("lakefile.toml", (REPO / "lakefile.toml").read_text().replace('"DPGraph.**"', '"DPGraph.Core"'))
        with self.assertRaisesRegex(ValueError, "every DPGraph module"):
            validate(self.repo)
        self.write("tests/axiom_audit.lean", "module\n")
        with self.assertRaisesRegex(ValueError, "import marker"):
            audit_source(self.repo, ["DPGraph"])

    def test_hidden_or_symlinked_source_is_rejected(self):
        self.write("DPGraph/.Hidden.lean", "module\n")
        with self.assertRaises(ValueError):
            validate(self.repo)
        (self.repo / "DPGraph/.Hidden.lean").unlink()
        (self.repo / "DPGraph/Alias.lean").symlink_to(self.repo / "DPGraph/Core.lean")
        with self.assertRaisesRegex(ValueError, "symlink"):
            validate(self.repo)


if __name__ == "__main__":
    unittest.main()
