module

public import Clafer.Compile.Groups
public import Clafer.Constraints.IntegerExamples

/-!
[impl->req~clafer-representative-integration~1]
[proof->req~clafer-representative-integration~1]
-/

/-!
# Appendix 6's mandatory version comparison through Compile and gluing

SoSyM Appendix 6 PDF p.34 (c02 in docs/inherited-realization.md), §6.2.4–5.
The six-declaration fragment retains comp/version, ECU, display/server and int.
Its comparison is attached to display and uses integer extraction after actual
head/dereference navigation. Generated local predicates establish operand
bounds; primitive-domain interpretation remains an explicit assumption.
-/

@[expose] public section
namespace Clafer.Examples.VersionCompilation
open CategoryTheory MCS Compile DPGraph DPGraph.Predicates Constraints

/-- Canonical Compile spelling and the actual source attachment are the only
changes to the delivered navigation fixture. -/
def root : Declaration := { VersionNavigation.rootDecl with name := "Sing" }
def display : Declaration := { VersionNavigation.displayDecl with constraints := [VersionNavigation.boundary] }

def ast : AST := ⟨⟨0⟩, [.branch root [.branch VersionNavigation.intDecl []],
  .branch VersionNavigation.compDecl [.branch VersionNavigation.versionDecl []], .branch VersionNavigation.ecuDecl [],
  .branch display [.branch VersionNavigation.serverDecl []]]⟩

theorem entries : ast.entries =
    [⟨root, none, 0⟩, ⟨VersionNavigation.intDecl, some ⟨0⟩, 1⟩, ⟨VersionNavigation.compDecl, none, 0⟩,
     ⟨VersionNavigation.versionDecl, some ⟨2⟩, 1⟩, ⟨VersionNavigation.ecuDecl, none, 0⟩,
     ⟨display, none, 0⟩, ⟨VersionNavigation.serverDecl, some ⟨5⟩, 1⟩] := rfl

instance ast_nonzero : NeZero ast.entries.length := ⟨by decide⟩
@[simp] theorem ast_root : ast.root = ⟨0⟩ := rfl

theorem wf : ast.WellFormed := by
  constructor
  all_goals try { simp [AST.Known, entries, root, display, VersionNavigation.rootDecl, VersionNavigation.intDecl,
    VersionNavigation.compDecl, VersionNavigation.versionDecl, VersionNavigation.ecuDecl, VersionNavigation.displayDecl, VersionNavigation.serverDecl,
    Reference.kind, Reference.target, Kind.CanExtend, PrimitiveDomain.name,
    ValidRange, GroupCard.range, Clafer.one, unrestricted,
    ConstraintBoundary.Resolved, VersionNavigation.boundary] }
  · refine ⟨fun i => if i = ⟨4⟩ ∨ i = ⟨5⟩ then 1 else 0, ?_⟩
    simp [entries, root, display, VersionNavigation.rootDecl, VersionNavigation.intDecl, VersionNavigation.compDecl, VersionNavigation.versionDecl,
      VersionNavigation.ecuDecl, VersionNavigation.displayDecl, VersionNavigation.serverDecl]
  · intro d hd hu p s hp hpm hs hsm
    simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases p <;> cases s <;>
      simp_all [entries, root, display, VersionNavigation.rootDecl, VersionNavigation.intDecl, VersionNavigation.compDecl, VersionNavigation.versionDecl,
        VersionNavigation.ecuDecl, VersionNavigation.displayDecl, VersionNavigation.serverDecl, Defaults, GroupCard.childDefault]
    all_goals aesop

theorem support_resolved : VersionNavigation.support.Resolved ast := by
  constructor
  · intro v
    fin_cases v <;> simp [AST.Known, entries, VersionNavigation.support, root, display,
      VersionNavigation.rootDecl, VersionNavigation.intDecl, VersionNavigation.compDecl, VersionNavigation.versionDecl, VersionNavigation.ecuDecl, VersionNavigation.displayDecl, VersionNavigation.serverDecl]
  · intro e
    fin_cases e <;> simp [Support.MapResolved, entries, VersionNavigation.support, root, display,
      VersionNavigation.rootDecl, VersionNavigation.intDecl, VersionNavigation.compDecl, VersionNavigation.versionDecl, VersionNavigation.ecuDecl, VersionNavigation.displayDecl, VersionNavigation.serverDecl,
      Reference.target]
  · intro v hv
    fin_cases v <;> simp_all [VersionNavigation.support, entries, root, display,
      VersionNavigation.rootDecl, VersionNavigation.intDecl, VersionNavigation.compDecl, VersionNavigation.versionDecl, VersionNavigation.ecuDecl, VersionNavigation.displayDecl, VersionNavigation.serverDecl]

theorem boundary_eq (q : ConstraintId ast) : boundary ast q = VersionNavigation.boundary := by
  rcases q with ⟨c, k⟩
  change Fin 7 at c
  fin_cases c <;> fin_cases k
  rfl

theorem constraint_typed (q : ConstraintId ast) : VersionNavigation.constraint.Input ast (boundary ast q) := by
  rw [boundary_eq]
  refine ⟨wf, support_resolved, ?_, VersionNavigation.constraint_input.boundary, rfl, ⟨.nil⟩⟩
  simp [ConstraintBoundary.Resolved, AST.Known, entries, root, display,
    VersionNavigation.rootDecl, VersionNavigation.intDecl, VersionNavigation.compDecl, VersionNavigation.versionDecl, VersionNavigation.ecuDecl, VersionNavigation.displayDecl, VersionNavigation.serverDecl]

noncomputable def input : Input ast where
  ast := wf
  root_name := by
    intro d hd
    simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  user_names := by
    intro d hd
    simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [root, display, VersionNavigation.rootDecl, VersionNavigation.intDecl, VersionNavigation.compDecl, VersionNavigation.versionDecl,
      VersionNavigation.ecuDecl, VersionNavigation.displayDecl, VersionNavigation.serverDecl, predefinedStrings]
    all_goals intro dom; cases dom <;> decide
  constraint _ := VersionNavigation.constraint
  typed := constraint_typed
  positive_support _ := by decide

noncomputable def q : ConstraintId ast := ⟨5, ⟨0, by decide⟩⟩
noncomputable def glued := gluedGroups input

theorem output_valid : Valid (compile input).labels (compile input).formulas ∧
    glued.toRawOver.WellFormed := ⟨wellFormed input, glued.wellFormed⟩

/-- c02 is the delivered unguarded not/less expression, owned by display. -/
theorem attachment : (input.constraint q).body = VersionNavigation.comparison ∧
    (compile input).formulas.owner (.inr q) = 5 ∧
    (promote input (formula input (.inr q))).translate (groupLabel input) ∈
      glued.declarations := ⟨rfl, rfl, .inl (.inr q), rfl⟩

theorem full_binding (v : VersionNavigation.support.Vertex) :
    sourceId ast ((binding input q).obj v) = VersionNavigation.support.classId v :=
  binding_vertices input q v

/-- Both head and dereference maps survive, with inheritance edges as distinct
support arrows. These are the four 1..1 formulas used for definedness below. -/
theorem mandatory_bounds :
    (family input).multiplicity 3 = one ∧ (family input).multiplicity 6 = one ∧
    (family input).super 5 = some 2 ∧ (family input).super 4 = some 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

variable {U : Type}

noncomputable def navigation (m : glued.carrier ⥤q semanticGraph U) :
    VersionNavigation.support.graph ⥤q semanticGraph U :=
  (binding input q).comp ((groupLabel input).comp m)

/-- Only the emitted built-in local formulas are assumed here. No truth of c02,
whole-model satisfaction, or singleton operand is assumed. -/
noncomputable def LocalHolds (m : glued.carrier ⥤q semanticGraph U) : Prop :=
  ∀ l : LocalId (family input),
    (interpretation U).Satisfies m (l.formula.translate (groupLabel input))

theorem local_of_model (authored : Interpretation (Constraints.signature input.constraint) (semanticGraph U))
    (m : glued.carrier ⥤q semanticGraph U)
    (hm : (groupInterpretation input U authored).IsModel glued.toDPGraph m) : LocalHolds m := by
  intro l
  exact hm _ ⟨.inl (.inl l), rfl⟩

/-- Establish the delivered integer-navigation hypotheses from these actual
compiled/glued formulas. Integer-domain realization is still explicit. -/
noncomputable def versionModel (m : glued.carrier ⥤q semanticGraph U)
    (hm : LocalHolds m) (R : IntegerRealization U)
    (hd : (navigation m).obj (5 : VersionNavigation.support.Vertex) = R.domain) : VersionNavigation.Model U where
  realization := R
  model := navigation m
  same_id := by
    intro x y h
    have he : x = y := by fin_cases x <;> fin_cases y <;> simp_all [VersionNavigation.support]
    subst y; rfl
  inclusion := by
    intro e he
    fin_cases e
    · exact hm (.inclusion ⟨5, 2, Shape.headInclusion _ _, rfl⟩)
    · exact hm (.inclusion ⟨4, 2, Shape.headInclusion _ _, rfl⟩)
    all_goals cases he
  integer_domain := by
    intro v hv
    fin_cases v <;> simp_all [VersionNavigation.support]
  version_head := hm (.multiplicity 3 ⟨.head, rfl⟩)
  version_dref := hm (.multiplicity 3 ⟨.dereference, rfl⟩)
  server_head := hm (.multiplicity 6 ⟨.head, rfl⟩)
  server_dref := hm (.multiplicity 6 ⟨.dereference, rfl⟩)

theorem operands_defined (m : glued.carrier ⥤q semanticGraph U)
    (hm : LocalHolds m) (R : IntegerRealization U)
    (hd : (navigation m).obj (5 : VersionNavigation.support.Vertex) = R.domain)
    (d : Subtype ((navigation m).obj (0 : VersionNavigation.support.Vertex))) :
    R.WellDefined ((versionModel m hm R hd).versionObjects {d.val}) ∧
    R.WellDefined ((versionModel m hm R hd).versionObjects
      ((versionModel m hm R hd).serverObjects d)) :=
  (versionModel m hm R hd).operands_defined d

theorem comparison_defined (m : glued.carrier ⥤q semanticGraph U)
    (hm : LocalHolds m) (R : IntegerRealization U)
    (hd : (navigation m).obj (5 : VersionNavigation.support.Vertex) = R.domain)
    (d : Subtype ((navigation m).obj (0 : VersionNavigation.support.Vertex))) :
    ∃ b, VersionNavigation.compareVersions R ((versionModel m hm R hd).versionObjects {d.val})
      ((versionModel m hm R hd).versionObjects ((versionModel m hm R hd).serverObjects d)) = some b :=
  (versionModel m hm R hd).comparison_defined d

end Clafer.Examples.VersionCompilation
