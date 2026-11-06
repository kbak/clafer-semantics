module

public import Clafer.Constraints.Integer
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
[impl->req~clafer-version-navigation~1]
[proof->req~clafer-version-navigation~1]
-/

/-!
# Appendix 6 version navigation

SoSyM Appendix 6 PDF p.34, D.3–D.4, §5.3 and §5.5. The selected fragment keeps
reference objects, head/dereference maps and both inheritance inclusions.
The omitted multiplicities of version and server are 1..1. In particular,
Appendix 6's comparison has no Figure 21 nonempty-server guard.
This is a conditional navigation theorem, not a whole-model interpretation.
-/

@[expose] public section
universe u w
namespace Clafer.Constraints.VersionNavigation
open CategoryTheory DPGraph.Predicates

/-- Resolved IDs of the selected Appendix 6 fragment (names are only metadata). -/
def rootDecl : Declaration := { id := ⟨0⟩, name := "root", origin := .syntheticRoot }
def intDecl : Declaration := { id := ⟨1⟩, name := "int", origin := .primitive .int }
def compDecl : Declaration :=
  { id := ⟨2⟩, name := "comp", authoredAbstract := true, isAbstract := true }
def versionDecl : Declaration :=
  { id := ⟨3⟩, name := "version", reference := .set ⟨1⟩, isAbstract := true }
def ecuDecl : Declaration :=
  { id := ⟨4⟩, name := "ECU", super := some ⟨2⟩,
    authoredAbstract := true, isAbstract := true }
def displayDecl : Declaration :=
  { id := ⟨5⟩, name := "display", super := some ⟨2⟩,
    authoredAbstract := true, isAbstract := true }
def serverDecl : Declaration :=
  { id := ⟨6⟩, name := "server", reference := .set ⟨4⟩, isAbstract := true }

def fragment : AST := ⟨⟨0⟩, [Tree.branch rootDecl [Tree.branch intDecl []],
  Tree.branch compDecl [Tree.branch versionDecl []], Tree.branch ecuDecl [],
  Tree.branch displayDecl [Tree.branch serverDecl []]]⟩

theorem fragment_entries : fragment.entries =
    [⟨rootDecl, none, 0⟩, ⟨intDecl, some ⟨0⟩, 1⟩, ⟨compDecl, none, 0⟩,
     ⟨versionDecl, some ⟨2⟩, 1⟩, ⟨ecuDecl, none, 0⟩,
     ⟨displayDecl, none, 0⟩, ⟨serverDecl, some ⟨5⟩, 1⟩] := rfl

@[simp] theorem fragment_root : fragment.root = ⟨0⟩ := rfl

theorem fragment_wellFormed : fragment.WellFormed := by
  constructor
  all_goals try { simp [AST.Known, fragment_entries, rootDecl, intDecl,
    compDecl, versionDecl, ecuDecl, displayDecl, serverDecl,
    Reference.kind, Reference.target, Kind.CanExtend, PrimitiveDomain.name,
    ValidRange, GroupCard.range, Clafer.one, unrestricted] }
  · refine ⟨fun i => if i = ⟨4⟩ ∨ i = ⟨5⟩ then 1 else 0, ?_⟩
    simp [fragment_entries, rootDecl, intDecl, compDecl, versionDecl,
      ecuDecl, displayDecl, serverDecl]
  · intro d hd hu p s hp hpm hs hsm
    simp only [fragment_entries, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases p <;> cases s <;>
      simp_all [fragment_entries, rootDecl, intDecl, compDecl, versionDecl,
        ecuDecl, displayDecl, serverDecl, Defaults, GroupCard.childDefault]
    all_goals aesop

/-- The bounds used below are the actual defaulted declarations in this fragment. -/
theorem default_multiplicities :
    versionDecl.multiplicity.effective = Clafer.one ∧
    serverDecl.multiplicity.effective = Clafer.one := ⟨rfl, rfl⟩

/-- display, ECU, comp, version-reference, server-reference, integer. -/
abbrev support : Support where
  classCount := 6
  mapCount := 6
  classId := ![⟨5⟩, ⟨4⟩, ⟨2⟩, ⟨3⟩, ⟨6⟩, ⟨1⟩]
  mapRef := ![⟨⟨5⟩, .inclusion, 0, 2, "isA"⟩,
    ⟨⟨4⟩, .inclusion, 1, 2, "isA"⟩,
    ⟨⟨3⟩, .head, 2, 3, "version"⟩,
    ⟨⟨3⟩, .dereference, 3, 5, "dref"⟩,
    ⟨⟨6⟩, .head, 0, 4, "server"⟩,
    ⟨⟨6⟩, .dereference, 4, 1, "dref"⟩]
  context := 0
  integer := fun v => v == 5

theorem support_resolved : support.Resolved fragment := by
  constructor
  · intro v
    fin_cases v <;> simp [AST.Known, fragment_entries, support,
      rootDecl, intDecl, compDecl, versionDecl, ecuDecl, displayDecl, serverDecl]
  · intro e
    fin_cases e <;> simp [Support.MapResolved, fragment_entries, support,
      rootDecl, intDecl, compDecl, versionDecl, ecuDecl, displayDecl, serverDecl,
      Reference.target]
  · intro v hv
    fin_cases v <;> simp_all [support, fragment_entries,
      rootDecl, intDecl, compDecl, versionDecl, ecuDecl, displayDecl, serverDecl]

def displayWiden : Widen support 0 2 := .inclusion 0 rfl
def ecuWiden : Widen support 1 2 := .inclusion 1 rfl

def version {Γ} (c : Expr support Γ (.collection (.objects 2))) :
    Expr support Γ .integer := .integerOf rfl (.image (.image c (.map 2)) (.map 3))

def displayVersion {Γ} : Expr support Γ .integer := version (.widenObjects displayWiden .this)
def serverVersion {Γ} : Expr support Γ .integer :=
  version (.widenObjects ecuWiden (.image (.image .this (.map 4)) (.map 5)))

/-- Accepted Q7 direction: display.version >= server.version. -/
def comparison : Expr support [] .boolean := .not (.less displayVersion serverVersion)

def constraint : Constraint := ⟨support, [], comparison⟩
abbrev boundary : ConstraintBoundary :=
  { id := 67, context := ⟨5⟩, scopeOccurrences := [⟨5⟩, ⟨4⟩, ⟨2⟩, ⟨3⟩, ⟨6⟩, ⟨1⟩] }

theorem constraint_input : constraint.Input fragment boundary where
  ast := fragment_wellFormed
  resolved := support_resolved
  boundary_resolved := by
    simp [ConstraintBoundary.Resolved, AST.Known, fragment_entries,
      rootDecl, intDecl, compDecl, versionDecl, ecuDecl, displayDecl, serverDecl]
  boundary := ⟨{
    context_eq := rfl
    occurrence := fun i => i
    occurrence_eq := by intro i; fin_cases i <;> rfl
    domain := fun b => Fin.elim0 b
    domain_eq := fun b => Fin.elim0 b }⟩
  locals_match := rfl
  domains := ⟨.nil⟩

/-- Selected multiplicities plus the reference-function discipline. No final
singleton or numeric inequality is assumed. Other Appendix 6 constraints belong
to the whole-model interpreter; e.g. server = parent further restricts the server. -/
structure Model (U : Type u) extends IntegerBinding.{u,w} support U where
  version_head : TargetMultiplicity versionDecl.multiplicity.effective (model.map (support.arrow 2))
  version_dref : TargetMultiplicity Clafer.one (model.map (support.arrow 3))
  server_head : TargetMultiplicity serverDecl.multiplicity.effective (model.map (support.arrow 4))
  server_dref : TargetMultiplicity Clafer.one (model.map (support.arrow 5))

def Model.versionObjects {U} (m : Model.{u,w} U) (values : Set U) : Set U :=
  navigationImage (m.model.map (support.arrow 3))
    (navigationImage (m.model.map (support.arrow 2)) values)

def Model.serverObjects {U} (m : Model.{u,w} U) (d : Subtype (m.model.obj (0 : support.Vertex))) : Set U :=
  navigationImage (m.model.map (support.arrow 5))
    (navigationImage (m.model.map (support.arrow 4)) {d.val})

/-- The two reference steps are functional by the head and dereference bounds. -/
theorem Model.version_singleton {U} (m : Model.{u,w} U) (c : Subtype (m.model.obj (2 : support.Vertex))) :
    ∃ x : Subtype (m.model.obj (5 : support.Vertex)), m.versionObjects {c.val} = {x.val} := by
  obtain ⟨v, hv⟩ := navigationImage_one _ m.version_head c
  obtain ⟨x, hx⟩ := navigationImage_one _ m.version_dref v
  exact ⟨x, by unfold versionObjects; rw [hv, hx]⟩

theorem Model.server_singleton {U} (m : Model.{u,w} U) (d : Subtype (m.model.obj (0 : support.Vertex))) :
    ∃ e : Subtype (m.model.obj (1 : support.Vertex)), m.serverObjects d = {e.val} := by
  obtain ⟨s, hs⟩ := navigationImage_one _ m.server_head d
  obtain ⟨e, he⟩ := navigationImage_one _ m.server_dref s
  exact ⟨e, by unfold serverObjects; rw [hs, he]⟩

/-- Well-definedness for both actual Appendix 6 operands, including inherited
version access. No absent-server guard is needed or inserted. -/
theorem Model.operands_defined {U} (m : Model.{u,w} U) (d : Subtype (m.model.obj (0 : support.Vertex))) :
    m.realization.WellDefined (m.versionObjects {d.val}) ∧
    m.realization.WellDefined (m.versionObjects (m.serverObjects d)) := by
  have hd := m.toIntegerBinding.widen_subset displayWiden d.property
  obtain ⟨v, hv⟩ := m.version_singleton ⟨d.val, hd⟩
  obtain ⟨e, he⟩ := m.server_singleton d
  have hec := m.toIntegerBinding.widen_subset ecuWiden e.property
  obtain ⟨s, hs⟩ := m.version_singleton ⟨e.val, hec⟩
  have dom := m.integer_domain 5 rfl
  exact ⟨⟨v.val, hv, dom ▸ v.property⟩,
    ⟨s.val, by rw [he]; exact hs, dom ▸ s.property⟩⟩

/-- Partial evaluation of exactly the displayed comparison. The general expression
interpreter can consume this interface; this is not Figure 21's VC interpretation. -/
noncomputable def compareVersions {U : Type u} (R : IntegerRealization U)
    (displayValues serverValues : Set U) : Option Bool := do
  let d ← R.extract displayValues
  let e ← R.extract serverValues
  pure (decide (e ≤ d))

theorem compareVersions_encoded {U : Type u} (R : IntegerRealization U) (d e : Int) :
    compareVersions R {R.encode d} {R.encode e} = some (decide (e ≤ d)) := by
  simp [compareVersions, IntegerRealization.extract_encoded]

/-- The semantic comparison agrees with the not/less form in `comparison`. -/
theorem compareVersions_not_less {U : Type u} (R : IntegerRealization U) (d e : Int) :
    compareVersions R {R.encode d} {R.encode e} = some (!decide (d < e)) := by
  rw [compareVersions_encoded]
  by_cases h : e ≤ d
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

/-- Definedness is independent of whether the comparison is true or false. -/
theorem Model.comparison_defined {U} (m : Model.{u,w} U) (d : Subtype (m.model.obj (0 : support.Vertex))) :
    ∃ result, compareVersions m.realization (m.versionObjects {d.val})
      (m.versionObjects (m.serverObjects d)) = some result := by
  obtain ⟨hd, he⟩ := m.operands_defined d
  obtain ⟨nd, hd⟩ := (m.realization.wellDefined_iff _).mp hd
  obtain ⟨ne, he⟩ := (m.realization.wellDefined_iff _).mp he
  rw [IntegerRealization.Extracts] at hd he
  rw [hd, he, compareVersions_encoded]
  exact ⟨_, rfl⟩

end Clafer.Constraints.VersionNavigation
