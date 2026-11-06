module

public import Clafer.Compile.Basic
public import Clafer.Constraints.Examples

/-!
[proof->req~clafer-compile-contract~1]
[proof->req~clafer-compile-formulas~1]
[proof->req~clafer-compile-group-data~1]
[proof->req~clafer-compile-structure~1]
-/

/-! # Compile acceptance examples: identity, sharing, bindings and rejected inputs -/

@[expose] public section
namespace Clafer.Compile.Examples
open Clafer.Examples CategoryTheory

/-- Two constraint positions deliberately have the same source boundary number. -/
def withConstraints : Declaration := { derivedDecl with constraints := [Clafer.Constraints.Examples.boundary, Clafer.Constraints.Examples.boundary] }
def nestedDecl : Declaration :=
  { id := ⟨9⟩, name := "same", group := ⟨some .xor, .xor⟩ }

def ast : AST := ⟨⟨0⟩,
  [.branch rootDecl [.branch intDecl [], .branch basicDecl [.branch nestedDecl []],
    .branch setDecl [], .branch bagDecl [], .branch withConstraints []],
   .branch abstractDecl [.branch abstractChild []], .branch abstractRefDecl []]⟩

theorem entries : ast.entries =
    [⟨rootDecl, none, 0⟩, ⟨intDecl, some ⟨0⟩, 1⟩, ⟨basicDecl, some ⟨0⟩, 1⟩,
     ⟨nestedDecl, some ⟨2⟩, 2⟩, ⟨setDecl, some ⟨0⟩, 1⟩, ⟨bagDecl, some ⟨0⟩, 1⟩,
     ⟨withConstraints, some ⟨0⟩, 1⟩, ⟨abstractDecl, none, 0⟩,
     ⟨abstractChild, some ⟨5⟩, 1⟩, ⟨abstractRefDecl, none, 0⟩] := rfl

@[simp] theorem ast_root : ast.root = ⟨0⟩ := rfl

theorem ast_wellFormed : ast.WellFormed := by
  constructor
  all_goals try { simp [AST.Known, entries, rootDecl, intDecl, basicDecl, nestedDecl,
    setDecl, bagDecl, withConstraints, derivedDecl, abstractDecl, abstractChild, abstractRefDecl,
    Reference.kind, Reference.target, Kind.CanExtend, PrimitiveDomain.name, ValidRange,
    GroupCard.range, Clafer.one, unrestricted, ConstraintBoundary.Resolved, Clafer.Constraints.Examples.boundary] }
  · refine ⟨fun i => if i = ⟨7⟩ then 1 else 0, ?_⟩
    simp [entries, rootDecl, intDecl, basicDecl, nestedDecl, setDecl, bagDecl,
      withConstraints, derivedDecl, abstractDecl, abstractChild, abstractRefDecl]
  · intro d hd hu p s hp hpm hs hsm
    simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases p <;> cases s <;>
      simp_all [entries, rootDecl, intDecl, basicDecl, nestedDecl, setDecl, bagDecl,
        withConstraints, derivedDecl, abstractDecl, abstractChild, abstractRefDecl,
        Defaults, GroupCard.childDefault]
    all_goals aesop

theorem constraint_boundary (q : ConstraintId ast) : boundary ast q = Clafer.Constraints.Examples.boundary := by
  obtain ⟨c, k⟩ := q
  change Fin 10 at c
  fin_cases c <;> fin_cases k <;> rfl

theorem constraint_typed (q : ConstraintId ast) : Clafer.Constraints.Examples.constraint.Input ast (boundary ast q) := by
  rw [constraint_boundary]
  refine ⟨ast_wellFormed, ?_, ?_, ⟨Clafer.Constraints.Examples.boundaryBinding⟩, rfl, ⟨.nil⟩⟩
  · constructor
    · intro v
      fin_cases v <;> simp [Clafer.Constraints.Examples.constraint, Clafer.Constraints.Examples.support, AST.Known, entries,
        rootDecl, basicDecl, withConstraints, derivedDecl, abstractRefDecl]
    · intro e
      fin_cases e <;> simp [Constraints.Support.MapResolved, Clafer.Constraints.Examples.constraint, Clafer.Constraints.Examples.support, entries,
        rootDecl, intDecl, basicDecl, nestedDecl, withConstraints, derivedDecl,
        setDecl, bagDecl, abstractDecl, abstractChild, abstractRefDecl, Reference.target]
    · intro v h; cases h
  · simp [ConstraintBoundary.Resolved, Clafer.Constraints.Examples.boundary, AST.Known, entries,
      rootDecl, basicDecl, withConstraints, derivedDecl, abstractRefDecl]

noncomputable def input : Input ast where
  ast := ast_wellFormed
  root_name := by
    intro d hd; simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  user_names := by
    intro d hd; simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [rootDecl, intDecl, basicDecl, nestedDecl, setDecl, bagDecl,
      withConstraints, derivedDecl, abstractDecl, abstractChild, abstractRefDecl,
      MCS.predefinedStrings]
    all_goals intro dom; cases dom <;> decide
  constraint _ := Clafer.Constraints.Examples.constraint
  typed := constraint_typed
  positive_support _ := by decide

noncomputable def result := compile input

/-- Root, nine declarations, two constraint occurrences, and a reference cycle. -/
theorem output_valid : MCS.Valid result.labels result.formulas := wellFormed input

def basic : ast.Occurrence := ⟨2, by decide⟩
def nested : ast.Occurrence := ⟨3, by decide⟩
def derived : ast.Occurrence := ⟨6, by decide⟩
def abstractRef : ast.Occurrence := ⟨9, by decide⟩
def q0 : ConstraintId ast := ⟨derived, ⟨0, by decide⟩⟩
def q1 : ConstraintId ast := ⟨derived, ⟨1, by decide⟩⟩

theorem nested_repeated_names :
    result.labels.className (result.roles.head basic) = "same" ∧
    result.labels.className (result.roles.head nested) = "same" ∧
    result.roles.head basic ≠ result.roles.head nested ∧
    result.family.parent nested = some basic := by
  exact ⟨rfl, rfl, fresh_heads input (by decide), rfl⟩

theorem shared_reference_target :
    (result.family.reference derived).target = some basic ∧
    (result.family.reference abstractRef).target = some basic ∧
    result.roles.head derived ≠ result.roles.head abstractRef :=
  ⟨rfl, rfl, fresh_heads input (by decide)⟩

noncomputable def derivedDref : result.family.MapId := .ordinary derived ⟨.dereference, rfl⟩
noncomputable def abstractDref : result.family.MapId := .ordinary abstractRef ⟨.dereference, rfl⟩

theorem shared_target_distinct_dereferences :
    result.roles.target derivedDref = result.roles.target abstractDref ∧
    result.labels.mapName derivedDref = result.labels.mapName abstractDref ∧
    derivedDref ≠ abstractDref := by
  refine ⟨rfl, rfl, ?_⟩
  exact fresh_maps input (by decide) _ _

theorem inheritance_preserved : result.family.super derived = some abstractRef := rfl

/-- A childless xor remains accepted structural input. The structural result alone
retains metadata; the augmented result supplies the separate empty-group predicate. -/
theorem empty_xor_metadata_preserved :
    result.family.group nested = ⟨some .xor, .xor⟩ := rfl

theorem nested_has_no_direct_children : IsEmpty (DirectChild input nested) := by
  refine ⟨fun c => ?_⟩
  have h := (directChild_iff input nested c.val).mp c.property
  obtain ⟨c, _⟩ := c
  change Fin 10 at c
  fin_cases c <;> cases h

noncomputable def nestedChild : DirectChild input basic := ⟨nested, rfl⟩

theorem nested_child_head_incidence :
    result.roles.source (directChildHead input basic nestedChild).val = basic ∧
    result.roles.target (directChildHead input basic nestedChild).val = nested :=
  (directChildHead input basic nestedChild).property

noncomputable def derivedChild : DirectChild input result.family.root := ⟨derived, rfl⟩

/-- The selected reference-child map ends at its head although its target is
the distinct basic declaration. -/
theorem reference_child_head_not_target :
    result.roles.target (directChildHead input result.family.root derivedChild).val = derived ∧
    (result.family.reference derived).target = some basic ∧ derived ≠ basic :=
  ⟨rfl, rfl, by decide⟩

theorem repeated_support_maps :
    (⟨1, by decide⟩ : (support input q0).Edge) ≠ ⟨6, by decide⟩ ∧
    ((binding input q0).map ((support input q0).arrow ⟨1, by decide⟩)).val =
    ((binding input q0).map ((support input q0).arrow ⟨6, by decide⟩)).val :=
  ⟨by decide, rfl⟩

theorem repeated_support_vertices :
    (⟨3, by decide⟩ : (support input q0).Vertex) ≠ ⟨4, by decide⟩ ∧
    (binding input q0).obj ⟨3, by decide⟩ = (binding input q0).obj ⟨4, by decide⟩ :=
  ⟨by decide, rfl⟩

theorem repeated_constraint_boundaries : boundary ast q0 = boundary ast q1 ∧
    q0 ≠ q1 ∧ (formula input (.inr q0)).symbol ≠ (formula input (.inr q1)).symbol := by
  refine ⟨rfl, ?_, ?_⟩
  · decide
  · intro h; exact (by decide : q0 ≠ q1) (Sum.inr.inj h)

theorem compiled_constraint_present : formula input (.inr q0) ∈
    result.formulas.diagram.declarations := constraint_declared input q0

theorem primitive_identity : result.family.origin ⟨1, by decide⟩ = .primitive .int ∧
    result.labels.className ⟨1, by decide⟩ = "int" ∧
    result.family.origin basic = .user := ⟨rfl, rfl, rfl⟩

/-- Reserved spelling cannot silently turn a user into a primitive domain. -/
theorem reserved_user_rejected (a : AST) (d : Located) (hd : d ∈ a.entries)
    (hu : d.declaration.origin = .user) (hn : d.declaration.name = "int") :
    ¬Nonempty (Input a) := by
  rintro ⟨i⟩
  exact i.user_names d hd hu (Or.inr ⟨.int, hn⟩)

theorem zero_map_rejected {a : AST} (i : Input a) (q : ConstraintId a)
    (hz : (i.constraint q).support.mapCount = 0) : False := by
  have hp := i.positive_support q
  omega

/-- Position 4 is isolated, but its class binding is still retained. -/
theorem isolated_vertex_retained :
    (∀ e : (support input q0).Edge,
      ((support input q0).mapRef e).source ≠ ⟨4, by decide⟩ ∧
      ((support input q0).mapRef e).target ≠ ⟨4, by decide⟩) ∧
    (binding input q0).obj ⟨4, by decide⟩ = basic := by
  constructor
  · intro e; fin_cases e <;> decide
  · rfl

def zeroSupport : Constraints.Support :=
  { Clafer.Constraints.Examples.support with mapCount := 0, mapRef := Fin.elim0 }
def zeroConstraint : Constraints.Constraint := ⟨zeroSupport, [], .boolean true⟩

/-- Zero-map Boolean input remains legal at the generic typing boundary. -/
theorem zero_generic_input : zeroConstraint.Input ast (boundary ast q0) := by
  rw [constraint_boundary]
  refine ⟨ast_wellFormed, ⟨?_, ?_, ?_⟩, ?_, ?_, rfl, ⟨.nil⟩⟩
  · exact (constraint_typed q0).resolved.classes
  · intro e; exact Fin.elim0 e
  · exact (constraint_typed q0).resolved.integers
  · exact (Clafer.Compile.Examples.constraint_typed q0).boundary_resolved
  · exact ⟨{
      context_eq := rfl
      occurrence := Clafer.Constraints.Examples.boundaryBinding.occurrence
      occurrence_eq := Clafer.Constraints.Examples.boundaryBinding.occurrence_eq
      domain := fun b => Fin.elim0 b
      domain_eq := fun b => Fin.elim0 b }⟩

theorem zero_not_compile_support : ¬0 < zeroConstraint.support.mapCount := by decide

end Clafer.Compile.Examples
