module

public import Clafer.Constraints.Typing
public import Clafer.Examples
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
[proof->req~clafer-core-binding~1]
[proof->req~clafer-core-support~1]
[proof->req~clafer-core-typing~1]
-/

/-! # Positive and rejected core typing examples (SoSyM D.1–D.3)

The `fail_if_success` assertions exercise Lean's elaboration of the actual
indexed constructors. They are typing regressions, not semantic theorems.
-/

@[expose] public section
namespace Clafer.Constraints.Examples
open Clafer.Examples CategoryTheory

/-- Two vertices deliberately denote basicDecl; position identity is preserved. -/
abbrev support : Support where
  classCount := 5
  mapCount := 7
  classId := ![⟨0⟩, ⟨7⟩, ⟨6⟩, ⟨2⟩, ⟨2⟩]
  mapRef := ![
    ⟨⟨7⟩, .head, 0, 1, "derived"⟩,
    ⟨⟨7⟩, .dereference, 1, 3, "dref"⟩,
    ⟨⟨6⟩, .dereference, 2, 3, "dref"⟩,
    ⟨⟨7⟩, .inclusion, 1, 2, ""⟩,
    ⟨⟨7⟩, .parent, 1, 0, "parent"⟩,
    ⟨⟨7⟩, .target, 0, 3, "target"⟩,
    ⟨⟨7⟩, .dereference, 1, 3, "dref"⟩]
  context := 1

theorem support_resolved : support.Resolved sample := by
  constructor
  · intro v
    fin_cases v <;> simp [support, AST.Known, sample_entries,
      rootDecl, basicDecl, derivedDecl, abstractRefDecl]
  · intro e
    fin_cases e <;> simp [Support.MapResolved, support, sample_entries,
      rootDecl, intDecl, basicDecl, setDecl, bagDecl, derivedDecl,
      abstractDecl, abstractChild, abstractRefDecl, Reference.target]
  · intro v h; cases h

def inherited : Widen support 1 2 := .inclusion 3 rfl

theorem widening_follows_super : Extends sample ⟨7⟩ ⟨6⟩ :=
  inherited.resolved support_resolved

def navigation {Γ} : Expr support Γ (.collection (.objects 3)) :=
  .image .this (.map 1)

def inheritedNavigation {Γ} : Expr support Γ (.collection (.objects 3)) :=
  .image (.widenObjects inherited .this) (.map 2)

def composed : Expr support [] (.collection (.relation 0 3)) :=
  .join (.map 0) (.map 1)

def inheritedJoin : Expr support [] (.collection (.relation 0 3)) :=
  .join (.widenRelation (.refl 0) inherited (.map 0)) (.map 2)

def compatibleUnion : Expr support [] (.collection (.relation 2 3)) :=
  .setOp .union (.widenRelation inherited (.refl 3) (.map 1)) (.map 2)

def duplicateIdentity : Expr support [] (.collection (.objects 4)) :=
  .widenObjects (.same (x := 3) (y := 4) rfl) navigation

def b : Local support := ⟨⟨10⟩, "x", 3⟩
def inner : Local support := ⟨⟨11⟩, "x", 3⟩

theorem b_fresh : ∀ old ∈ ([] : List (Local support)), old.id ≠ b.id := by simp

def quantified : Expr support [] .boolean :=
  .all b b_fresh navigation (.subset (.var .here) navigation)

def nested : Expr support [] .boolean :=
  .all b b_fresh navigation
    (.all inner (by simp [b, inner]) (.var .here)
      (.equal (.var .here) (.var (.there .here))))

theorem shadowed_name_keeps_ids : b.name = inner.name ∧ b.id ≠ inner.id := by decide

theorem outer_variable_position :
    (Var.there (Var.here (b := b) (Γ := [])) (b := inner)).index = 1 := rfl

def numericConstraint : Expr support [] .boolean :=
  .and (.less (.arithmetic .add (.cardinality navigation) (.integer 1)) (.integer 3))
    (.equal (.arithmetic .subtract (.integer 3) (.integer 1)) (.integer 2))

def collectionConstraint : Expr support [] .boolean :=
  .and (.some (.setOp .intersection navigation navigation))
    (.and (.no (.setOp .difference navigation navigation))
      (.and (.one navigation) (.lone (.setOp .union navigation navigation))))

def relationConstraint : Expr support [] .boolean :=
  .and (.subset (.setOp .intersection (.map 1) (.map 6)) (.map 1))
    (.not (.equal (.cardinality (.setOp .difference (.map 1) (.map 6))) (.integer 1)))

def path : Path support 1 3 := .cons 4 rfl (.cons 0 rfl (.cons 1 rfl (.nil 3)))
noncomputable def pathNavigation : Expr support [] (.collection (.objects 3)) := path.navigate .this

abbrev boundary : ConstraintBoundary :=
  { id := 21, context := ⟨7⟩, scopeOccurrences := [⟨2⟩, ⟨2⟩, ⟨6⟩, ⟨7⟩, ⟨0⟩] }

def boundaryBinding : support.Boundary boundary where
  context_eq := rfl
  occurrence := ![3, 4, 2, 1, 0]
  occurrence_eq := by intro i; fin_cases i <;> rfl
  domain b := Fin.elim0 b
  domain_eq b := Fin.elim0 b

theorem repeated_scope_retained :
    boundaryBinding.occurrence 0 ≠ boundaryBinding.occurrence 1 ∧
    support.classId (boundaryBinding.occurrence 0) =
      support.classId (boundaryBinding.occurrence 1) := by decide

def constraint : Constraint := ⟨support, [], quantified⟩

theorem constraint_input : constraint.Input sample boundary where
  ast := sample_wellFormed
  resolved := support_resolved
  boundary_resolved := by
    simp [ConstraintBoundary.Resolved, AST.Known, sample_entries,
      rootDecl, basicDecl, derivedDecl, abstractRefDecl]
  boundary := ⟨boundaryBinding⟩
  locals_match := rfl
  domains := ⟨.nil⟩

def resolvedConstraint : ResolvedConstraint sample := ⟨boundary, constraint, constraint_input⟩

abbrev externalBoundary : ConstraintBoundary :=
  { boundary with binders := [⟨b.id, b.name, [⟨2⟩, ⟨2⟩]⟩] }

def externalBoundaryBinding : support.Boundary externalBoundary where
  context_eq := rfl
  occurrence := boundaryBinding.occurrence
  occurrence_eq := boundaryBinding.occurrence_eq
  domain _ i := if i.val = 0 then 3 else 4
  domain_eq := by intro j i; fin_cases j; fin_cases i <;> rfl

def externalConstraint : Constraint := ⟨support, [b], .some (.var .here)⟩

theorem external_input : externalConstraint.Input sample externalBoundary where
  ast := sample_wellFormed
  resolved := support_resolved
  boundary_resolved := by
    simp [ConstraintBoundary.Resolved, b, AST.Known,
      sample_entries, rootDecl, basicDecl, derivedDecl, abstractRefDecl]
  boundary := ⟨externalBoundaryBinding⟩
  locals_match := rfl
  domains := ⟨.cons b .nil (by simp) navigation⟩

theorem repeated_domain_retained :
    externalBoundaryBinding.domain 0 ⟨0, by decide⟩ ≠ externalBoundaryBinding.domain 0 ⟨1, by decide⟩ ∧
    support.classId (externalBoundaryBinding.domain 0 ⟨0, by decide⟩) =
      support.classId (externalBoundaryBinding.domain 0 ⟨1, by decide⟩) := by decide

def externalDomains : Domains support [inner, b] :=
  .cons inner (.cons b .nil (by simp) navigation)
    (by simp [b, inner]) (.var .here)

def formula : DPGraph.Formula (signature (fun _ : Unit => constraint)) support.graph :=
  Constraint.formula (fun _ : Unit => constraint) () (Prefunctor.id support.graph)

theorem full_graph_binding : formula.binding = Prefunctor.id support.graph := rfl

theorem repeated_maps_retained : support.mapRef 1 = support.mapRef 6 ∧
    support.arrow 1 ≠ support.arrow 6 := by
  constructor
  · rfl
  · intro h
    have he := congrArg Subtype.val h
    exact (by decide : (1 : support.Edge) ≠ 6) he

theorem wrong_image_rejected : True := by
  fail_if_success
    have _ : Expr support [] (.collection (.objects 1)) := .image .this (.map 0)
  trivial

theorem wrong_join_rejected : True := by
  fail_if_success
    have _ : Expr support [] (.collection (.relation 0 3)) := .join (.map 0) (.map 2)
  trivial

theorem mixed_collection_rejected : True := by
  fail_if_success
    have _ : Expr support [] (.collection (.objects 3)) := .setOp .union navigation (.map 1)
  trivial

theorem nonboolean_body_rejected : True := by
  fail_if_success
    have _ : Expr support [] .boolean := .all b b_fresh navigation (.var .here)
  trivial

theorem relation_domain_rejected : True := by
  fail_if_success
    have _ : Expr support [] .boolean := .all b b_fresh (.map 1) (.boolean true)
  trivial

theorem out_of_scope_rejected : True := by
  fail_if_success
    have _ : Expr support [] (.collection (.objects 3)) := .var .here
  trivial

theorem domain_cannot_use_own_binder : True := by
  fail_if_success
    have _ : Expr support [] .boolean := .all b b_fresh (.var .here) (.boolean true)
  trivial

theorem bare_set_is_not_boolean : True := by
  fail_if_success
    have _ : Expr support [] .boolean := navigation
  trivial

theorem boolean_arithmetic_rejected : True := by
  fail_if_success
    have _ : Expr support [] .integer := .arithmetic .add (.boolean true) (.integer 1)
  trivial

theorem integer_cardinality_rejected : True := by
  fail_if_success
    have _ : Expr support [] .integer := .cardinality (.integer 1)
  trivial

theorem mixed_equality_rejected : True := by
  fail_if_success
    have _ : Expr support [] .boolean := .equal navigation (.integer 1)
  trivial

theorem duplicate_binder_id_rejected : ¬(∀ old ∈ [b], old.id ≠ b.id) := by simp

theorem non_inclusion_cannot_widen : (support.mapRef 1).kind ≠ .inclusion := by decide

theorem unrelated_widening_rejected : IsEmpty (Widen support 1 0) := by
  constructor
  intro w
  have step : ∀ x y, DirectSuper sample x y →
      (x = ⟨7⟩ ∨ x = ⟨6⟩) → (y = ⟨7⟩ ∨ y = ⟨6⟩) := by
    intro x y h _
    simp [DirectSuper, sample_entries, rootDecl, intDecl, basicDecl, setDecl,
      bagDecl, derivedDecl, abstractDecl, abstractChild, abstractRefDecl] at h
    exact Or.inr h.2.symm
  have h := (w.resolved support_resolved).preserves step (Or.inl rfl)
  change (⟨0⟩ : DeclId) = ⟨7⟩ ∨ (⟨0⟩ : DeclId) = ⟨6⟩ at h
  rcases h with h | h <;> cases h

theorem wrong_map_incidence_rejected : IsEmpty (support.Arrow 0 2) := by
  constructor
  rintro ⟨e, h⟩
  fin_cases e <;> simp [support] at h

end Clafer.Constraints.Examples
