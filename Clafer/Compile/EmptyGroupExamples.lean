module

public import Clafer.Compile.GroupExamples

-- [proof->req~clafer-compile-groups~1]

/-! # Zero-arrow group supports retain literal empty-inventory semantics -/

@[expose] public section
namespace Clafer.Compile.EmptyGroupExamples
open CategoryTheory MCS DPGraph DPGraph.Predicates Semantics

def decl (g : GroupCard) : Declaration := { GroupExamples.root with group := ⟨some g, g⟩ }
def ast (g : GroupCard) : AST := ⟨⟨0⟩, [.branch (decl g) []]⟩

instance ast_nonzero (g) : NeZero (ast g).entries.length := ⟨by change (1 : Nat) ≠ 0; decide⟩

theorem wf (g : GroupCard) (valid : ValidRange g.range) : (ast g).WellFormed := by
  constructor
  all_goals try { simp [ast, AST.entries, AST.Known, Tree.branch, Tree.entries,
    Forest.ofList, decl, GroupExamples.root, Reference.target, ValidRange, one] }
  simpa [ast, AST.entries, Tree.branch, Tree.entries, Forest.ofList, decl, GroupExamples.root, ValidRange, one] using valid

theorem no_constraints (g : GroupCard) (q : ConstraintId (ast g)) : False := by
  rcases q with ⟨c, k⟩
  change Fin 1 at c
  fin_cases c
  exact Fin.elim0 k

noncomputable def input (g : GroupCard) (valid : ValidRange g.range) : Input (ast g) where
  ast := wf g valid
  root_name := by
    intro d hd
    simp [ast, AST.entries, Tree.branch, Tree.entries, Forest.ofList] at hd
    subst d; intro _; rfl
  user_names := by
    intro d hd
    simp [ast, AST.entries, Tree.branch, Tree.entries, Forest.ofList] at hd
    subst d; intro h; cases h
  constraint q := (no_constraints g q).elim
  typed q := (no_constraints g q).elim
  positive_support q := (no_constraints g q).elim

variable (g : GroupCard) (valid : ValidRange g.range)

theorem inventory_empty : IsEmpty (Groups.Child (family (input g valid)) 0) := by
  constructor
  rintro ⟨s, c, hc⟩
  change Fin 1 at c
  fin_cases c
  cases hc

theorem no_support_arrows (x y : Groups.arity (family (input g valid)) 0)
    (e : x ⟶ y) : False := by
  cases e with
  | head c => exact (inventory_empty g valid).false c
  | inclusion s t h =>
    rcases s with ⟨s, _⟩
    change Fin 1 at s
    fin_cases s
    cases h

/-- No map role exists, so adding an artificial nonempty support is impossible. -/
theorem no_role_maps : IsEmpty (family (input g valid)).MapId := by
  constructor
  intro m
  cases m with
  | ordinary c r =>
    change Fin 1 at c
    fin_cases c
    rcases r with ⟨r, h⟩
    cases r <;> cases h
  | inclusion slot =>
    rcases slot with ⟨c, s, r, h⟩
    change Fin 1 at c
    fin_cases c
    cases h

def config (inhabited : Bool) : Configuration (Fin 1) Unit where
  root := ()
  head _ := { _x | inhabited = true }
  contains _ _ _ := False
  deref _ _ _ := False

theorem typed (b : Bool) : (config b).Typed (EffectiveCore.erase (input g valid)) :=
  ⟨fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩

noncomputable def authored :
    Interpretation (Constraints.signature (input g valid).constraint) (semanticGraph Unit) :=
  ⟨fun q => (no_constraints g q).elim⟩

noncomputable def Accepted (b : Bool) : Prop :=
  (groupInterpretation (input g valid) Unit (authored g valid)).Satisfies
    (descendGroups (input g valid) (config b))
    ((generatedGroup (input g valid) ⟨0, rfl⟩).translate (groupLabel (input g valid)))

theorem accepted_iff (b : Bool) : Accepted g valid b ↔
    (b = true → DPGraph.Predicates.CountInRange g.range 0) := by
  unfold Accepted
  erw [descended_group_iff _ _ _ (typed g valid b),
    Groups.empty_holds_iff (EffectiveCore.erase (input g valid)) (config b) (0 : Fin 1) (inventory_empty g valid)]
  constructor
  · intro h hb; exact h ⟨(), hb⟩
  · intro h x; exact h x.property

theorem empty_context_positive : Accepted .xor (by decide) false := by
  rw [accepted_iff]; decide
theorem inhabited_context_positive_rejected : ¬ Accepted .xor (by decide) true := by
  rw [accepted_iff]; decide
theorem inhabited_zero_bounds : Accepted .opt (by decide) true ∧
    Accepted .mux (by decide) true ∧ Accepted (.bounds ⟨0, .finite 0⟩) (by decide) true := by
  simp only [accepted_iff]; decide

end Clafer.Compile.EmptyGroupExamples
