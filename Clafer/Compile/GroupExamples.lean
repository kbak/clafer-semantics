module

public import Clafer.Compile.GroupSemantics
public import Clafer.Semantics.Relational
public import Mathlib.Tactic.FinCases

/-! # Compiled and glued group witnesses

These tests exercise generated declarations and canonical gluing, with explicit
typed relation models. They do not assert #66's realization of abstract children.
-/

@[expose] public section
namespace Clafer.Compile.GroupExamples
open CategoryTheory MCS DPGraph DPGraph.Predicates Semantics

instance rangeDecidable (r : Range) : Decidable (ValidRange r) := by
  unfold ValidRange
  cases r.upper <;> infer_instance

def root : Declaration := ⟨⟨0⟩, "Sing", .syntheticRoot, .basic, none, false, false,
  {}, {}, []⟩
def parent (g : Option GroupCard) : Declaration :=
  { id := ⟨1⟩, name := "B", super := some ⟨5⟩,
    group := ⟨g, g.getD .xor⟩ }
def child (id : Nat) (abstract : Bool := false) : Declaration :=
  { id := ⟨id⟩, name := "child", reference := .bag ⟨4⟩,
    isAbstract := abstract, multiplicity := ⟨some optional, optional⟩ }
def target : Declaration := { id := ⟨4⟩, name := "Target" }
def superDecl : Declaration :=
  { id := ⟨5⟩, name := "A", authoredAbstract := true, isAbstract := true,
    group := ⟨some .xor, .xor⟩ }

def ast (g : Option GroupCard) : AST := ⟨⟨0⟩,
  [.branch root [.branch (parent g) [.branch (child 2) [], .branch (child 3) []],
    .branch target []], .branch superDecl [.branch (child 6 true) []]]⟩

theorem entries (g) : (ast g).entries =
    [⟨root, none, 0⟩, ⟨parent g, some ⟨0⟩, 1⟩,
      ⟨child 2, some ⟨1⟩, 2⟩, ⟨child 3, some ⟨1⟩, 2⟩,
      ⟨target, some ⟨0⟩, 1⟩, ⟨superDecl, none, 0⟩, ⟨child 6 true, some ⟨5⟩, 1⟩] := rfl

instance ast_nonzero (g) : NeZero (ast g).entries.length := ⟨by change (7 : Nat) ≠ 0; decide⟩

@[simp] theorem ast_root (g) : (ast g).root = ⟨0⟩ := rfl

theorem wf (g) (valid : ValidRange (g.getD .xor).range) : (ast g).WellFormed := by
  constructor
  all_goals try { simp [AST.Known, entries, root, parent, child, target, superDecl,
    Reference.kind, Reference.target, Kind.CanExtend, PrimitiveDomain.name,
    ValidRange, GroupCard.range, one, optional, unrestricted] }
  · refine ⟨fun id => if id = ⟨1⟩ then 1 else 0, ?_⟩
    simp [entries, root, parent, child, target, superDecl]
  · simpa [entries, root, parent, child, target, superDecl, ValidRange,
      GroupCard.range, one, optional, unrestricted] using valid
  · intro d hd hu p s hp hpm hs hsm
    simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases p <;> cases s <;>
      simp_all [entries, root, parent, child, target, superDecl, Defaults,
        GroupCard.childDefault, GroupCard.range, one, optional, unrestricted]
    all_goals aesop

theorem no_constraints (g) (q : ConstraintId (ast g)) : False := by
  rcases q with ⟨c, k⟩
  change Fin 7 at c
  fin_cases c <;> exact Fin.elim0 k

noncomputable def input (g) (valid : ValidRange (g.getD .xor).range) : Input (ast g) where
  ast := wf g valid
  root_name := by
    intro d hd
    simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [root, parent, child, target, superDecl]
  user_names := by
    intro d hd
    simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [root, parent, child, target, superDecl, predefinedStrings]
    all_goals intro dom; cases dom <;> decide
  constraint q := (no_constraints g q).elim
  typed q := (no_constraints g q).elim
  positive_support q := (no_constraints g q).elim

variable (g : Option GroupCard) (valid : ValidRange (g.getD .xor).range)

noncomputable def core : EffectiveCore 7 := EffectiveCore.erase (input g valid)

theorem supers (p : Fin 7) : (core g valid).family.super p =
    if p = 1 then some 5 else none := by
  fin_cases p <;> rfl

theorem ancestor_iff (p s : Fin 7) :
    Groups.Ancestor (core g valid).family p s ↔ s = p ∨ (p = 1 ∧ s = 5) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | @tail b c h edge ih =>
      have he : b = 1 ∧ c = 5 := by
        rw [supers] at edge
        split at edge
        · exact ⟨‹b = 1›, (Option.some.inj edge).symm⟩
        · cases edge
      rcases ih with rfl | ⟨hp, hb⟩
      · exact Or.inr he
      · omega
  · rintro (rfl | ⟨rfl, rfl⟩)
    · exact .refl
    · exact Relation.ReflTransGen.single rfl

/-- Object IDs 0/1/2 are root, context and shared reference target.
Every right-summand object is a distinct child occurrence. -/
abbrev Objects (k : Nat) := Fin 3 ⊕ Fin k

def config {k : Nat} (which : Fin k → Fin 3) : Configuration (Fin 7) (Objects k) where
  root := .inl 0
  head d := {x | match x with
    | .inl n => (d = 0 ∧ n = 0) ∨ ((d = 1 ∨ d = 5) ∧ n = 1) ∨ (d = 4 ∧ n = 2)
    | .inr j => d = (if which j = 0 then 2 else if which j = 1 then 3 else 6)}
  contains d p x := match x with
    | .inl n => p = .inl 0 ∧ ((d = 1 ∧ n = 1) ∨ (d = 4 ∧ n = 2))
    | .inr j => p = .inl 1 ∧ d = (if which j = 0 then 2 else if which j = 1 then 3 else 6)
  deref d x t := match x with
    | .inl _ => False
    | .inr j => t = .inl 2 ∧ d = (if which j = 0 then 2 else if which j = 1 then 3 else 6)

instance headDecidable {k} (which : Fin k → Fin 3) (d : Fin 7) :
    DecidablePred (fun x => x ∈ (config which).head d) := fun x => by
  cases x <;> simp only [config, Set.mem_ofPred_eq] <;> infer_instance

instance containsDecidable {k} (which : Fin k → Fin 3) (d : Fin 7) (p x : Objects k) :
    Decidable ((config which).contains d p x) := by
  cases x <;> dsimp [config, Set.mem_ofPred_eq] <;> infer_instance

instance derefDecidable {k} (which : Fin k → Fin 3) (d : Fin 7) (x t : Objects k) :
    Decidable ((config which).deref d x t) := by
  cases x <;> dsimp [config, Set.mem_ofPred_eq] <;> infer_instance

theorem typed {k} (which : Fin k → Fin 3) : (config which).Typed (core g valid) := by
  constructor
  · intro d p x h
    cases x with
    | inl n =>
      rcases h with ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨by simp [config, Set.mem_ofPred_eq], 0, rfl, by simp [config, Set.mem_ofPred_eq]⟩
      · exact ⟨by simp [config, Set.mem_ofPred_eq], 0, rfl, by simp [config, Set.mem_ofPred_eq]⟩
    | inr j =>
      rcases h with ⟨rfl, rfl⟩
      generalize hw : which j = w
      fin_cases w
      all_goals
        refine ⟨by simp [config, Set.mem_ofPred_eq, hw], ?_⟩
        first | exact ⟨1, rfl, by simp [config, Set.mem_ofPred_eq]⟩ | exact ⟨5, rfl, by simp [config, Set.mem_ofPred_eq]⟩
  · intro d x t h
    cases x with
    | inl n => exact h.elim
    | inr j =>
      rcases h with ⟨rfl, rfl⟩
      generalize hw : which j = w
      fin_cases w
      all_goals exact ⟨by simp [config, Set.mem_ofPred_eq, hw], 4, rfl, by simp [config, Set.mem_ofPred_eq]⟩

theorem child_objects {k} (which : Fin k → Fin 3) (y : Objects k) :
    Groups.ChildObjects (core g valid).family (config which) 1 (.inl 1) y ↔
      ∃ j, y = .inr j := by
  simp only [Groups.ChildObjects, ancestor_iff]
  constructor
  · rintro ⟨a, ha, c, hc, h⟩
    cases y with
    | inl n =>
      have he : (1 : Fin 3) = 0 := Sum.inl.inj h.1
      exact ((by decide : (1 : Fin 3) ≠ 0) he).elim
    | inr j => exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    generalize hw : which j = w
    fin_cases w
    · exact ⟨1, by simp, 2, rfl, by simp [config, hw]⟩
    · exact ⟨1, by simp, 3, rfl, by simp [config, hw]⟩
    · exact ⟨5, by simp, 6, rfl, by simp [config, hw]⟩

noncomputable def countedEquiv {k} (which : Fin k → Fin 3) :
    {y : Objects k // Groups.ChildObjects (core g valid).family (config which) 1 (.inl 1) y} ≃ Fin k where
  toFun y := match hy : y.val with
    | .inl _ => False.elim (by obtain ⟨j, hj⟩ := (child_objects g valid which y.val).mp y.property; simp [hy] at hj)
    | .inr j => j
  invFun j := ⟨.inr j, (child_objects g valid which _).mpr ⟨j, rfl⟩⟩
  left_inv y := by
    obtain ⟨j, hj⟩ := (child_objects g valid which y.val).mp y.property
    cases y; cases hj; rfl
  right_inv _ := rfl

theorem holds_count {k} (which : Fin k → Fin 3) :
    Groups.Holds (core g valid).family (config which) 1 ↔
      DPGraph.Predicates.CountInRange (g.getD .xor).range k := by
  have hx : ∀ x : (config which).head 1, x.val = .inl 1 := by
    rintro ⟨x, hx⟩
    cases x with
    | inl n => simp [config, Set.mem_ofPred_eq] at hx; exact congrArg Sum.inl hx
    | inr j =>
      generalize hw : which j = w
      fin_cases w <;> simp [config, Set.mem_ofPred_eq, hw] at hx
  have hcount := (inRange_iff (g.getD .xor).range (countedEquiv g valid which)).trans
    (DPGraph.Predicates.inRange_card _ (Fin k))
  simp only [Fintype.card_fin] at hcount
  constructor
  · intro h; exact hcount.mp (h ⟨.inl 1, by simp [config, Set.mem_ofPred_eq]⟩)
  · intro h x
    change InRange (g.getD .xor).range _
    simp only [hx x]
    exact hcount.mpr h

noncomputable def authored (U : Type) :
    Interpretation (Constraints.signature (input g valid).constraint) (semanticGraph U) :=
  ⟨fun q => (no_constraints g q).elim⟩

noncomputable def parentId : Groups.Id (family (input g valid)) := ⟨1, rfl⟩

/-- These are actual emitted and glued formulas, not just retained metadata. -/
theorem emitted : generatedGroup (input g valid) (parentId g valid) ∈
    (compileAugmented (input g valid)).complete.diagram.declarations := group_declared _ _
theorem glued_emitted :
    (generatedGroup (input g valid) (parentId g valid)).translate (groupLabel (input g valid)) ∈
      (gluedGroups (input g valid)).declarations := glued_group_declared _ _

-- [proof->req~clafer-compile-groups~1]
theorem compiled_count {k} (which : Fin k → Fin 3) :
    (groupInterpretation (input g valid) (Objects k) (authored g valid _)).Satisfies
      ((config which).interpret (core g valid)) (generatedGroup (input g valid) (parentId g valid)) ↔
      DPGraph.Predicates.CountInRange (g.getD .xor).range k :=
  (generated_group_iff _ _ _ (typed g valid which) _).trans (holds_count g valid which)

theorem glued_count {k} (which : Fin k → Fin 3) :
    (groupInterpretation (input g valid) (Objects k) (authored g valid _)).Satisfies
      (descendGroups (input g valid) (config which))
      ((generatedGroup (input g valid) (parentId g valid)).translate (groupLabel (input g valid))) ↔
      DPGraph.Predicates.CountInRange (g.getD .xor).range k :=
  (descended_group_iff _ _ _ (typed g valid which) _).trans (holds_count g valid which)

def Verdict (g : Option GroupCard) (k : Nat) : Prop := DPGraph.Predicates.CountInRange (g.getD .xor).range k

instance verdictDecidable (g : Option GroupCard) (k : Nat) : Decidable (Verdict g k) := by
  unfold Verdict
  infer_instance

theorem xor_bounds : Verdict none 1 ∧ ¬ Verdict none 0 ∧ ¬ Verdict none 2 := by decide
theorem numeric_bounds : Verdict (some (.bounds ⟨2, .finite 3⟩)) 2 ∧
    Verdict (some (.bounds ⟨2, .finite 3⟩)) 3 ∧
    ¬ Verdict (some (.bounds ⟨2, .finite 3⟩)) 1 ∧
    ¬ Verdict (some (.bounds ⟨2, .finite 3⟩)) 4 := by decide
theorem keywords : Verdict (some .or) 2 ∧ ¬ Verdict (some .or) 0 ∧
    Verdict (some .mux) 0 ∧ Verdict (some .mux) 1 ∧ ¬ Verdict (some .mux) 2 ∧
    Verdict (some .opt) 0 ∧ Verdict (some .opt) 2 := by decide

/-- Only a new child, absent from A's inventory, satisfies inherited xor. -/
theorem inherited_new_child :
    (groupInterpretation (input none (by decide)) (Objects 1) (authored none (by decide) _)).Satisfies
      (descendGroups (input none (by decide)) (config (fun _ : Fin 1 => 0)))
      ((generatedGroup (input none (by decide)) (parentId none (by decide))).translate
        (groupLabel (input none (by decide)))) :=
  (glued_count none (by decide) (fun _ : Fin 1 => 0)).mpr (by decide)

theorem abstract_has_no_group : ¬ ∃ p : Groups.Id (family (input g valid)), p.val = 5 := by
  rintro ⟨⟨p, hp⟩, rfl⟩; cases hp

theorem override_two :
    (groupInterpretation (input (some .opt) (by decide)) (Objects 2)
      (authored (some .opt) (by decide) _)).Satisfies
      (descendGroups (input (some .opt) (by decide)) (config (fun j : Fin 2 => ⟨j.val, by omega⟩)))
      ((generatedGroup (input (some .opt) (by decide)) (parentId (some .opt) (by decide))).translate
        (groupLabel (input (some .opt) (by decide)))) :=
  (glued_count (some .opt) (by decide) _).mpr (by decide)

def spread {k : Nat} (j : Fin k) : Fin 3 := ⟨j.val % 3, Nat.mod_lt _ (by decide)⟩

noncomputable def Accepted (g : Option GroupCard) (valid : ValidRange (g.getD .xor).range)
    (k : Nat) (which : Fin k → Fin 3 := spread) : Prop :=
  (groupInterpretation (input g valid) (Objects k) (authored g valid _)).Satisfies
    ((config which).interpret (core g valid)) (generatedGroup (input g valid) (parentId g valid)) ∧
  (groupInterpretation (input g valid) (Objects k) (authored g valid _)).Satisfies
    (descendGroups (input g valid) (config which))
    ((generatedGroup (input g valid) (parentId g valid)).translate (groupLabel (input g valid)))

theorem accepted_iff (k : Nat) (which : Fin k → Fin 3) :
    Accepted g valid k which ↔ Verdict g k := by
  rw [Accepted, compiled_count, glued_count, and_self]
  rfl

theorem xor_compiled_glued : Accepted none (by decide) 1 ∧
    ¬ Accepted none (by decide) 0 ∧ ¬ Accepted none (by decide) 2 := by
  simp only [accepted_iff]
  decide

theorem numeric_compiled_glued :
    Accepted (some (.bounds ⟨2, .finite 3⟩)) (by decide) 2 ∧
    Accepted (some (.bounds ⟨2, .finite 3⟩)) (by decide) 3 ∧
    ¬ Accepted (some (.bounds ⟨2, .finite 3⟩)) (by decide) 1 ∧
    ¬ Accepted (some (.bounds ⟨2, .finite 3⟩)) (by decide) 4 := by
  simp only [accepted_iff]
  decide

theorem keywords_compiled_glued :
    Accepted (some .or) (by decide) 2 ∧ ¬ Accepted (some .or) (by decide) 0 ∧
    Accepted (some .mux) (by decide) 0 ∧ Accepted (some .mux) (by decide) 1 ∧
    ¬ Accepted (some .mux) (by decide) 2 ∧
    Accepted (some .opt) (by decide) 0 ∧ Accepted (some .opt) (by decide) 2 := by
  simp only [accepted_iff]
  decide

theorem one_declaration_two_objects :
    Accepted (some (.bounds ⟨2, .finite 3⟩)) (by decide) 2 (fun _ => 0) ∧
    ¬ Accepted none (by decide) 2 (fun _ => 0) := by
  simp only [accepted_iff]
  decide

/-- Both bag-head occurrences point to the very same target object. -/
theorem shared_target_occurrences :
    (config (@spread 2)).deref 2 (.inr 0) (.inl 2) ∧
    (config (@spread 2)).deref 3 (.inr 1) (.inl 2) ∧
    (Sum.inr (0 : Fin 2) : Objects 2) ≠ .inr 1 ∧
    ¬ Accepted none (by decide) 2 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  rw [accepted_iff]; decide

/-- Every selected head fiber is individually optional in all three xor
boundary cases. Their conjunction alone cannot imply the generated xor. -/
theorem xor_individually_optional (k : Fin 3) (c : Fin 7)
    (hc : c = 2 ∨ c = 3 ∨ c = 6) :
    InRange optional {x : Objects k.val // (config (@spread k.val)).contains c (.inl 1) x} := by
  fin_cases k
  all_goals rcases hc with rfl | rfl | rfl
  all_goals
    rw [DPGraph.Predicates.inRange_card]
    decide

theorem xor_optional_head_maps (k : Fin 3) (c : Fin 7)
    (hc : c = 2 ∨ c = 3 ∨ c = 6) :
    TargetMultiplicity optional
      ((config (@spread k.val)).headMap (core none (by decide)) c) := by
  let s := config (@spread k.val)
  let m := core none (by decide)
  have hp : m.family.parent c = some (if c = 6 then 5 else 1) := by
    rcases hc with rfl | rfl | rfl <;> rfl
  have hm : m.family.multiplicity c = optional := by
    rcases hc with rfl | rfl | rfl <;> rfl
  rw [← hm]
  apply (s.head_multiplicity_iff m (typed none (by decide) _) c _ hp).mpr
  intro x hx
  have he : x = .inl 1 := by
    rcases hc with rfl | rfl | rfl
    all_goals
      cases x with
      | inl j => simpa [s, config] using hx
      | inr j =>
        fin_cases k <;> fin_cases j <;> simp [s, config, spread] at hx
  subst x
  simpa only [hm] using xor_individually_optional k c hc

end Clafer.Compile.GroupExamples
