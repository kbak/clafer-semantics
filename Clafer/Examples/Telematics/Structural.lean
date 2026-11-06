module

public import Clafer.Compile.Realization
public import Clafer.Semantics.RealizationCompatibility
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation

/-!
# Telematics structural realization witness

SoSyM Appendix 6 (PDF p.34).

The source IDs d01–d26 map injectively to DeclId 1–26; root=0 and int=27.
Preorder occurrences differ from source IDs (see `source_order`). This fixture
contains the structural declarations only: the twelve source constraints and
complete final selections/satisfaction remain #64/#68/#69.
-/

@[expose] public section
namespace Clafer.Examples.Telematics.Structural
open CategoryTheory MCS Compile DPGraph DPGraph.Predicates Semantics

instance rangeDecidable (r : Range) : Decidable (ValidRange r) := by
  unfold ValidRange
  cases r.upper <;> infer_instance

def decl : Nat → Declaration
  | 0 => { id := ⟨0⟩, name := "Sing", origin := .syntheticRoot }
  | 1 => { id := ⟨1⟩, name := "options", authoredAbstract := true, isAbstract := true }
  | 2 => { id := ⟨2⟩, name := "size", isAbstract := true, group := ⟨some .xor, .xor⟩ }
  | 3 => { id := ⟨3⟩, name := "small", isAbstract := true, multiplicity := ⟨some optional, optional⟩ }
  | 4 => { id := ⟨4⟩, name := "large", isAbstract := true, multiplicity := ⟨some optional, optional⟩ }
  | 5 => { id := ⟨5⟩, name := "cache", isAbstract := true, multiplicity := ⟨some optional, optional⟩ }
  | 6 => { id := ⟨6⟩, name := "size", reference := .set ⟨27⟩, isAbstract := true }
  | 7 => { id := ⟨7⟩, name := "fixed", isAbstract := true, multiplicity := ⟨some optional, optional⟩ }
  | 8 => { id := ⟨8⟩, name := "comp", authoredAbstract := true, isAbstract := true }
  | 9 => { id := ⟨9⟩, name := "version", reference := .set ⟨27⟩, isAbstract := true }
  | 10 => { id := ⟨10⟩, name := "ECU", super := some ⟨8⟩, authoredAbstract := true, isAbstract := true }
  | 11 => { id := ⟨11⟩, name := "display", super := some ⟨8⟩, authoredAbstract := true, isAbstract := true }
  | 12 => { id := ⟨12⟩, name := "server", reference := .set ⟨10⟩, isAbstract := true }
  | 13 => { id := ⟨13⟩, name := "options", super := some ⟨1⟩, isAbstract := true }
  | 14 => { id := ⟨14⟩, name := "plaECU", super := some ⟨10⟩, authoredAbstract := true, isAbstract := true }
  | 15 => { id := ⟨15⟩, name := "plaDisplay", super := some ⟨11⟩, isAbstract := true, multiplicity := ⟨some ⟨1, .finite 2⟩, ⟨1, .finite 2⟩⟩ }
  | 16 => { id := ⟨16⟩, name := "ECU1", super := some ⟨14⟩ }
  | 17 => { id := ⟨17⟩, name := "ECU2", super := some ⟨14⟩, multiplicity := ⟨some optional, optional⟩ }
  | 18 => { id := ⟨18⟩, name := "master", reference := .set ⟨16⟩ }
  | 19 => { id := ⟨19⟩, name := "telematics" }
  | 20 => { id := ⟨20⟩, name := "channel", group := ⟨some .xor, .xor⟩ }
  | 21 => { id := ⟨21⟩, name := "single", multiplicity := ⟨some optional, optional⟩ }
  | 22 => { id := ⟨22⟩, name := "dual", multiplicity := ⟨some optional, optional⟩ }
  | 23 => { id := ⟨23⟩, name := "extraDisplay", multiplicity := ⟨some optional, optional⟩ }
  | 24 => { id := ⟨24⟩, name := "size", group := ⟨some .xor, .xor⟩ }
  | 25 => { id := ⟨25⟩, name := "small", multiplicity := ⟨some optional, optional⟩ }
  | 26 => { id := ⟨26⟩, name := "large", multiplicity := ⟨some optional, optional⟩ }
  | 27 => { id := ⟨27⟩, name := "int", origin := .primitive .int }
  | k => { id := ⟨k⟩, name := "unused" }

def ast : AST := ⟨⟨0⟩, [.branch (decl 0) [.branch (decl 16) [], .branch (decl 17) [.branch (decl 18) []], .branch (decl 19) [.branch (decl 20) [.branch (decl 21) [], .branch (decl 22) []], .branch (decl 23) [], .branch (decl 24) [.branch (decl 25) [], .branch (decl 26) []]], .branch (decl 27) []], .branch (decl 1) [.branch (decl 2) [.branch (decl 3) [], .branch (decl 4) []], .branch (decl 5) [.branch (decl 6) [.branch (decl 7) []]]], .branch (decl 8) [.branch (decl 9) []], .branch (decl 10) [], .branch (decl 11) [.branch (decl 12) [], .branch (decl 13) []], .branch (decl 14) [.branch (decl 15) []]]⟩

theorem entries : ast.entries = [⟨decl 0, none, 0⟩, ⟨decl 16, some ⟨0⟩, 1⟩, ⟨decl 17, some ⟨0⟩, 1⟩, ⟨decl 18, some ⟨17⟩, 2⟩, ⟨decl 19, some ⟨0⟩, 1⟩, ⟨decl 20, some ⟨19⟩, 2⟩, ⟨decl 21, some ⟨20⟩, 3⟩, ⟨decl 22, some ⟨20⟩, 3⟩, ⟨decl 23, some ⟨19⟩, 2⟩, ⟨decl 24, some ⟨19⟩, 2⟩, ⟨decl 25, some ⟨24⟩, 3⟩, ⟨decl 26, some ⟨24⟩, 3⟩, ⟨decl 27, some ⟨0⟩, 1⟩, ⟨decl 1, none, 0⟩, ⟨decl 2, some ⟨1⟩, 1⟩, ⟨decl 3, some ⟨2⟩, 2⟩, ⟨decl 4, some ⟨2⟩, 2⟩, ⟨decl 5, some ⟨1⟩, 1⟩, ⟨decl 6, some ⟨5⟩, 2⟩, ⟨decl 7, some ⟨6⟩, 3⟩, ⟨decl 8, none, 0⟩, ⟨decl 9, some ⟨8⟩, 1⟩, ⟨decl 10, none, 0⟩, ⟨decl 11, none, 0⟩, ⟨decl 12, some ⟨11⟩, 1⟩, ⟨decl 13, some ⟨11⟩, 1⟩, ⟨decl 14, none, 0⟩, ⟨decl 15, some ⟨14⟩, 1⟩] := rfl

theorem source_order : ast.entries.map (·.declaration.id) = [⟨0⟩, ⟨16⟩, ⟨17⟩, ⟨18⟩, ⟨19⟩, ⟨20⟩, ⟨21⟩, ⟨22⟩, ⟨23⟩, ⟨24⟩, ⟨25⟩, ⟨26⟩, ⟨27⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩, ⟨6⟩, ⟨7⟩, ⟨8⟩, ⟨9⟩, ⟨10⟩, ⟨11⟩, ⟨12⟩, ⟨13⟩, ⟨14⟩, ⟨15⟩] := rfl

instance ast_nonzero : NeZero ast.entries.length := ⟨by decide⟩
@[simp] theorem ast_root : ast.root = ⟨0⟩ := rfl

theorem unique_entry : ∀ d ∈ ast.entries, ∀ e ∈ ast.entries,
    d.declaration.id = e.declaration.id → d = e := by decide

theorem option_entry (v : Located) (hv : v ∈ ast.entries)
    (p : Option Located) (hp : p.map (·.declaration.id) = some v.declaration.id)
    (hm : ∀ x ∈ p, x ∈ ast.entries) : p = some v := by
  cases p with
  | none => cases hp
  | some x =>
    exact congrArg some (unique_entry x (hm x rfl) v hv (Option.some.inj hp))

theorem defaults_valid (d : Located) (hd : d ∈ ast.entries)
    (hu : d.declaration.origin = .user) (p s : Option Located)
    (hp : p.map (·.declaration.id) = d.parent) (hpm : ∀ x ∈ p, x ∈ ast.entries)
    (hs : s.map (·.declaration.id) = d.declaration.super) (hsm : ∀ x ∈ s, x ∈ ast.entries) :
    Defaults d.declaration (p.map (·.declaration)) (s.map (·.declaration)) := by
  simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases hu
  · have hp' : p = some (⟨decl 0, none, 0⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = some (⟨decl 14, none, 0⟩) := option_entry _ (by decide) s hs hsm
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 0, none, 0⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = some (⟨decl 14, none, 0⟩) := option_entry _ (by decide) s hs hsm
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 17, some ⟨0⟩, 1⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = none := Option.map_eq_none_iff.mp hs
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 0, none, 0⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = none := Option.map_eq_none_iff.mp hs
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 19, some ⟨0⟩, 1⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = none := Option.map_eq_none_iff.mp hs
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 20, some ⟨19⟩, 2⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = none := Option.map_eq_none_iff.mp hs
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 20, some ⟨19⟩, 2⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = none := Option.map_eq_none_iff.mp hs
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 19, some ⟨0⟩, 1⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = none := Option.map_eq_none_iff.mp hs
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 19, some ⟨0⟩, 1⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = none := Option.map_eq_none_iff.mp hs
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 24, some ⟨19⟩, 2⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = none := Option.map_eq_none_iff.mp hs
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 24, some ⟨19⟩, 2⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = none := Option.map_eq_none_iff.mp hs
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · cases hu
  · have hp' : p = none := Option.map_eq_none_iff.mp hp
    subst p
    have hs' : s = none := Option.map_eq_none_iff.mp hs
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 1, none, 0⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = none := Option.map_eq_none_iff.mp hs
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 2, some ⟨1⟩, 1⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = none := Option.map_eq_none_iff.mp hs
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 2, some ⟨1⟩, 1⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = none := Option.map_eq_none_iff.mp hs
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 1, none, 0⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = none := Option.map_eq_none_iff.mp hs
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 5, some ⟨1⟩, 1⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = none := Option.map_eq_none_iff.mp hs
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 6, some ⟨5⟩, 2⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = none := Option.map_eq_none_iff.mp hs
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = none := Option.map_eq_none_iff.mp hp
    subst p
    have hs' : s = none := Option.map_eq_none_iff.mp hs
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 8, none, 0⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = none := Option.map_eq_none_iff.mp hs
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = none := Option.map_eq_none_iff.mp hp
    subst p
    have hs' : s = some (⟨decl 8, none, 0⟩) := option_entry _ (by decide) s hs hsm
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = none := Option.map_eq_none_iff.mp hp
    subst p
    have hs' : s = some (⟨decl 8, none, 0⟩) := option_entry _ (by decide) s hs hsm
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 11, none, 0⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = none := Option.map_eq_none_iff.mp hs
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 11, none, 0⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = some (⟨decl 1, none, 0⟩) := option_entry _ (by decide) s hs hsm
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = none := Option.map_eq_none_iff.mp hp
    subst p
    have hs' : s = some (⟨decl 10, none, 0⟩) := option_entry _ (by decide) s hs hsm
    subst s
    exact ⟨rfl,rfl,rfl⟩
  · have hp' : p = some (⟨decl 14, none, 0⟩) := option_entry _ (by decide) p hp hpm
    subst p
    have hs' : s = some (⟨decl 11, none, 0⟩) := option_entry _ (by decide) s hs hsm
    subst s
    exact ⟨rfl,rfl,rfl⟩

set_option maxHeartbeats 1000000 in
theorem wf : ast.WellFormed where
  unique_ids := by decide
  root_exists := by simp [AST.Known, entries, decl]
  root_origin := by decide
  root_shape := by decide
  parent_exists := by simp [entries, decl, AST.Known]
  parent_depth := by decide
  parentless_abstract := by decide
  nested_abstract := by decide
  primitive_shape := by simp [entries, decl, PrimitiveDomain.name]
  unique_domains := by simp [entries, decl]
  targets_resolved := by simp [entries, decl, Reference.target, AST.Known]
  supers_resolved := by simp [entries, decl, AST.Known]
  inheritance_kind := by
    unfold Kind.CanExtend
    decide
  inheritance_parent := by decide
  inheritance_rank := by
    refine ⟨fun id => if id = ⟨16⟩ ∨ id = ⟨17⟩ then 3 else
        if id = ⟨14⟩ ∨ id = ⟨15⟩ then 2 else
        if id = ⟨10⟩ ∨ id = ⟨11⟩ ∨ id = ⟨13⟩ then 1 else 0, ?_⟩
    simp [entries, decl]
  valid_bounds := by decide
  defaults := defaults_valid
  constraints_resolved := by simp [entries, decl]

theorem no_constraints (q : ConstraintId ast) : False := by
  rcases q with ⟨c,k⟩
  change Fin 28 at c
  fin_cases c <;> exact Fin.elim0 k

noncomputable def input : Input ast where
  ast := wf
  root_name := by
    intro d hd
    simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [decl]
  user_names := by
    intro d hd
    simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [decl, predefinedStrings]
    all_goals intro dom; cases dom <;> decide
  constraint q := (no_constraints q).elim
  typed q := (no_constraints q).elim
  positive_support q := (no_constraints q).elim

noncomputable def core : Semantics.Realization.Core 28 := Semantics.Realization.Core.ofInput input

def parents : Fin 28 → Option (Fin 28) := ![none, some 0, some 0, some 2, some 0, some 4, some 5, some 5, some 4, some 4, some 9, some 9, some 0, none, some 13, some 14, some 14, some 13, some 17, some 18, none, some 20, none, none, some 23, some 23, none, some 26]
def supers : Fin 28 → Option (Fin 28) := ![none, some 26, some 26, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 20, some 20, none, some 13, some 22, some 23]
def references : Fin 28 → ReferenceTo (Fin 28) := ![.basic, .basic, .basic, .set 1, .basic, .basic, .basic, .basic, .basic, .basic, .basic, .basic, .basic, .basic, .basic, .basic, .basic, .basic, .set 12, .basic, .basic, .set 12, .basic, .basic, .set 22, .basic, .basic, .basic]
def explicit : Fin 28 → Bool := ![false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, true, false, true, true, false, false, true, false]
def effective : Fin 28 → Bool := ![false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]
def bounds : Fin 28 → Range := ![one, one, optional, one, one, one, optional, optional, optional, one, optional, optional, one, one, one, optional, optional, optional, one, optional, one, one, one, one, one, one, one, ⟨1,.finite 2⟩]
def groupBounds : Fin 28 → Range := ![unrestricted, unrestricted, unrestricted, unrestricted, unrestricted, one, unrestricted, unrestricted, unrestricted, one, unrestricted, unrestricted, unrestricted, unrestricted, one, unrestricted, unrestricted, unrestricted, unrestricted, unrestricted, unrestricted, unrestricted, unrestricted, unrestricted, unrestricted, unrestricted, unrestricted, unrestricted]

theorem parents_eq (d : Fin 28) : core.family.parent d = parents d := by
  fin_cases d <;> rfl

theorem supers_eq (d : Fin 28) : core.family.super d = supers d := by
  fin_cases d <;> rfl

theorem references_eq (d : Fin 28) : core.family.reference d = references d := by
  fin_cases d <;> rfl

theorem explicit_eq (d : Fin 28) : core.explicitAbstract d = explicit d := by
  fin_cases d <;> rfl

theorem effective_eq (d : Fin 28) : core.family.isAbstract d = effective d := by
  fin_cases d <;> rfl

theorem bounds_eq (d : Fin 28) : core.family.multiplicity d = bounds d := by
  fin_cases d <;> rfl

theorem groupBounds_eq (d : Fin 28) : core.group d = groupBounds d := by
  fin_cases d <;> rfl

theorem family_groups (d : Fin 28) : (core.family.group d).effective.range = groupBounds d := by
  fin_cases d <;> rfl

theorem selected : core.Selected := by
  unfold Semantics.Realization.Core.Selected
  simp only [parents_eq, supers_eq, references_eq, explicit_eq, effective_eq]
  refine ⟨by decide, by decide, ?_, by decide, ?_⟩
  · intro d c hc
    fin_cases d <;> simp [supers] at hc
    all_goals subst c; exact ⟨rfl,rfl⟩
  · refine ⟨![0,1,1,2,1,2,3,3,2,2,3,3,1,8,9,10,10,9,10,11,7,8,3,6,7,7,2,5], ?_, ?_⟩
    · decide
    · decide


def heads : Fin 28 → Finset (Fin 25) := ![{0}, {2}, {3}, {18}, {19}, {20}, ∅, {21}, {22}, {23}, ∅, {24}, {1}, {12, 13}, {14, 15}, ∅, {16, 17}, ∅, ∅, ∅, {2, 3, 4, 5}, {6, 7, 8, 9}, {2, 3}, {4, 5}, {10, 11}, {12, 13}, {2, 3}, {4, 5}]

def ownership : Fin 28 → Finset (Fin 25 × Fin 25) := ![∅, {(0,2)}, {(0,3)}, {(3,18)}, {(0,19)}, {(19,20)}, ∅, {(20,21)}, {(19,22)}, {(19,23)}, ∅, {(23,24)}, {(0,1)}, ∅, {(12,14), (13,15)}, ∅, {(14,16), (15,17)}, ∅, ∅, ∅, ∅, {(2,6), (3,7), (4,8), (5,9)}, ∅, ∅, {(4,10), (5,11)}, {(4,12), (5,13)}, ∅, {(2,4), (3,5)}]

def targets : Fin 28 → Finset (Fin 25 × Fin 25) := ![∅, ∅, ∅, {(18,2)}, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, {(6,1), (7,1), (8,1), (9,1)}, ∅, ∅, {(10,2), (11,3)}, ∅, ∅, ∅]

-- [impl->req~clafer-inherited-witnesses~1]
def config : Configuration (Fin 28) (Fin 25) where
  root := 0
  head d := {x | x ∈ heads d}
  contains d p x := (p,x) ∈ ownership d
  deref d x t := (x,t) ∈ targets d

instance headDecidable (d : Fin 28) : DecidablePred (fun x => x ∈ config.head d) :=
  fun _ => inferInstanceAs (Decidable (_ ∈ heads d))
instance containsDecidable (d : Fin 28) (p x : Fin 25) : Decidable (config.contains d p x) :=
  inferInstanceAs (Decidable ((p,x) ∈ ownership d))
instance derefDecidable (d : Fin 28) (x t : Fin 25) : Decidable (config.deref d x t) :=
  inferInstanceAs (Decidable ((x,t) ∈ targets d))

theorem typed : config.Typed core.toEffectiveCore := by
  constructor
  · intro d; fin_cases d
    all_goals simp [config, heads, ownership, parents_eq, parents]
    all_goals aesop
  · intro d; fin_cases d
    all_goals simp [config, heads, targets, references_eq, references, ReferenceTo.target]
    all_goals aesop

theorem inherits : config.Inherits core.toEffectiveCore := by
  intro d c hc
  rw [supers_eq] at hc
  fin_cases d <;> simp [supers] at hc
  all_goals subst c; simp [config, heads]

theorem parents_hold : config.Parents core.toEffectiveCore := by
  intro d p hp x hx
  rw [parents_eq] at hp
  fin_cases d <;> simp [parents] at hp
  all_goals simp [config, heads] at hx
  all_goals rcases hx with rfl | rfl | rfl | rfl
  all_goals simp [config, ownership, ExistsUnique]

theorem references_hold : config.References core.toEffectiveCore := by
  intro d t ht x hx
  rw [references_eq] at ht
  fin_cases d <;> simp [references, ReferenceTo.target] at ht
  all_goals simp [config, heads] at hx
  all_goals rcases hx with rfl | rfl | rfl | rfl
  all_goals simp [config, targets, ExistsUnique]

theorem keys : config.Keys core.toEffectiveCore := by
  intro d hd
  rw [references_eq] at hd
  fin_cases d <;> simp [references, ReferenceTo.kind] at hd
  all_goals simp [config, ownership, targets]
  all_goals aesop

theorem abstracts : Semantics.Realization.Abstracts core config := by
  intro d hd
  rw [explicit_eq] at hd
  fin_cases d <;> simp [explicit] at hd
  all_goals simp only [supers_eq]
  all_goals decide

theorem rooted : config.Rooted core.toEffectiveCore := by
  change config.Rooted { core.toEffectiveCore with family.root := (0 : Fin 28) }
  unfold Configuration.Rooted
  simp only [config]
  decide

/-- Positive finite fiber bounds, including optional absent cache fields. -/
theorem multiplicities : config.Multiplicities core.toEffectiveCore := by
  intro d p hp x hx
  rw [parents_eq] at hp
  rw [bounds_eq]
  rw [DPGraph.Predicates.inRange_card]
  fin_cases d <;> simp [parents] at hp
  all_goals subst p
  all_goals simp [config, heads] at hx
  all_goals rcases hx with rfl | rfl | rfl | rfl
  all_goals decide

/-- Exact finite hierarchy table, proved from the seven actual super edges. -/
def ancestorTable : Fin 28 → Finset (Fin 28) := ![{0}, {1,26,22,20}, {2,26,22,20}, {3}, {4}, {5}, {6}, {7}, {8}, {9}, {10}, {11}, {12}, {13}, {14}, {15}, {16}, {17}, {18}, {19}, {20}, {21}, {22,20}, {23,20}, {24}, {25,13}, {26,22,20}, {27,23,20}]

theorem ancestor_iff (p a : Fin 28) : Compile.Groups.Ancestor core.family p a ↔
    a ∈ ancestorTable p := by
  constructor
  · intro h
    induction h with
    | refl => fin_cases p <;> decide
    | @tail b c path edge ih =>
      rw [supers_eq] at edge
      have closed : ∀ p b c : Fin 28, b ∈ ancestorTable p → supers b = some c → c ∈ ancestorTable p := by decide
      exact closed p b c ih edge
  · intro h
    fin_cases p
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl | rfl | rfl | rfl
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single (r := fun c s : Fin 28 => core.family.super c = some s) (show core.family.super 1 = some 26 from rfl)
      · exact (Relation.ReflTransGen.single (r := fun c s : Fin 28 => core.family.super c = some s) (show core.family.super 1 = some 26 from rfl)).tail (show core.family.super 26 = some 22 from rfl)
      · exact ((Relation.ReflTransGen.single (r := fun c s : Fin 28 => core.family.super c = some s) (show core.family.super 1 = some 26 from rfl)).tail (show core.family.super 26 = some 22 from rfl)).tail (show core.family.super 22 = some 20 from rfl)
    · simp [ancestorTable] at h
      rcases h with rfl | rfl | rfl | rfl
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single (r := fun c s : Fin 28 => core.family.super c = some s) (show core.family.super 2 = some 26 from rfl)
      · exact (Relation.ReflTransGen.single (r := fun c s : Fin 28 => core.family.super c = some s) (show core.family.super 2 = some 26 from rfl)).tail (show core.family.super 26 = some 22 from rfl)
      · exact ((Relation.ReflTransGen.single (r := fun c s : Fin 28 => core.family.super c = some s) (show core.family.super 2 = some 26 from rfl)).tail (show core.family.super 26 = some 22 from rfl)).tail (show core.family.super 22 = some 20 from rfl)
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl | rfl
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single (r := fun c s : Fin 28 => core.family.super c = some s) (show core.family.super 22 = some 20 from rfl)
    · simp [ancestorTable] at h
      rcases h with rfl | rfl
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single (r := fun c s : Fin 28 => core.family.super c = some s) (show core.family.super 23 = some 20 from rfl)
    · simp [ancestorTable] at h
      rcases h with rfl
      exact Relation.ReflTransGen.refl
    · simp [ancestorTable] at h
      rcases h with rfl | rfl
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single (r := fun c s : Fin 28 => core.family.super c = some s) (show core.family.super 25 = some 13 from rfl)
    · simp [ancestorTable] at h
      rcases h with rfl | rfl | rfl
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single (r := fun c s : Fin 28 => core.family.super c = some s) (show core.family.super 26 = some 22 from rfl)
      · exact (Relation.ReflTransGen.single (r := fun c s : Fin 28 => core.family.super c = some s) (show core.family.super 26 = some 22 from rfl)).tail (show core.family.super 22 = some 20 from rfl)
    · simp [ancestorTable] at h
      rcases h with rfl | rfl | rfl
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single (r := fun c s : Fin 28 => core.family.super c = some s) (show core.family.super 27 = some 23 from rfl)
      · exact (Relation.ReflTransGen.single (r := fun c s : Fin 28 => core.family.super c = some s) (show core.family.super 27 = some 23 from rfl)).tail (show core.family.super 23 = some 20 from rfl)

instance childDecidable (d : Fin 28) (x y : Fin 25) :
    Decidable (Compile.Groups.ChildObjects core.family config d x y) :=
  decidable_of_iff (∃ a, a ∈ ancestorTable d ∧ ∃ c, parents c = some a ∧ config.contains c x y)
    (by simp only [Compile.Groups.ChildObjects, ancestor_iff, parents_eq])

theorem groups : Semantics.Realization.Groups core config := by
  intro d hd x
  rcases x with ⟨x,hx⟩
  rw [family_groups, DPGraph.Predicates.inRange_card]
  rw [explicit_eq] at hd
  fin_cases d <;> simp [explicit] at hd
  all_goals simp [config, heads] at hx
  all_goals rcases hx with rfl | rfl | rfl | rfl
  all_goals dsimp only
  all_goals decide +revert

theorem declaration_disjoint : config.DeclarationDisjoint core.toEffectiveCore := by
  change ∀ d e x, x ∈ heads d → x ∈ heads e →
    Compile.Groups.Ancestor core.family d e ∨ Compile.Groups.Ancestor core.family e d
  simp only [ancestor_iff]
  decide

-- [proof->req~clafer-inherited-witnesses~1]
theorem satisfies : Semantics.Realization.Satisfies core config :=
  ⟨typed, rooted, ⟨inherits, parents_hold, references_hold, keys, multiplicities⟩, abstracts, groups, declaration_disjoint⟩

theorem all_reach_root (x : Fin 25) : config.Reaches x :=
  Semantics.Realization.reaches core config (EffectiveCore.erase_wellFormed input) selected satisfies x

noncomputable def authored : Interpretation (Constraints.signature input.constraint) (semanticGraph (Fin 25)) :=
  ⟨fun q => (no_constraints q).elim⟩

theorem compiled_glued_model :
    (Compile.Realization.interpretation input (Fin 25) authored).IsModel
      (Compile.Realization.glued input).toDPGraph (Compile.Realization.descend input config) :=
  (Compile.Realization.whole_model input authored selected config).mpr
    ⟨satisfies, fun q => (no_constraints q).elim⟩ |>.2.2.2

/-- d09 version retains one occurrence at every view of each component. -/
theorem inherited_version :
    Semantics.Realization.Contains config 21 1 2 6 ∧
    Semantics.Realization.Contains config 21 26 2 6 ∧
    Semantics.Realization.Contains config 21 22 2 6 ∧
    Semantics.Realization.Contains config 21 20 2 6 ∧
    Semantics.Realization.Contains config 21 2 3 7 ∧
    Semantics.Realization.Contains config 21 27 4 8 ∧
    Semantics.Realization.Contains config 21 23 4 8 ∧
    Semantics.Realization.Contains config 21 20 4 8 := by
  unfold Semantics.Realization.Contains
  decide

-- [proof->req~clafer-representative-coverage~1]
theorem inherited_options_and_displays :
    Semantics.Realization.Contains config 27 1 2 4 ∧
    Semantics.Realization.Contains config 27 2 3 5 ∧
    Semantics.Realization.Contains config 25 27 4 12 ∧
    Semantics.Realization.Contains config 14 25 12 14 ∧
    Semantics.Realization.Contains config 16 14 14 16 := by
  unfold Semantics.Realization.Contains
  decide

noncomputable def sizeField : Compile.Realization.FieldId input := ⟨14, rfl, rfl⟩

theorem realized_xor_generated :
    (Compile.Realization.interpretation input (Fin 25) authored).Satisfies
      (config.interpret core.toEffectiveCore) (Compile.Realization.fieldFormula input sizeField) :=
  (Compile.Realization.field_iff input authored config typed sizeField).mpr (groups 14 rfl)

theorem realized_xor_glued :
    (Compile.Realization.interpretation input (Fin 25) authored).Satisfies
      (Compile.Realization.descend input config)
      ((Compile.Realization.fieldFormula input sizeField).translate (groupLabel input)) :=
  compiled_glued_model _ ⟨.inr (.inr sizeField), rfl⟩

end Clafer.Examples.Telematics.Structural
