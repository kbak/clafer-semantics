module

public import Clafer.Examples.Telematics.Expressions
public import Clafer.Compile.ConstraintMeaning

/-!
[impl->req~clafer-appendix-f-complete~1]
[proof->req~clafer-appendix-f-complete~1]
-/

/-!
# Complete resolved telematics input

SoSyM Appendix 6 PDF p.34, Appendix 3 and §6.2.4–5. The source map is manual:
all d01–d26 declarations reuse the reviewed inherited projection; all c01–c12
bodies reuse the reviewed expression inventory. The implicit integer head has
unrestricted bounds, as required for the complete mathematical integer domain.
-/

@[expose] public section
namespace Clafer.Examples.Telematics
open CategoryTheory MCS Compile DPGraph DPGraph.Predicates Semantics Constraints

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def contexts : Fin 12 → Fin 28 := ![1,11,15,15,19,19,19,19,19,0,0,0]

def sourceBoundary (c : Fin 12) : ConstraintBoundary where
  id := c.val + 1
  context := ⟨(contexts c).val⟩
  scopeOccurrences := List.ofFn (fun d : Fin 28 => DeclId.mk d.val)

def attachments : Nat → List ConstraintBoundary
  | 0 => [sourceBoundary 9, sourceBoundary 10, sourceBoundary 11]
  | 1 => [sourceBoundary 0]
  | 11 => [sourceBoundary 1]
  | 15 => [sourceBoundary 2, sourceBoundary 3]
  | 19 => [sourceBoundary 4, sourceBoundary 5, sourceBoundary 6,
      sourceBoundary 7, sourceBoundary 8]
  | _ => []

def decl (n : Nat) : Declaration :=
  { Telematics.Structural.decl n with
    constraints := attachments n
    multiplicity := if n = 27 then ⟨some unrestricted, unrestricted⟩
      else (Telematics.Structural.decl n).multiplicity }

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
  root_exists := by simp [AST.Known, entries, decl, Telematics.Structural.decl]
  root_origin := by decide
  root_shape := by decide
  parent_exists := by simp [entries, decl, Telematics.Structural.decl, AST.Known]
  parent_depth := by decide
  parentless_abstract := by decide
  nested_abstract := by decide
  primitive_shape := by simp [entries, decl, Telematics.Structural.decl, PrimitiveDomain.name]
  unique_domains := by simp [entries, decl, Telematics.Structural.decl]
  targets_resolved := by simp [entries, decl, Telematics.Structural.decl, Reference.target, AST.Known]
  supers_resolved := by simp [entries, decl, Telematics.Structural.decl, AST.Known]
  inheritance_kind := by
    unfold Kind.CanExtend
    decide
  inheritance_parent := by decide
  inheritance_rank := by
    refine ⟨fun id => if id = ⟨16⟩ ∨ id = ⟨17⟩ then 3 else
        if id = ⟨14⟩ ∨ id = ⟨15⟩ then 2 else
        if id = ⟨10⟩ ∨ id = ⟨11⟩ ∨ id = ⟨13⟩ then 1 else 0, ?_⟩
    simp [entries, decl, Telematics.Structural.decl]
  valid_bounds := by decide
  defaults := defaults_valid
  constraints_resolved := by
    simp [entries, decl, Telematics.Structural.decl, attachments, sourceBoundary, contexts,
      ConstraintBoundary.Resolved, AST.Known]


theorem support_resolved (c : Fin 28) : (Telematics.Expressions.support c).Resolved ast := by
  constructor
  · intro v; fin_cases v <;> simp [AST.Known, entries, decl, Telematics.Structural.decl]
  · intro e; fin_cases e <;> simp [Support.MapResolved, Telematics.Expressions.support,
      Telematics.Expressions.maps, entries, decl, Telematics.Structural.decl, Reference.target]
  · intro v h; fin_cases v <;> simp_all [Telematics.Expressions.support,
      entries, decl, Telematics.Structural.decl]

theorem boundary_resolved (c : Fin 12) : (sourceBoundary c).Resolved ast.Known := by
  fin_cases c <;> simp [sourceBoundary, contexts, ConstraintBoundary.Resolved,
    AST.Known, entries, decl, Telematics.Structural.decl]

noncomputable def sourceIndex (q : ConstraintId ast) : Fin 12 :=
  ⟨(boundary ast q).id - 1, by
    rcases q with ⟨c,k⟩
    change Fin 28 at c
    fin_cases c <;> fin_cases k <;> decide⟩

theorem attached_boundary (q : ConstraintId ast) :
    boundary ast q = sourceBoundary (sourceIndex q) := by
  rcases q with ⟨c,k⟩
  change Fin 28 at c
  fin_cases c <;> fin_cases k <;> rfl

theorem inventory_input (c : Fin 12) :
    (Telematics.Expressions.inventory c).Input ast (sourceBoundary c) := by
  fin_cases c
  all_goals refine ⟨wf, support_resolved _, boundary_resolved _, ⟨?_⟩, rfl, ⟨.nil⟩⟩
  all_goals exact {
    context_eq := rfl
    occurrence := fun d => ⟨d.val, by change d.val < 28; exact d.isLt⟩
    occurrence_eq := by intro d; change DeclId.mk d.val = (List.ofFn (fun v : Fin 28 => DeclId.mk v.val))[d.val]; rw [List.getElem_ofFn]
    domain := fun d => Fin.elim0 d
    domain_eq := fun d => Fin.elim0 d }

noncomputable def input : Input ast where
  ast := wf
  root_name := by
    intro d hd
    simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [decl, Telematics.Structural.decl]
  user_names := by
    intro d hd
    simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [decl, Telematics.Structural.decl, predefinedStrings]
    all_goals intro dom; cases dom <;> decide
  constraint q := Telematics.Expressions.inventory (sourceIndex q)
  typed q := by rw [attached_boundary]; exact inventory_input _
  positive_support q := by
    generalize sourceIndex q = c
    fin_cases c <;> decide

noncomputable def result := compile input

theorem mcs_valid : MCS.Valid result.labels result.formulas := wellFormed input


noncomputable def core : Semantics.Realization.Core 28 := Semantics.Realization.Core.ofInput input

def bounds (d : Fin 28) : Range := if d = 12 then unrestricted else Telematics.Structural.bounds d

theorem parents_eq (d : Fin 28) : core.family.parent d = Telematics.Structural.parents d := by
  fin_cases d <;> rfl

theorem supers_eq (d : Fin 28) : core.family.super d = Telematics.Structural.supers d := by
  fin_cases d <;> rfl

theorem references_eq (d : Fin 28) : core.family.reference d = Telematics.Structural.references d := by
  fin_cases d <;> rfl

theorem explicit_eq (d : Fin 28) : core.explicitAbstract d = Telematics.Structural.explicit d := by
  fin_cases d <;> rfl

theorem effective_eq (d : Fin 28) : core.family.isAbstract d = Telematics.Structural.effective d := by
  fin_cases d <;> rfl

theorem bounds_eq (d : Fin 28) : core.family.multiplicity d = bounds d := by
  fin_cases d <;> rfl

theorem groupBounds_eq (d : Fin 28) : core.group d = Telematics.Structural.groupBounds d := by
  fin_cases d <;> rfl

theorem family_groups (d : Fin 28) : (core.family.group d).effective.range = Telematics.Structural.groupBounds d := by
  fin_cases d <;> rfl

theorem selected : core.Selected := by
  unfold Semantics.Realization.Core.Selected
  simp only [parents_eq, supers_eq, references_eq, explicit_eq, effective_eq]
  refine ⟨by decide, by decide, ?_, by decide, ?_⟩
  · intro d c hc
    fin_cases d <;> simp [Telematics.Structural.supers] at hc
    all_goals subst c; exact ⟨rfl,rfl⟩
  · refine ⟨![0,1,1,2,1,2,3,3,2,2,3,3,1,8,9,10,10,9,10,11,7,8,3,6,7,7,2,5], ?_, ?_⟩
    · decide
    · decide




/-- Every printed conjunct has one actual owner/position attachment. -/
noncomputable def occurrence : Fin 12 → ConstraintId ast :=
  ![⟨13,⟨0,by decide⟩⟩, ⟨23,⟨0,by decide⟩⟩, ⟨27,⟨0,by decide⟩⟩, ⟨27,⟨1,by decide⟩⟩, ⟨4,⟨0,by decide⟩⟩, ⟨4,⟨1,by decide⟩⟩,
    ⟨4,⟨2,by decide⟩⟩, ⟨4,⟨3,by decide⟩⟩, ⟨4,⟨4,by decide⟩⟩, ⟨0,⟨0,by decide⟩⟩, ⟨0,⟨1,by decide⟩⟩, ⟨0,⟨2,by decide⟩⟩]

theorem sourceIndex_occurrence (c : Fin 12) : sourceIndex (occurrence c) = c := by
  fin_cases c <;> rfl

theorem occurrence_sourceIndex (q : ConstraintId ast) : occurrence (sourceIndex q) = q := by
  rcases q with ⟨c,k⟩
  change Fin 28 at c
  fin_cases c <;> fin_cases k <;> rfl

theorem occurrence_body (c : Fin 12) : input.constraint (occurrence c) = Telematics.Expressions.inventory c := by
  change Telematics.Expressions.inventory (sourceIndex (occurrence c)) = _
  rw [sourceIndex_occurrence]

theorem occurrence_owner (c : Fin 12) :
    (ast.at (occurrence c).1).declaration.id = ⟨(contexts c).val⟩ := by
  fin_cases c <;> rfl

theorem gluing_compatible : Gluing.Compatible (roles input) (labels input) (groupAnnotations input) :=
  groupCompatible input

theorem effective_defaults : Gluing.Defaults (roles input) (Compile.Realization.bank input) :=
  Compile.Realization.defaults input

theorem formalcd_valid : (Compile.Realization.glued input).toRawOver.WellFormed :=
  (Compile.Realization.glued input).wellFormed

theorem exact_declarations (φ) : φ ∈ (Compile.Realization.glued input).declarations ↔
    ∃ q, ((Compile.Realization.bank input).formula q).translate (groupLabel input) = φ :=
  Compile.Realization.glued_declarations input φ

end Clafer.Examples.Telematics
