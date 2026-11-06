module

public import Clafer.Compile.GroupExamples

-- [proof->req~clafer-compile-groups~1]

/-! # The same object visible in an own and an inherited head counts once

This exercises group interpretation on typed relations. Realizing the abstract
child as a complete inherited family remains an explicit #66 obligation.
These group-only witnesses retain raw overlap and do not assert #87 whole-model
declaration disjointness.
-/

@[expose] public section
namespace Clafer.Compile.GroupOverlapExamples
open CategoryTheory MCS DPGraph DPGraph.Predicates Semantics GroupExamples

def base : Configuration (Fin 7) (Objects 1) := config (fun _ => 0)

def overlap : Configuration (Fin 7) (Objects 1) where
  root := base.root
  head d := {x | x ∈ base.head d ∨ (d = 6 ∧ x = .inr 0)}
  contains d p x := base.contains d p x ∨ (d = 6 ∧ p = .inl 1 ∧ x = .inr 0)
  deref d x t := base.deref d x t ∨ (d = 6 ∧ x = .inr 0 ∧ t = .inl 2)

theorem overlap_typed : overlap.Typed (core none (by decide)) := by
  have h := typed none (by decide) (fun _ : Fin 1 => 0)
  constructor
  · intro d p x hx
    rcases hx with hb | ⟨rfl, rfl, rfl⟩
    · obtain ⟨hy, a, ha, hp⟩ := h.1 d p x hb
      exact ⟨Or.inl hy, a, ha, Or.inl hp⟩
    · exact ⟨Or.inr ⟨rfl, rfl⟩, 5, rfl, Or.inl (by simp [base, config])⟩
  · intro d x t hx
    rcases hx with hb | ⟨rfl, rfl, rfl⟩
    · obtain ⟨hy, a, ha, ht⟩ := h.2 d x t hb
      exact ⟨Or.inl hy, a, ha, Or.inl ht⟩
    · exact ⟨Or.inr ⟨rfl, rfl⟩, 4, rfl, Or.inl (by simp [base, config])⟩

theorem union_unchanged (p y : Objects 1) :
    Groups.ChildObjects (core none (by decide)).family overlap 1 p y ↔
      Groups.ChildObjects (core none (by decide)).family base 1 p y := by
  constructor
  · rintro ⟨a, ha, c, hc, h | ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨a, ha, c, hc, h⟩
    · exact ⟨1, .refl, 2, rfl, by simp [base, config]⟩
  · rintro ⟨a, ha, c, hc, h⟩
    exact ⟨a, ha, c, hc, Or.inl h⟩

theorem overlap_holds : Groups.Holds (core none (by decide)).family overlap 1 := by
  have hb := (holds_count none (by decide) (fun _ : Fin 1 => 0)).mpr (by decide)
  intro x
  have hx : x.val ∈ base.head 1 := by
    rcases x.property with h | ⟨h, _⟩
    · exact h
    · cases h
  apply (inRange_iff _ (Equiv.subtypeEquivRight (fun y => union_unchanged x.val y))).mpr
  exact hb ⟨x.val, hx⟩

theorem two_head_paths_one_object :
    overlap.contains 2 (.inl 1) (.inr 0) ∧
    overlap.contains 6 (.inl 1) (.inr 0) := ⟨Or.inl (by simp [base, config]), Or.inr ⟨rfl, rfl, rfl⟩⟩

theorem compiled_overlap_xor :
    (groupInterpretation (input none (by decide)) (Objects 1) (authored none (by decide) _)).Satisfies
      (overlap.interpret (core none (by decide)))
      (generatedGroup (input none (by decide)) (parentId none (by decide))) :=
  (generated_group_iff _ _ _ overlap_typed _).mpr overlap_holds

theorem glued_overlap_xor :
    (groupInterpretation (input none (by decide)) (Objects 1) (authored none (by decide) _)).Satisfies
      (descendGroups (input none (by decide)) overlap)
      ((generatedGroup (input none (by decide)) (parentId none (by decide))).translate
        (groupLabel (input none (by decide)))) :=
  (descended_group_iff _ _ _ overlap_typed _).mpr overlap_holds

end Clafer.Compile.GroupOverlapExamples
