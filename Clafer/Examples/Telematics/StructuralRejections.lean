module

public import Clafer.Examples.Telematics.Structural

-- [proof->req~clafer-inherited-witnesses~1]

/-! # Rejected inherited realizations (telematics, selected D2/D4/D6)

SoSyM Appendix 6 (PDF p.34).

These mutations exercise the actual shared-object obligations and generated
realized-field group predicate. They are not a full expression countermodel.
-/

@[expose] public section
namespace Clafer.Examples.Telematics.Structural
open CategoryTheory MCS Compile DPGraph DPGraph.Predicates Semantics

/-- A competing context may not move ECU1's version to ECU2. -/
theorem inconsistent_context_parent :
    ¬ Semantics.Realization.Contains config 21 2 3 6 := by
  unfold Semantics.Realization.Contains
  decide

theorem inconsistent_context_reference :
    ¬ Semantics.Realization.Deref config 21 1 6 2 := by
  unfold Semantics.Realization.Deref Semantics.Realization.View
  decide

def sharedOwner : Configuration (Fin 28) (Fin 25) :=
  { config with contains := fun d p x => config.contains d p x ∨ (d = 21 ∧ p = 3 ∧ x = 6) }

theorem shared_owner_rejected : ¬ sharedOwner.Parents core.toEffectiveCore := by
  intro h
  have he := (h 21 20 rfl 6 (by dsimp [sharedOwner]; decide)).unique
    (show sharedOwner.contains 21 2 6 from Or.inl (by decide))
    (show sharedOwner.contains 21 3 6 from Or.inr ⟨rfl,rfl,rfl⟩)
  exact (by decide : (2 : Fin 25) ≠ 3) he

/-- Move a distinct occurrence to an already occupied mandatory set field.
Parent uniqueness alone cannot detect this duplication; the set key does. -/
def duplicated : Configuration (Fin 28) (Fin 25) :=
  { config with contains := fun d p x => if d = 21 ∧ x = 7 then p = 2 else config.contains d p x }

theorem duplicate_rejected : ¬ duplicated.Keys core.toEffectiveCore := by
  intro h
  have he := h 21 rfl 2 1 6 7
    (by dsimp [duplicated]; decide) (by dsimp [duplicated]; decide)
    (by simp [duplicated]) (by dsimp [duplicated]; decide)
  exact (by decide : (6 : Fin 25) ≠ 7) he

def uncovered : Configuration (Fin 28) (Fin 25) :=
  { config with head := fun d => if d = 25 then ∅ else config.head d }

theorem uncovered_rejected : ¬ Semantics.Realization.Abstracts core uncovered := by
  intro h
  obtain ⟨c,hc,hx⟩ := (h 13 rfl).1 12 (by dsimp [uncovered]; decide)
  have he : c = 25 := by
    rw [supers_eq] at hc
    fin_cases c <;> simp [supers] at hc ⊢
  subst c
  simp [uncovered] at hx

def overlapping : Configuration (Fin 28) (Fin 25) :=
  { config with head := fun d => if d = 2 then insert 2 (config.head d) else config.head d }

theorem overlap_rejected : ¬ Semantics.Realization.Abstracts core overlapping := by
  intro h
  exact (h 26 rfl).2 1 2 rfl rfl (by dsimp [overlapping]; decide) 2 ⟨by dsimp [overlapping]; decide, by dsimp [overlapping]; decide⟩

theorem uncovered_generated_cover :
    ¬ (Compile.Realization.interpretation input (Fin 25) authored).Satisfies
      (uncovered.interpret core.toEffectiveCore)
      (Compile.Realization.abstractFormula input ⟨13,rfl⟩ false) := by
  intro h
  obtain ⟨c,hc,hx⟩ := (Compile.Realization.cover_iff core uncovered 13).mp h 12
    (by dsimp [uncovered]; decide)
  have he : c = 25 := by
    rw [supers_eq] at hc
    fin_cases c <;> simp [supers] at hc ⊢
  subst c
  simp [uncovered] at hx

theorem overlap_inherits : overlapping.Inherits core.toEffectiveCore := by
  intro d c hc
  rw [supers_eq] at hc
  fin_cases d <;> simp [supers] at hc
  all_goals subst c; simp [overlapping,config,heads]

theorem overlap_generated_disjoint :
    ¬ (Compile.Realization.interpretation input (Fin 25) authored).Satisfies
      (overlapping.interpret core.toEffectiveCore)
      (Compile.Realization.abstractFormula input ⟨26,rfl⟩ true) := by
  intro h
  have hd := (Compile.Realization.disjoint_iff core overlapping overlap_inherits 26).mp h
  exact hd 1 2 rfl rfl (by decide) 2
    ⟨by dsimp [overlapping]; decide, by dsimp [overlapping]; decide⟩

/-- Version and server are distinct field declarations, even though their
inherited views reuse each declaration's own occurrence identities. -/
def unrelatedFields : Configuration (Fin 28) (Fin 25) :=
  { config with head := fun d => {x | x ∈ config.head d ∨ (d = 24 ∧ x = 6)} }

theorem unrelated_fields_typed : unrelatedFields.Typed core.toEffectiveCore := by
  constructor
  · intro d p x h
    obtain ⟨hx, c, hc, hp⟩ := typed.1 d p x h
    exact ⟨Or.inl hx, c, hc, Or.inl hp⟩
  · intro d x t h
    obtain ⟨hx, c, hc, ht⟩ := typed.2 d x t h
    exact ⟨Or.inl hx, c, hc, Or.inl ht⟩

theorem unrelated_fields_disjoint_rejected :
    ¬ unrelatedFields.DeclarationDisjoint core.toEffectiveCore := by
  intro h
  have hc := h 21 24 6 (Or.inl (by decide)) (Or.inr ⟨rfl, rfl⟩)
  change Groups.Ancestor core.family 21 24 ∨ Groups.Ancestor core.family 24 21 at hc
  simp [ancestor_iff, ancestorTable] at hc

theorem unrelated_fields_rejected : ¬ Semantics.Realization.Satisfies core unrelatedFields := by
  intro h
  exact unrelated_fields_disjoint_rejected h.2.2.2.2.2

/-- Add small alongside large at the same realized options.size context. -/
def twoOptions : Configuration (Fin 28) (Fin 25) :=
  { config with
    head := fun d => if d = 15 then {17} else config.head d
    contains := fun d p x => if d = 15 then p = 14 ∧ x = 17 else config.contains d p x }

theorem two_options_typed : twoOptions.Typed core.toEffectiveCore := by
  constructor
  · intro d p x h
    by_cases hd : d = 15
    · subst d
      rcases h with ⟨rfl,rfl⟩
      exact ⟨by dsimp [twoOptions]; decide,14,rfl,by dsimp [twoOptions]; decide⟩
    · have hh : config.contains d p x := by simpa [twoOptions,hd] using h
      obtain ⟨hx,c,hc,hp⟩ := typed.1 d p x hh
      refine ⟨by simpa [twoOptions,hd] using hx,c,hc,?_⟩
      by_cases he : c = 15
      · subst c
        rw [parents_eq] at hc
        have imp : ∀ d : Fin 28, parents d ≠ some 15 := by dsimp [twoOptions]; decide
        exact (imp d hc).elim
      · simpa [twoOptions,he] using hp
  · intro d x t h
    obtain ⟨hx,c,hc,ht⟩ := typed.2 d x t h
    have hd : d ≠ 15 := by
      intro he; subst d; simp [twoOptions,config,targets] at h
    have hn : c ≠ 15 := by
      intro he; subst c
      rw [references_eq] at hc
      have imp : ∀ d : Fin 28, (references d).target ≠ some 15 := by dsimp [twoOptions]; decide
      exact imp d hc
    exact ⟨by simpa [twoOptions,hd] using hx,c,hc,by simpa [twoOptions,hn] using ht⟩

theorem two_options_rejected : ¬ Compile.Groups.Holds core.family twoOptions 14 := by
  intro h
  have hh := h ⟨14,by dsimp [twoOptions]; decide⟩
  change InRange one {y : Fin 25 // Compile.Groups.ChildObjects core.family twoOptions 14 14 y} at hh
  have hs := (Semantics.inRange_one_iff _).mp hh |>.2
  let l : {y : Fin 25 // Compile.Groups.ChildObjects core.family twoOptions 14 14 y} :=
    ⟨16,14,.refl,16,rfl,by dsimp [twoOptions]; decide⟩
  let r : {y : Fin 25 // Compile.Groups.ChildObjects core.family twoOptions 14 14 y} :=
    ⟨17,14,.refl,15,rfl,by dsimp [twoOptions]; decide⟩
  have he : (16 : Fin 25) = 17 := congrArg Subtype.val (@Subsingleton.elim _ hs l r)
  exact (by decide : (16 : Fin 25) ≠ 17) he

theorem generated_xor_rejects_two :
    ¬ (Compile.Realization.interpretation input (Fin 25) authored).Satisfies
      (twoOptions.interpret core.toEffectiveCore) (Compile.Realization.fieldFormula input sizeField) := by
  intro h
  exact two_options_rejected ((Compile.Realization.field_iff input authored twoOptions two_options_typed sizeField).mp h)

theorem glued_xor_rejects_two :
    ¬ (Compile.Realization.interpretation input (Fin 25) authored).Satisfies
      (Compile.Realization.descend input twoOptions)
      ((Compile.Realization.fieldFormula input sizeField).translate (groupLabel input)) := by
  intro h
  have hh := (Interpretation.satisfies_translate _ _ _ _).mp h
  erw [Compile.Realization.descend_reduct input twoOptions] at hh
  exact generated_xor_rejects_two hh

end Clafer.Examples.Telematics.Structural
