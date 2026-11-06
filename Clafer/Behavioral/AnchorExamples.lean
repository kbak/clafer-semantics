module

public import Clafer.Behavioral.Anchors
public import Clafer.Behavioral.FormulaExamples

/-! # Anchor and recurrence witnesses on an admitted trace

T7/T9: a single root event satisfies anchored existence but not recurrence.
A repeated birth requires a fresh body; finality is tested before disappearance.
-/

@[expose] public section
namespace Clafer.Behavioral.AnchorExamples
open Anchors Examples FormulaExamples

-- [utest->req~behavioral-modifiers~1]
-- [utest->req~behavioral-patterns~1]
theorem once_is_not_recurrent :
    (error.eventually.initially : F 0).Attached cycling eventAtOne (fun _ => {0}) ∧
    ¬ (error.eventually : F 0).Attached cycling eventAtOne (fun _ => {0}) := by
  constructor
  · apply (root_anchored_existence cycling eventAtOne error cycling_valid.root_live).mpr
    exact ⟨1, rfl⟩
  · intro h
    obtain ⟨j, hj, he⟩ := (root_recurrence cycling eventAtOne error cycling_valid.root_live).mp h 2
    change j = 1 at he
    omega

def onlyZero : Observation A D (Fin 8) := { noError with atom := fun _ _ t => t = 0 }

theorem second_birth_required :
    ¬ (error.initially : F 0).PartialAttached cycling (.ofTotal onlyZero) (fun _ => {3}) := by
  intro h
  have atBirth := (initially_at_births _ _ _ _).mp h 3 3 (by simp)
    (by simp [Trace.Starts, cycling, phaseLive])
  rw [Formula.total_agrees] at atBirth
  exact (by decide : ¬ (3 = 0)) atBirth

theorem time_zero_required :
    ¬ (error.initially : F 0).PartialAttached cycling (.ofTotal eventAtOne) (fun _ => {3}) := by
  intro h
  have atBirth := (initially_at_births _ _ _ _).mp h 0 3 (by simp)
    ((cycling.starts_zero 3).mpr (by simp [cycling, phaseLive]))
  rw [Formula.total_agrees] at atBirth
  exact (by decide : ¬ (0 = 1)) atBirth

theorem after_death_too_late :
    ¬ (error.finally : F 0).PartialAttached cycling (.ofTotal eventAtOne) (fun _ => {3}) := by
  intro h
  have atDeath := (finally_at_deaths _ _ _ _).mp h 0 3 (by simp)
    (by simp [Trace.Ends, cycling, phaseLive])
  rw [Formula.total_agrees] at atDeath
  exact (by decide : ¬ (0 = 1)) atDeath

def missing : PartialObservation A D (Fin 8) where
  atom _ _ _ := none
  domain _ _ _ := none

theorem endless_final_is_vacuous :
    (error.finally : F 0).PartialAttached cycling missing (fun _ => {0}) := by
  apply finally_vacuous
  intro t c hc
  have : c = 0 := hc
  subst c
  exact fun h => h.2 (cycling_valid.root_live (t + 1))

end Clafer.Behavioral.AnchorExamples
