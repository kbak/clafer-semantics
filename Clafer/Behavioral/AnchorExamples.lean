module

public import Clafer.Behavioral.ExplicitAnchors
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

def presentThis {n} : SF n := .atom (.inhabited .this)

private theorem some_this (ρ : Environment (Fin 8) 0) (t : Nat) :
    presentThis.raw cycling sets ρ t ↔ ρ.this ∈ cycling.live t := by
  change (∃ x, x = ρ.this ∧ x ∈ cycling.live t) ↔ _
  simp

/-- The attachment is live at state 2. At states 3 and 4 its parent survives,
but the context is absent. Testing only predecessor absence invents a birth. -/
-- [utest->req~behavioral-past-formulas~1]
theorem nested_initially_requires_current_presence :
    let ρ : Environment (Fin 8) 0 := .closed 2
    let p : SF 0 := .not .truth
    let written := (p.initially.next.next).lower.expandAnchors
    let printed := ((presentThis.previous.not.implies p).next.next).lower
    ρ.this ∈ cycling.live 2 ∧ written.eval cycling sets ρ 2 ∧
      ¬ printed.eval cycling sets ρ 2 ∧ printed.AnchorFree := by
  dsimp only
  rw [Core.expandAnchors_agrees, Formula.lower_agrees, Formula.lower_agrees]
  refine ⟨by simp [Environment.closed, cycling, phaseLive], ?_, ?_, by trivial⟩
  · simp only [Formula.raw, Lifetime.next, not_true_eq_false]
    intro _ _ birth
    exact (by simp [cycling, phaseLive] : (2 : Fin 8) ∉ cycling.live 4) birth.1
  · simp only [Formula.raw, Lifetime.next, Lifetime.previous, some_this, not_true_eq_false]
    intro h
    have parent (t : Nat) : cycling.ParentPresent 2 t :=
      Or.inr ⟨0, rfl, cycling_valid.root_live t⟩
    exact h (parent 3) (parent 4) (fun prev =>
      (by simp [cycling, phaseLive] : (2 : Fin 8) ∉ cycling.live 3) prev.2)

/-- Signed source negation remains inside the anchor. Even an exact classical
birth test cannot turn a negated inactive anchor into a negated implication. -/
-- [utest->req~behavioral-past-formulas~1]
theorem negation_at_inactive_root_birth :
    let ρ : Environment (Fin 8) 0 := .closed 0
    (Formula.not (.initially .truth) : SF 0).denote cycling sets true ρ 1 ∧
    ¬ (Formula.not (.implies (.and presentThis (.not (.previous presentThis))) .truth) : SF 0).denote
      cycling sets true ρ 1 := by
  dsimp only
  constructor
  · intro birth
    have := (cycling.root_starts model cycling_valid 1).mp birth
    contradiction
  · simp [Formula.denote, polarity]

end Clafer.Behavioral.AnchorExamples
