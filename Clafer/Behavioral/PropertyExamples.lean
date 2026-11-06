module

public import Clafer.Behavioral.Properties
public import Clafer.Behavioral.FormulaExamples

/-! # Universal assertions versus existential scenarios

T5–T6: two structurally valid traces separate feasibility from universality.
The cancellation witness distinguishes meta-level failure from source negation.
-/

@[expose] public section
namespace Clafer.Behavioral.PropertyExamples
open Properties Examples FormulaExamples

def shifted : Trace (Fin 4) (Fin 8) where
  identities := cycling.identities
  live t := cycling.live (t + 1)
  deref t := cycling.deref (t + 1)

theorem shifted_valid : shifted.Valid Examples.model where
  identities := cycling_valid.identities
  root_live t := cycling_valid.root_live (t + 1)
  parent_live t := cycling_valid.parent_live (t + 1)
  states t := by
    have h := cycling_valid.states (t + 1)
    exact ⟨h.typed, h.root_head, h.root_separate, h.inherits, h.abstracts,
      h.parents, h.references, h.keys, h.multiplicities, h.groups, h.disjoint⟩

def observes (τ : Trace (Fin 4) (Fin 8)) : Observation A D (Fin 8) where
  atom _ _ t := (3 : Fin 8) ∈ τ.live t
  domain _ _ _ := ∅

def models : Model (Fin 4) A D (Fin 8) :=
  ⟨fun τ => τ.Valid Examples.model, fun τ => .ofTotal (observes τ), ∅⟩

def startsPresent : Constraint (Fin 4) A D (Fin 8) := Constraint.root error.initially

-- [utest->req~behavioral-properties~1]
theorem good_trace : startsPresent.Holds cycling (.ofTotal (observes cycling)) := by
  unfold startsPresent
  rw [Constraint.root_holds _ _ _ cycling_valid.root_live]
  intro t
  rw [Formula.total_agrees]
  intro birth
  have ht := (Trace.root_starts Examples.model cycling cycling_valid t).mp birth
  subst t
  simp [error, Formula.denote, polarity, observes, cycling, phaseLive]

theorem bad_trace : ¬ startsPresent.Holds shifted (.ofTotal (observes shifted)) := by
  intro h
  have atZero := (Constraint.root_holds _ _ _ shifted_valid.root_live).mp h 0
  rw [Formula.total_agrees] at atZero
  have bad := atZero ((shifted.starts_zero _).mpr (shifted_valid.root_live 0))
  simp [error, Formula.denote, polarity, observes, shifted, cycling, phaseLive] at bad

-- [utest->req~behavioral-properties~1]
theorem possible_not_universal : models.Possible {startsPresent} ∧ ¬ models.Asserts startsPresent := by
  constructor
  · refine ⟨cycling, ⟨cycling_valid, ?_⟩, ?_⟩
    · simp [models]
    · intro c hc
      have : c = startsPresent := hc
      subst c
      exact good_trace
  · intro h
    exact bad_trace (h shifted ⟨shifted_valid, by simp [models]⟩)

def nestedFailure : Constraint (Fin 4) A D (Fin 8) :=
  Constraint.nested (Structural.Core.ofEffective Examples.model) 2 error

def oneGoodInstance : Observation A D (Fin 8) where
  atom _ ρ _ := ρ.this = 3
  domain _ _ _ := ∅

/-- One good instance does not establish a nested assertion for its sibling. -/
-- [utest->req~behavioral-properties~1]
theorem nested_all_instances : ¬ nestedFailure.Holds cycling (.ofTotal oneGoodInstance) := by
  intro h
  have bad := h 0 4 (by
    change (4 : Fin 8) ∈ cycling.live 0 ∧ _
    exact ⟨by simp [cycling, phaseLive], .refl⟩) (by simp [cycling, phaseLive])
  rw [Formula.total_agrees] at bad
  simp [nestedFailure, Constraint.nested, error, Formula.denote, polarity,
    oneGoodInstance, Environment.closed] at bad

/-- At the concrete source attachment both F false and source !F false hold.
Thus an interpreter must negate the interpreted assertion, not replace it by !. -/
theorem source_not_is_not_failure :
    (error.eventually : F 0).denote cycling noError true source 0 ∧
    error.eventually.not.denote cycling noError true source 0 ∧
    ¬ (¬ (error.eventually : F 0).denote cycling noError true source 0) :=
  ⟨both_polarities.1, both_polarities.2, fun h => h both_polarities.1⟩

/-- The negative-scenario mistake: ! (request => next bad) forbids states
without a request. The corrected forbidden event is request && next bad. -/
-- [utest->req~behavioral-properties~1]
theorem negative_scenario_conjunction :
    ¬ (Formula.not (.implies error (.next error)) : F 0).denote cycling noError true (.closed 0) 0 ∧
    (Formula.not (.and error (.next error)) : F 0).denote cycling noError true (.closed 0) 0 := by
  constructor
  · exact fun h => h.1
  · exact Or.inl id

end Clafer.Behavioral.PropertyExamples
