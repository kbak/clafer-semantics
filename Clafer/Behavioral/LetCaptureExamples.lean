module

public import Clafer.Behavioral.LetCapture
public import Clafer.Behavioral.FormulaExamples

/-!
# Temporal let counterexamples on a valid trace

The independently admitted cycling trace has persistent targets 5 and 6,
reference heads 3 and 4, and a parent gap at phase 2. At phase 3 a head targets
6; at phase 0 it targets 5. D1 retains a captured target set across this change.
These witnesses do not assert parsing or Haskell/Alloy preservation.
-/

@[expose] public section
namespace Clafer.Behavioral.LetCaptureExamples
open Examples FormulaExamples

/-- The outer resolved variable supplies the singleton old target for comparison. -/
def oldTarget : Environment (Fin 8) 1 := source.push {6}

def targets {n : Nat} : SetExpr (Fin 4) n := .thisStep (.deref 2)
def sameOld : SF 2 := .atom (.equal (.var 0) (.var 1))

private theorem targets_at_three : targets.eval model cycling oldTarget 3 = {6} := by
  ext x
  simp [targets, SetExpr.eval, Step.image, Step.relation, oldTarget, source,
    Environment.push, Environment.closed, cycling, phaseDeref, phaseLive]
  rintro rfl
  simp

private theorem targets_at_four : targets.eval model cycling oldTarget 4 = {5} := by
  ext x
  simp [targets, SetExpr.eval, Step.image, Step.relation, oldTarget, source,
    Environment.push, Environment.closed, cycling, phaseDeref, phaseLive]
  rintro rfl
  simp

-- [utest->req~behavioral-environments~1]
-- [utest->req~behavioral-formula-denotation~1]
/-- Capturing the target before next succeeds; evaluating it inside next fails.
The parent survives this edge, so neither outcome is a cancellation artefact. -/
theorem target_capture_distinguishes :
    cycling.Admissible model ∧
    (Formula.letSet targets (.next sameOld)).denote cycling sets true oldTarget 3 ∧
    ¬ (Formula.next (.letSet targets sameOld)).denote cycling sets true oldTarget 3 := by
  refine ⟨cycling_admissible, ?_, ?_⟩
  · intro _
    change targets.eval model cycling oldTarget 3 = ({6} : Set (Fin 8))
    exact targets_at_three
  · intro h
    have hp : cycling.ParentPresent oldTarget.this 4 := by
      simp [oldTarget, source, Environment.push, Environment.closed,
        Trace.ParentPresent, cycling, pool, phaseLive]
    have bad := h hp
    change targets.eval model cycling oldTarget 4 = ({6} : Set (Fin 8)) at bad
    rw [targets_at_four] at bad
    have hm : (5 : Fin 8) ∈ ({6} : Set (Fin 8)) := bad ▸ (by simp)
    simp at hm

-- [utest->req~behavioral-environments~1]
/-- Same-state evaluation is preserved, while the captured target differs from
current navigation of the retained head. -/
theorem same_state_and_current_head :
    (Formula.letSet targets sameOld).denote cycling sets true oldTarget 3 ∧
    (SetExpr.step (.deref 2) (.var 0)).eval model cycling (source.push {3}) 4 = {5} ∧
    (SetExpr.var 0 : SetExpr (Fin 4) 1).eval model cycling (source.push {6}) 4 = {6} := by
  refine ⟨targets_at_three, ?_, rfl⟩
  ext x
  simp [SetExpr.captured_deref, cycling, phaseLive, phaseDeref]
  rintro rfl
  simp

-- [utest->req~behavioral-environments~1]
/-- Captured membership persists through a head gap and same-identity rebirth;
fresh evaluation of the changing extent is empty at the gap. This observation
claim does not resume an obligation cancelled by the intervening parent gap. -/
theorem changing_set_and_rebirth :
    (SetExpr.extent 2 : SetExpr (Fin 4) 0).eval model cycling source 0 = {3, 4} ∧
    (SetExpr.extent 2 : SetExpr (Fin 4) 0).eval model cycling source 1 = ∅ ∧
    (∀ t, (SetExpr.var 0 : SetExpr (Fin 4) 1).eval model cycling (source.push {3, 4}) t = {3, 4}) ∧
    3 ∈ cycling.live 3 := by
  refine ⟨?_, ?_, fun _ => rfl, ?_⟩
  · ext x
    simp only [SetExpr.eval, Trace.raw, cycling, phaseLive, Set.mem_ofPred_eq]
    fin_cases x <;> decide
  · ext x
    simp only [SetExpr.eval, Trace.raw, cycling, phaseLive, Set.mem_ofPred_eq]
    fin_cases x <;> decide
  · simp [cycling, phaseLive]

-- [utest->req~behavioral-reference-atoms~1]
/-- Strict D3 definedness distinguishes an erased unused binding from truth. -/
theorem unused_missing_binding (τ : Trace C U) (O : PartialObservation A D U)
    {n : Nat} (d : D n) (ρ : Environment U n) (t : Nat)
    (missing : O.domain d ρ t = none) :
    (Formula.truth : Formula A D n).Satisfies τ O true ρ t ∧
    ¬ (Formula.letSet d .truth).Satisfies τ O true ρ t ∧
    ¬ (Formula.letSet d .truth).Satisfies τ O false ρ t := by
  exact ⟨⟨trivial, trivial⟩, Formula.letSet_undefined_neither τ O d .truth ρ t missing⟩

end Clafer.Behavioral.LetCaptureExamples
