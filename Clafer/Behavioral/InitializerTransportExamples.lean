module

public import Clafer.Behavioral.InitializerCompatibility
public import Clafer.Behavioral.InitializerCandidateExamples

/-! # Source-context transport witnesses

Behavioral §5 Definitions 4–5 / §6.1 and #171's accepted examples. The
Box/child lifetime trace is structurally admitted. Opaque reference targets 5/6
can stand for distinct values; the conditional itself returns mathematical 1/2.
-/

@[expose] public section
namespace Clafer.Behavioral.Initializers.TransportExamples
open Transport

/-- Box 1 and x 3 live at zero and disappear next; root remains present. -/
def disappearing : Trace (Fin 4) (Fin 8) :=
  CandidateExamples.sample (fun t => if t = 0 then 0 else 2)

theorem disappearing_valid : disappearing.Valid Examples.model :=
  CandidateExamples.sample_valid _

/-- The resolved flag view is empty at the next state. The formula retains its
original Box attachment; only generated initialization attaches to x. -/
def flagCondition : Formula (SetAtom (Fin 4)) (SetExpr (Fin 4)) 0 :=
  .next (.atom (.inhabited (.thisStep (.child 2))))

noncomputable def rhs : Value (Fin 8) Int 0 :=
  conditional disappearing (.ofTotal (.sets Examples.model disappearing)) flagCondition
    (fun _ _ => some 1) (fun _ _ => some 2)

-- [utest->req~behavioral-environments~1]
-- [utest->req~behavioral-formula-denotation~1]
theorem original_condition_false :
    ¬ flagCondition.raw disappearing (.sets Examples.model disappearing) (.closed 1) 0 := by
  simp [flagCondition, Formula.raw, Lifetime.next, Trace.ParentPresent, disappearing,
    CandidateExamples.sample, Examples.pool, Examples.cycling, Examples.phaseLive,
    Observation.sets, SetAtom.eval, SetExpr.eval, Step.image, Step.relation,
    Trace.raw, Trace.ParentAt, Environment.closed]

/-- A name-only rewrite keeps the live-filtered parent navigation but changes
the temporal bound: Box disappearance cancels X in the child context. -/
def naiveCondition : Formula (SetAtom (Fin 4)) (SetExpr (Fin 4)) 0 :=
  .next (.atom (.inhabited (.step (.child 2) (.thisStep .parent))))

theorem naive_condition_true :
    naiveCondition.raw disappearing (.sets Examples.model disappearing) (.closed 3) 0 := by
  simp [naiveCondition, Formula.raw, Lifetime.next, Trace.ParentPresent, disappearing,
    CandidateExamples.sample, Examples.pool, Examples.cycling, Examples.phaseLive,
    Environment.closed]

theorem original_requires_two : rhs (.closed 1) 0 = some 2 := by
  classical
  have domain := Formula.total_defined disappearing (.sets Examples.model disappearing)
    flagCondition (.closed 1) 0
  simp only [rhs, conditional, condition, domain, ↓reduceIte]
  have falseCondition : ¬ flagCondition.raw disappearing
      (PartialObservation.ofTotal (.sets Examples.model disappearing)).canonical (.closed 1) 0 :=
    original_condition_false
  simp [falseCondition, choose]

theorem transported_requires_two : moved rhs (move (.closed 1) 3) 0 = some 2 := by
  rw [observation_preserved, original_requires_two]

theorem name_only_requires_one :
    conditional disappearing (.ofTotal (.sets Examples.model disappearing)) naiveCondition
      (fun _ _ => some (1 : Int)) (fun _ _ => some 2) (.closed 3) 0 = some 1 := by
  classical
  have domain := Formula.total_defined disappearing (.sets Examples.model disappearing)
    naiveCondition (.closed 3) 0
  simp only [conditional, condition, domain, ↓reduceIte]
  have trueCondition : naiveCondition.raw disappearing
      (PartialObservation.ofTotal (.sets Examples.model disappearing)).canonical (.closed 3) 0 :=
    naive_condition_true
  simp [trueCondition, choose]

-- [utest->req~behavioral-reference-atoms~1]
theorem strict_unselected_branch : choose (some true) (some (1 : Int)) none = none := rfl

theorem absent_direct_navigation :
    SetExpr.eval Examples.model disappearing (.closed 3) 1 (.thisStep .parent) = ∅ ∧
    SetExpr.eval Examples.model disappearing (.closed 1) 1 (.thisStep .parent) = {0} := by
  constructor <;> ext x <;>
    simp [SetExpr.eval, Step.image, Step.relation, Environment.closed, disappearing,
      CandidateExamples.sample, Examples.cycling, Examples.phaseLive, Examples.pool] <;>
    fin_cases x <;> decide

/-- At later absence, restoring the original identity still reaches root;
reconstructing it via child.parent would have lost the absent Box. -/
theorem moved_absent_parent :
    moved (fun ρ t => some (SetExpr.eval Examples.model disappearing ρ t (.thisStep .parent)))
      (move (.closed 1) 3) 1 = some {0} := by
  rw [observation_preserved, absent_direct_navigation.2]

-- [utest->req~behavioral-environments~1]
theorem capture_avoiding (ρ : Environment (Fin 8) 1) (S : Set (Fin 8)) :
    ((move ρ 3).push S).restore.lookup 0 = S ∧
    ((move ρ 3).push S).restore.lookup 1 = ρ.lookup 0 ∧
    ((move ρ 3).push S).child.lookup 0 = {3} := by
  exact ⟨rfl, rfl, rfl⟩

theorem nested_capture (ρ : Environment (Fin 8) 1) (S T : Set (Fin 8)) :
    (((move ρ 3).push S).push T).restore = (ρ.push S).push T := by simp

/-- Captured values are neither refreshed nor intersected with current live
objects when a generated binder is introduced. -/
theorem retained_capture :
    moved (fun ρ t => some (SetExpr.eval Examples.model disappearing ρ t (.var 0)))
      (move ((Environment.closed 1).push {3}) 4) 1 = some {3} := by
  rw [observation_preserved]
  rfl

theorem inherited_root_context :
    attach disappearing.identities .root Fin.elim0 3 = some (move (.closed 0) 3) := rfl

end Clafer.Behavioral.Initializers.TransportExamples
