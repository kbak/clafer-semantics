module

public import Clafer.Behavioral.Patterns
public import Clafer.Behavioral.Properties
public import Clafer.Behavioral.LassoExamples

/-! # Complete pattern matrix and boundary mutations

The independent admitted four-state fixture has a final self-loop. All thirty
pattern/scope combinations have both a satisfying and violating valuation, and
both source polarities are checked. `source_agrees` connects the kernel-computed
finite result to infinite source meaning. No native-decide axiom is used.
-/

@[expose] public section
namespace Clafer.Behavioral.PatternExamples
open Patterns

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

abbrev A (_ : Nat) := Fin 4
abbrev D (_ : Nat) := Unit
abbrev F := Formula A D 0
def p : F := .atom 0
def q : F := .atom 1
def r : F := .atom 2
def s : F := .atom 3
def trace := LassoExamples.cycle 3

/-- Row order N,E,L,A,P,R; column order suffix,before,after,between,after-until. -/
def pattern (row : Fin 6) : Pattern F :=
  match row.val with
  | 0 => .never p | 1 => .sometime p | 2 => .lonce p
  | 3 => .always p | 4 => .precede s p | _ => .follow s p

def scope (column : Fin 5) : Scope F :=
  match column.val with
  | 0 => .suffix | 1 => .before r | 2 => .after q
  | 3 => .between q r | _ => .afterUntil q r

abbrev Valuation := Fin 4 → Fin 4 → Bool

/-- Explicit positive/negative trace fixtures, not values obtained by searching
the expander. All scopes open at 0 and close at 3 when a closing event applies. -/
def matrix (row : Fin 6) (good : Bool) : Valuation := fun atom time =>
  if atom = 1 then time == 0
  else if atom = 2 then time == 3
  else if atom = 3 then
    if row = 4 then time == (if good then 0 else 2)
    else row == 5 && good && time == 2
  else match row.val with
    | 0 => !good && time == 1
    | 1 => good && time == 1
    | 2 => if good then time == 1 || time == 2 else time == 0 || time == 2
    | 3 => good || time == 1
    | _ => time == 1

def finiteObservation (v : Valuation) : FiniteObservation A D 8 3 where
  atom a _ clock := v a clock.1
  domain _ _ _ := ∅

def observation (v : Valuation) : Observation A D (Fin 8) where
  atom a _ t := v a (trace.clock t).1 = true
  domain _ _ _ := ∅

theorem observations_agree (v : Valuation) : (finiteObservation v).Agrees trace (observation v) :=
  ⟨fun _ _ _ => Iff.rfl, fun _ _ _ => Finset.coe_empty⟩

noncomputable def checkFormula (a : F) (v : Valuation) (positive : Bool := true)
    (context : Fin 8 := 0) (time : Nat := 0) : Bool :=
  (a.normalize positive).lower.finite trace (finiteObservation v) (.closed context) (trace.clock time)

noncomputable def check (row : Fin 6) (column : Fin 5) (good positive : Bool) : Bool :=
  checkFormula (expand (pattern row) (scope column)) (matrix row good) positive

-- [proof->req~behavioral-patterns~1]
theorem source_agrees (a : F) (v : Valuation) (positive : Bool) (context : Fin 8) (time : Nat) :
    checkFormula a v positive context time = true ↔
      a.denote trace.unfold (observation v) positive (.closed context) time := by
  rw [checkFormula, Core.finite_agrees trace _ _ (observations_agree v),
    Formula.normalize_lower_agrees, FiniteEnvironment.realize_closed]

-- [utest->req~behavioral-patterns~1]
theorem all_thirty_positive : ∀ row column, check row column true true = true := by
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [check, checkFormula, pattern, scope, expand, p, q, r, s, Formula.normalize, Formula.lower] <;> decide

-- [utest->req~behavioral-patterns~1]
theorem all_thirty_negative : ∀ row column, check row column false true = false := by
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [check, checkFormula, pattern, scope, expand, p, q, r, s, Formula.normalize, Formula.lower] <;> decide

theorem all_thirty_opposite_signs :
    (∀ row column, check row column true false = false) ∧
    (∀ row column, check row column false false = true) := by
  constructor <;> intro row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [check, checkFormula, pattern, scope, expand, p, q, r, s, Formula.normalize, Formula.lower] <;> decide

theorem all_thirty_infinite_witnesses (row : Fin 6) (column : Fin 5) :
    (expand (pattern row) (scope column)).denote trace.unfold (observation (matrix row true)) true (.closed 0) 0 ∧
    ¬ (expand (pattern row) (scope column)).denote trace.unfold (observation (matrix row false)) true (.closed 0) 0 := by
  constructor
  · exact (source_agrees _ _ true 0 0).mp (all_thirty_positive row column)
  · intro h
    have bad := (source_agrees _ _ true 0 0).mpr h
    have no := all_thirty_negative row column
    exact Bool.noConfusion (no.symm.trans bad)

/-- The source fixture used by the complete matrix is structurally admitted. -/
theorem trace_valid : trace.unfold.Valid Examples.model := LassoExamples.cycle_valid 3

def laterTrigger : Valuation := matrix 5 false

/-- The pinned D2 error places the trigger implication outside the whole interval. -/
def pinnedBetween : F :=
  .always (.implies (.and (.and q (.not r)) (.eventually r))
    (.implies p (.strongUntil (.strongUntil (.not r) (.and s (.not r))) r)))

-- [utest->req~behavioral-patterns~1]
theorem between_late_trigger_regression :
    checkFormula pinnedBetween laterTrigger = true ∧
    checkFormula (expand (.follow s p) (.between q r)) laterTrigger = false := by
  simp [checkFormula, expand, pinnedBetween, p, q, r, s,
    Formula.normalize, Formula.lower]
  decide

def repeatedOpener : Valuation := fun atom time =>
  if atom = 0 then time == 1 else if atom = 1 then time == 0 || time == 2
  else if atom = 3 then time == 3 else false

def pinnedAfterPrecedence : F :=
  .or (.always (.not q)) (.eventually (.and q (.weakUntil (.not p) s)))

-- [utest->req~behavioral-patterns~1]
theorem first_opener_regression :
    checkFormula pinnedAfterPrecedence repeatedOpener = true ∧
    checkFormula (expand (.precede s p) (.after q)) repeatedOpener = false := by
  simp [checkFormula, expand, pinnedAfterPrecedence, p, q, s,
    Formula.normalize, Formula.lower]
  decide

def noOpener : Valuation := fun atom time => atom == 0 && time == 1

theorem missing_opener_vacuity :
    checkFormula (expand (.follow s p) (.between q r)) noOpener = true ∧
    checkFormula (expand (.always p) (.after q)) noOpener = true := by
  simp [checkFormula, expand, p, q, r, s,
    Formula.normalize, Formula.lower]
  decide

def unfinished : Valuation := fun atom time => atom == 1 && time == 0

theorem unfinished_scope_difference :
    checkFormula (expand (.sometime p) (.between q r)) unfinished = true ∧
    checkFormula (expand (.sometime p) (.afterUntil q r)) unfinished = false := by
  simp [checkFormula, expand, p, q, r,
    Formula.normalize, Formula.lower]
  decide

def atClose : Valuation := fun atom time =>
  if atom = 1 then time == 0 else (atom == 0 || atom == 2) && time == 3

theorem closing_event_excluded :
    checkFormula (expand (.sometime p) (.between q r)) atClose = false ∧
    checkFormula (expand (.never p) (.between q r)) atClose = true := by
  simp [checkFormula, expand, p, q, r,
    Formula.normalize, Formula.lower]
  decide

def atOpen : Valuation := fun atom time =>
  if atom = 2 then time == 3 else (atom == 0 || atom == 1) && time == 0

theorem opening_event_included :
    checkFormula (expand (.sometime p) (.between q r)) atOpen = true ∧
    checkFormula (expand (.never p) (.between q r)) atOpen = false := by
  simp [checkFormula, expand, p, q, r,
    Formula.normalize, Formula.lower]
  decide

def simultaneous : Valuation := fun atom time => (atom == 1 || atom == 2) && time == 0

theorem simultaneous_empty_interval :
    checkFormula (expand (.sometime p) (.between q r)) simultaneous = true ∧
    checkFormula (expand (.follow s p) (.between q r)) simultaneous = true := by
  simp [checkFormula, expand, p, q, r, s,
    Formula.normalize, Formula.lower]
  decide

/-- No actual closing r occurs. A parent ending must not make the negated
F r scope premise false: the source-negative judgment is G !r. -/
theorem cancellation_scope_premise :
    checkFormula (expand (.always p) (.between q r)) unfinished true 3 0 = true ∧
    checkFormula (expand (.always p) (.between q r)) unfinished false 3 0 = true := by
  simp [checkFormula, expand, p, q, r,
    Formula.normalize, Formula.lower]
  decide


def acrossGap : Valuation := fun atom time =>
  if atom = 1 then time == 0 || time == 3
  else atom == 0 && (time == 1 || time == 3)

/-- The first parent's lifetime cancels an unanswered response. Reappearance
begins a fresh interval whose persistent parent cannot cancel it. -/
theorem parent_gap_and_reappearance :
    checkFormula (expand (.follow s p) (.afterUntil q r)) acrossGap true 3 0 = true ∧
    checkFormula (expand (.follow s p) (.afterUntil q r)) acrossGap true 3 3 = false := by
  simp [checkFormula, expand, p, q, r, s, Formula.normalize, Formula.lower]
  decide

/-- Context 3 disappears at 1, while its parent survives until 2. The failure
at 1 is still inside the constraint's lifetime. -/
theorem context_death_not_cancellation :
    checkFormula (expand (.always p) .suffix) atOpen true 3 0 = false := by
  simp [checkFormula, expand, p, Formula.normalize, Formula.lower]
  decide

def repeatedCloser : Valuation := fun atom time =>
  if atom = 1 then time == 0 else if atom = 2 then time == 1 || time == 3
  else (atom == 0 || atom == 3) && time == 2

/-- A later closing boundary cannot admit an event beyond the first close. -/
theorem first_closer :
    checkFormula (expand (.sometime p) (.between q r)) repeatedCloser = false := by
  simp [checkFormula, expand, p, q, r, Formula.normalize, Formula.lower]
  decide

/-- The first opener has its precedent immediately. The second opens a new
obligation at the root, with p later and no further s. -/
def attachmentOpeners : Valuation := fun atom time =>
  if atom = 1 then time == 0 || time == 2
  else if atom = 3 then time == 0
  else atom == 0 && time == 3

def afterPrecedence : F := expand (.precede s p) (.after q)

-- [utest->req~behavioral-patterns~1]
theorem attachment_evaluations :
    checkFormula afterPrecedence attachmentOpeners true 0 0 = true ∧
    checkFormula afterPrecedence attachmentOpeners true 0 2 = false := by
  simp [checkFormula, afterPrecedence, expand, p, q, s, Formula.normalize, Formula.lower]
  decide

/-- The actual root assertion API supplies implicit always; initially limits
this same pattern to the root's birth. The lasso is admitted by trace_valid. -/
-- [utest->req~behavioral-patterns~1]
-- [utest->req~behavioral-properties~1]
theorem root_attachment_not_initially :
    (Properties.Constraint.root afterPrecedence.initially).Holds trace.unfold
      (.ofTotal (observation attachmentOpeners)) ∧
    ¬ (Properties.Constraint.root afterPrecedence).Holds trace.unfold
      (.ofTotal (observation attachmentOpeners)) := by
  constructor
  · rw [Properties.Constraint.root_holds _ _ _ trace_valid.root_live]
    intro t
    rw [Formula.total_agrees]
    intro birth
    have ht := (Trace.root_starts Examples.model trace.unfold trace_valid t).mp birth
    subst t
    exact (source_agrees _ _ true 0 0).mp attachment_evaluations.1
  · intro h
    have bad := (Properties.Constraint.root_holds _ _ _ trace_valid.root_live).mp h 2
    rw [Formula.total_agrees] at bad
    have yes := (source_agrees _ _ true 0 2).mpr bad
    exact Bool.noConfusion (attachment_evaluations.2.symm.trans yes)

end Clafer.Behavioral.PatternExamples
