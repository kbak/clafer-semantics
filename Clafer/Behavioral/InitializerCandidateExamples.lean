module

public import Clafer.Behavioral.InitializerCandidate
public import Clafer.Behavioral.Examples
public import Clafer.Behavioral.PrimitiveExpressionExamples

/-! Candidate boundary witnesses for #169/#170. The clock witnesses reuse
structurally admitted snapshots; they do not assert a frontend classification
of inherited or bag declarations. The arithmetic witness uses the actual partial
primitive evaluator. Behavioral §5 Definitions 3–5, §6.1, T7/T9. -/

@[expose] public section
namespace Clafer.Behavioral.Initializers.CandidateExamples
open Candidate

/-- Reordering snapshots preserves structural validity, without making any
claim about preservation of temporal formulas. -/
def sample (f : Nat → Nat) : Trace (Fin 4) (Fin 8) where
  identities := Examples.pool
  live t := Examples.cycling.live (f t)
  deref t := Examples.cycling.deref (f t)

theorem sample_valid (f : Nat → Nat) : (sample f).Valid Examples.model where
  identities := Examples.cycling_valid.identities
  root_live t := Examples.cycling_valid.root_live (f t)
  parent_live t := Examples.cycling_valid.parent_live (f t)
  states t := by
    have h := Examples.cycling_valid.states (f t)
    exact ⟨h.typed, h.root_head, h.root_separate, h.inherits, h.abstracts,
      h.parents, h.references, h.keys, h.multiplicities, h.groups, h.disjoint⟩

/-- Parent 1 stays alive; reference heads 3 and 4 first appear at time 1,
both pointing to 6. The first snapshot has no reference heads. -/
def delayed : Trace (Fin 4) (Fin 8) := sample (fun t => if t = 0 then 1 else 3)

private theorem delayed_live (t : Nat) :
    1 ∈ delayed.live t ∧ (3 ∈ delayed.live t ↔ t ≠ 0) := by
  by_cases h : t = 0 <;>
    simp [delayed, sample, Examples.cycling, Examples.phaseLive, h]

private theorem parent_birth (t : Nat) : delayed.Starts t 1 ↔ t = 0 := by
  constructor
  · rintro ⟨_, h | ⟨k, _, absent⟩⟩
    · exact h
    · exact (absent (delayed_live k).1).elim
  · rintro rfl
    exact (delayed.starts_zero 1).mpr (delayed_live 0).1

private theorem child_birth (t : Nat) : delayed.Starts t 3 ↔ t = 1 := by
  cases t with
  | zero => simp [Trace.Starts, (delayed_live 0).2]
  | succ t =>
    rw [delayed.starts_succ]
    simp [(delayed_live (t + 1)).2, (delayed_live t).2]

def delayedHeads (t : Nat) (_ : Fin 8) : Set (Fin 8) :=
  if t = 0 then ∅ else {3, 4}

def delayedTargets (t : Nat) (_ : Fin 8) : Set (Fin 8) :=
  if t = 0 then ∅ else {6}

/-- These are the complete child-head and target observations under parent 1,
not arbitrarily chosen empty guards. Occurrence identity remains in the heads. -/
theorem delayed_observations (t : Nat) :
    delayedHeads t 1 = {x | delayed.ParentAt t 1 x ∧ (x = 3 ∨ x = 4)} ∧
    delayedTargets t 1 = {y | ∃ x ∈ delayedHeads t 1, delayed.deref t 2 x y} := by
  by_cases h : t = 0
  · subst t
    constructor <;> ext x <;>
      simp [delayedHeads, delayedTargets, delayed, sample, Examples.cycling,
        Examples.phaseLive, Examples.phaseDeref, Trace.ParentAt, Examples.pool]
    fin_cases x <;> decide
  · constructor
    · ext x
      simp [delayedHeads, delayed, sample, Examples.cycling, Examples.phaseLive,
        Trace.ParentAt, Examples.pool, h]
      fin_cases x <;> decide
    · ext y
      simp [delayedHeads, delayedTargets, delayed, sample, Examples.cycling,
        Examples.phaseDeref, h]

-- [utest->req~behavioral-structural-compatibility~1]
/-- Empty at parent birth permits an undefined RHS, including after heads are
added later in the same parent lifetime. No extra birth obligation is inserted. -/
theorem empty_collection_later_additions :
    delayed.Valid Examples.model ∧
    CollectionBirths delayed (fun _ => {1}) delayedHeads delayedTargets (fun _ _ => none) ∧
    ¬ EveryLive delayed (fun _ => {1}) delayedHeads delayedTargets (fun _ _ => none) := by
  refine ⟨sample_valid _, ?_, ?_⟩
  · intro t p hp birth
    have hp' : p = 1 := hp
    subst p
    have ht := (parent_birth t).mp birth
    subst t
    exact empty_guard _ _
  · intro h
    have bad := h 1 1 rfl (delayed_live 1).1
    have present : (delayedHeads 1 1).Nonempty := ⟨3, by simp [delayedHeads]⟩
    cases bad present

/-- The same late birth succeeds with a defined matching RHS at birth, even
though it was undefined beforehand. Per-instance and collection timing differ. -/
theorem late_single_birth :
    SingleBirths delayed (fun _ => {3}) (fun _ _ => 6)
      (fun t _ => if t = 0 then none else some {6}) ∧
    ¬ SingleBirths delayed (fun _ => {3}) (fun _ _ => 6) (fun _ _ => none) := by
  constructor
  · intro t x hx birth
    have hx' : x = 3 := hx
    subst x
    have ht := (child_birth t).mp birth
    subst t
    rfl
  · intro h
    have bad := h 1 3 rfl ((child_birth 1).mpr rfl)
    cases bad

theorem never_present_single :
    (sample (fun _ => 1)).Valid Examples.model ∧
    SingleBirths (sample (fun _ => 1)) (fun _ => {3})
      (fun _ _ => 6) (fun _ _ => none) := by
  refine ⟨sample_valid _, ?_⟩
  intro t x hx birth
  have hx' : x = 3 := hx
  subst x
  have absent : (3 : Fin 8) ∉ (sample (fun _ => 1)).live t := by
    simp [sample, Examples.cycling, Examples.phaseLive]
  exact (absent birth.1).elim

/-- A wrong value at a new lifetime is rejected; the earlier correct value
cannot discharge the new obligation. -/
theorem rebirth_requires_fresh_value :
    ¬ SingleBirths Examples.cycling (fun _ => {3})
      (fun t _ => if t % 4 = 0 then 5 else 6) (fun _ _ => some {5}) := by
  intro h
  have birth : Examples.cycling.Starts 3 3 :=
    (Examples.cycling.starts_succ 2 3).mpr (by
      simp [Examples.cycling, Examples.phaseLive])
  have bad := h 3 3 rfl birth
  have : (5 : Fin 8) = 6 := Set.singleton_injective (Option.some.inj bad)
  contradiction

theorem parent_rebirth_checks_collection :
    ¬ CollectionBirths Examples.cycling (fun _ => {1})
      (fun t _ => if t % 4 = 0 ∨ t % 4 = 3 then {3, 4} else ∅)
      (fun t _ => if t % 4 = 0 then {5} else {6}) (fun _ _ => some {5}) := by
  intro h
  have birth : Examples.cycling.Starts 3 1 :=
    (Examples.cycling.starts_succ 2 1).mpr (by
      simp [Examples.cycling, Examples.phaseLive])
  have bad := h 3 1 rfl birth ⟨3, by simp⟩
  have : (5 : Fin 8) = 6 := Set.singleton_injective (Option.some.inj bad)
  contradiction

-- [utest->req~behavioral-reference-atoms~1]
theorem empty_and_undefined_distinct :
    Guarded (∅ : Set Nat) ∅ none ∧ Guarded (∅ : Set Nat) ∅ (some ∅) ∧
    ¬ Guarded ({1} : Set Nat) {3} none ∧
    ¬ Guarded ({1} : Set Nat) {3} (some ∅) ∧
    Guarded ({1} : Set Nat) {3} (some {3}) ∧
    ¬ Guarded ({1} : Set Nat) {3} (some {4}) := by
  simp [Guarded]

open PrimitiveExpressionExamples in
theorem undefined_after_birth_allowed :
    Structural.Valid model trace ∧
    SingleBirths trace (fun _ => {Sum.inl 1})
      (fun t _ => Sum.inr (if t = 0 then 3 else 5))
      (fun t _ => if t = 0 then some {Sum.inr 3} else none) ∧
    ¬ EveryLive trace (fun _ => {Sum.inl 1}) (fun _ x => {x})
      (fun t _ => {Sum.inr (if t = 0 then 3 else 5)})
      (fun t _ => if t = 0 then some {Sum.inr 3} else none) := by
  refine ⟨valid, ?_, ?_⟩
  · intro t x _ birth
    have ht := ((starts_constant_live trace (fun _ => rfl) t x).mp birth).2
    subst t
    rfl
  · intro h
    have bad := h 1 (.inl 1) rfl (Set.mem_univ _) (Set.singleton_nonempty _)
    cases bad

open PrimitiveExpressionExamples in
/-- Actual partial arithmetic distinguishes the new guard from the old
strict implication on an admitted trace. This is an expression-level witness. -/
theorem strict_guard_counterexample :
    let zeroDiv : CollectionExpr (Fin 3) 0 :=
      .integer (.binary .divide (.literal 6) (.literal 0))
    Structural.Valid model trace ∧
    Guarded ∅ ∅ (PrimitiveExpression.collection model.toEffectiveCore
      (Structural.observed model trace) integers (.closed (.inl 0)) 0 zeroDiv) ∧
    ¬ (Initializers.constant (.set .empty) (.set .empty) zeroDiv).Satisfies trace
      (.primitives model trace integers) true (.closed (.inl 0)) 0 := by
  dsimp only
  refine ⟨valid, empty_guard _ _, ?_⟩
  apply old_constant_rejects_undefined
  simp [PrimitiveExpression.collection, PrimitiveExpression.integerValue,
    Arithmetic.Binary.eval, Arithmetic.Binary.apply]

end Clafer.Behavioral.Initializers.CandidateExamples
