module

public import Clafer.Behavioral.FiniteOrbit
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Finite machines for mixed past and future formulas

States include history, not just a lasso position. Cardinality certificates live
in proofs; an executable bound is composed arithmetically, without enumerating
product states. Future search stops when the reachable machine orbit repeats.
-/

@[expose] public section
namespace Clafer.Behavioral

-- [impl->req~behavioral-past-verification~1]
structure FiniteMachine (α : Type) where
  State : Type
  finiteState : Finite State
  eqState : DecidableEq State
  bound : Nat
  card_le : Nat.card State ≤ bound
  start : State
  step : State → State
  output : State → α

attribute [instance] FiniteMachine.finiteState FiniteMachine.eqState

namespace FiniteMachine
variable {α β : Type}

def state (M : FiniteMachine α) (t : Nat) : M.State := M.step^[t] M.start

def run (M : FiniteMachine α) (t : Nat) : α := M.output (M.state t)

@[simp] theorem state_zero (M : FiniteMachine α) : M.state 0 = M.start := rfl
@[simp] theorem state_succ (M : FiniteMachine α) (t : Nat) :
    M.state (t + 1) = M.step (M.state t) := Function.iterate_succ_apply' _ _ _

theorem state_add (M : FiniteMachine α) (t k : Nat) :
    M.state (t + k) = M.step^[k] (M.state t) := by
  rw [Nat.add_comm, state, Function.iterate_add_apply]
  rfl

def ofFinite {S : Type} [Fintype S] [DecidableEq S]
    (start : S) (step : S → S) (output : S → α) : FiniteMachine α where
  State := S
  finiteState := inferInstance
  eqState := inferInstance
  bound := Fintype.card S
  card_le := by simp [Nat.card_eq_fintype_card]
  start := start
  step := step
  output := output

def map (f : α → β) (M : FiniteMachine α) : FiniteMachine β where
  State := M.State
  finiteState := M.finiteState
  eqState := M.eqState
  bound := M.bound
  card_le := M.card_le
  start := M.start
  step := M.step
  output := f ∘ M.output

@[simp] theorem run_map (f : α → β) (M : FiniteMachine α) (t : Nat) :
    (M.map f).run t = f (M.run t) := rfl

def pair (M : FiniteMachine α) (N : FiniteMachine β) : FiniteMachine (α × β) where
  State := M.State × N.State
  finiteState := inferInstance
  eqState := inferInstance
  bound := M.bound * N.bound
  card_le := by rw [Nat.card_prod]; exact Nat.mul_le_mul M.card_le N.card_le
  start := (M.start, N.start)
  step s := (M.step s.1, N.step s.2)
  output s := (M.output s.1, N.output s.2)

@[simp] theorem state_pair (M : FiniteMachine α) (N : FiniteMachine β) (t : Nat) :
    (M.pair N).state t = (M.state t, N.state t) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [state_succ, ih]; rfl

@[simp] theorem run_pair (M : FiniteMachine α) (N : FiniteMachine β) (t : Nat) :
    (M.pair N).run t = (M.run t, N.run t) := by
  unfold run
  rw [state_pair]
  rfl

def family {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ι → FiniteMachine α) : FiniteMachine (ι → α) where
  State := (i : ι) → (M i).State
  finiteState := inferInstance
  eqState := inferInstance
  bound := ∏ i, (M i).bound
  card_le := by
    rw [Nat.card_pi]
    exact Finset.prod_le_prod (fun i _ => (M i).card_le)
  start i := (M i).start
  step s i := (M i).step (s i)
  output s i := (M i).output (s i)

@[simp] theorem state_family {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ι → FiniteMachine α) (t : Nat) (i : ι) :
    (family M).state t i = (M i).state t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [state_succ]; change (M i).step _ = _; rw [ih]

@[simp] theorem run_family {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ι → FiniteMachine α) (t : Nat) (i : ι) :
    (family M).run t i = (M i).run t := by
  change (M i).output ((family M).state t i) = _
  rw [state_family]
  rfl

def next (M : FiniteMachine α) : FiniteMachine α :=
  { M with output := M.output ∘ M.step }

@[simp] theorem run_next (M : FiniteMachine α) (t : Nat) :
    M.next.run t = M.run (t + 1) := by
  change M.output (M.step (M.state t)) = _
  rw [← state_succ]
  rfl

def previous (M : FiniteMachine Bool) : FiniteMachine Bool where
  State := M.State × Bool
  finiteState := inferInstance
  eqState := inferInstance
  bound := M.bound * 2
  card_le := by simp only [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]; exact Nat.mul_le_mul_right 2 M.card_le
  start := (M.start, false)
  step s := (M.step s.1, M.output s.1)
  output s := s.2

@[simp] theorem state_previous (M : FiniteMachine Bool) (t : Nat) :
    (M.previous.state t).1 = M.state t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [state_succ]; change M.step _ = _; rw [ih]

@[simp] theorem run_previous_zero (M : FiniteMachine Bool) : M.previous.run 0 = false := rfl

@[simp] theorem run_previous_succ (M : FiniteMachine Bool) (t : Nat) :
    M.previous.run (t + 1) = M.run t := by
  simp only [run, state_succ]
  change M.output (M.previous.state t).1 = _
  rw [state_previous]

-- [proof->req~behavioral-past-verification~1]
theorem previous_agrees (M : FiniteMachine Bool) (t : Nat) :
    M.previous.run t = true ↔ Temporal.previous (fun j => M.run j = true) t := by
  cases t <;> simp [Temporal.previous]

def since (M : FiniteMachine (Bool × Bool)) : FiniteMachine Bool where
  State := M.State × Bool
  finiteState := inferInstance
  eqState := inferInstance
  bound := M.bound * 2
  card_le := by simp only [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]; exact Nat.mul_le_mul_right 2 M.card_le
  start := (M.start, false)
  step s := (M.step s.1, (M.output s.1).2 || ((M.output s.1).1 && s.2))
  output s := (M.output s.1).2 || ((M.output s.1).1 && s.2)

@[simp] theorem state_since (M : FiniteMachine (Bool × Bool)) (t : Nat) :
    (M.since.state t).1 = M.state t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [state_succ]; change M.step _ = _; rw [ih]

@[simp] theorem run_since_zero (M : FiniteMachine (Bool × Bool)) :
    M.since.run 0 = (M.run 0).2 := by simp [run, since]

theorem run_since_succ (M : FiniteMachine (Bool × Bool)) (t : Nat) :
    M.since.run (t + 1) = ((M.run (t + 1)).2 || ((M.run (t + 1)).1 && M.since.run t)) := by
  have current : M.since.run (t + 1) =
      ((M.run (t + 1)).2 || ((M.run (t + 1)).1 && (M.since.state (t + 1)).2)) := by
    change ((M.output (M.since.state (t + 1)).1).2 ||
      ((M.output (M.since.state (t + 1)).1).1 && _)) = _
    rw [state_since]
    rfl
  have cache : (M.since.state (t + 1)).2 = M.since.run t := by
    rw [state_succ]
    rfl
  rw [current, cache]

-- [proof->req~behavioral-past-verification~1]
theorem since_agrees (M : FiniteMachine (Bool × Bool)) (t : Nat) :
    M.since.run t = true ↔ Temporal.since (fun j => (M.run j).1 = true)
      (fun j => (M.run j).2 = true) t := by
  induction t with
  | zero => simp
  | succ t ih => rw [run_since_succ, Temporal.since_succ]; simp only [Bool.or_eq_true, Bool.and_eq_true, ih]

def searchUntil (M : FiniteMachine α) (a b : α → Bool) : FiniteMachine Bool :=
  { M with output := FiniteOrbit.untilB M.bound M.step (a ∘ M.output) (b ∘ M.output) }

-- [proof->req~behavioral-past-verification~1]
theorem searchUntil_agrees (M : FiniteMachine α) (a b : α → Bool) (t : Nat) :
    (M.searchUntil a b).run t = true ↔ ∃ k, b (M.run (t + k)) = true ∧
      ∀ i, i < k → a (M.run (t + i)) = true := by
  change FiniteOrbit.untilB M.bound M.step (a ∘ M.output) (b ∘ M.output) (M.state t) = true ↔ _
  rw [FiniteOrbit.until_iff _ M.card_le]
  simp only [FiniteOrbit.Until, Function.comp_apply, ← state_add, run]

def eventually (M : FiniteMachine Bool) : FiniteMachine Bool := M.searchUntil (fun _ => true) id

theorem eventually_agrees (M : FiniteMachine Bool) (t : Nat) :
    M.eventually.run t = true ↔ ∃ k, M.run (t + k) = true := by
  simp [eventually, searchUntil_agrees]

def always (M : FiniteMachine Bool) : FiniteMachine Bool :=
  (M.searchUntil (fun _ => true) Bool.not).map Bool.not

theorem always_agrees (M : FiniteMachine Bool) (t : Nat) :
    M.always.run t = true ↔ ∀ k, M.run (t + k) = true := by
  have h := not_congr (M.searchUntil_agrees (fun _ => true) Bool.not t)
  simpa [always] using h

end FiniteMachine
end Clafer.Behavioral
