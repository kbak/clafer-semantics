module

public import Clafer.Behavioral.InitializerPast
public import Clafer.Behavioral.Lasso

/-! # Past-time boundary witnesses

These distinguish parent history from context history, reject unbounded history
across rebirth, and expose the finite-history and strict-definedness obligations
of the subsequent formula/core integration. Signal witnesses do not assert a
complete structural model or a source-parser/target-compiler result.
-/

@[expose] public section
namespace Clafer.Behavioral.PastExamples

-- [utest->req~behavioral-past-foundation~1]
theorem strong_previous_at_zero : ¬ Lifetime.previous (fun _ => True) (fun _ => True) 0 := by
  simp [Lifetime.previous]

theorem weak_previous_at_zero : Lifetime.weakPrevious (fun _ => True) (fun _ => False) 0 := by
  trivial

theorem once_includes_now : Lifetime.once (fun _ => True) (fun j => j = 0) 0 := by
  simp

theorem historically_includes_now : ¬ Lifetime.historically (fun _ => True) (fun j => j ≠ 0) 0 := by
  simp [Temporal.historically]

theorem since_includes_now : Lifetime.since (fun _ => True) (fun _ => False) (fun j => j = 0) 0 := by
  simp

theorem triggered_includes_now :
    ¬ Lifetime.triggered (fun _ => True) (fun _ => True) (fun _ => False) 0 := by
  rw [Lifetime.triggered_dual, Lifetime.since_zero]
  simp

/-- A child born at state two can see a parent's event at state zero. -/
theorem parent_history_before_child_birth :
    Lifetime.once (fun _ => True) (fun j => j = 0) 2 ∧
      ¬ Lifetime.once (fun j => 2 ≤ j) (fun j => j = 0) 2 := by
  constructor
  · exact ⟨0, by decide, fun _ _ _ => trivial, rfl⟩
  · rintro ⟨j, _, live, rfl⟩
    have impossible := live 0 le_rfl (by decide)
    omega

theorem previous_resets_at_parent_birth :
    Temporal.previous (fun j => j = 1) 2 ∧
      ¬ Lifetime.previous (fun j => j ≠ 1) (fun j => j = 1) 2 := by
  simp [Temporal.previous, Lifetime.previous]

theorem once_forgets_old_lifetime :
    Temporal.once (fun j => j = 0) 2 ∧
      ¬ Lifetime.once (fun j => j ≠ 1) (fun j => j = 0) 2 := by
  constructor
  · exact ⟨0, by decide, rfl⟩
  · rw [Lifetime.once_reset (P := fun j => j ≠ 1) (t := 1) (by simp)]
    simp

theorem since_forgets_old_lifetime :
    Temporal.since (fun _ => True) (fun j => j = 0) 2 ∧
      ¬ Lifetime.since (fun j => j ≠ 1) (fun _ => True) (fun j => j = 0) 2 := by
  constructor
  · exact ⟨0, by decide, rfl, fun _ _ _ => trivial⟩
  · rw [Lifetime.since_reset (P := fun j => j ≠ 1) (t := 1) (by simp)]
    simp

theorem historically_forgets_old_lifetime :
    Lifetime.historically (fun j => j ≠ 1) (fun j => j ≠ 0) 2 := by
  rw [Lifetime.historically_dual,
    Lifetime.once_reset (P := fun j => j ≠ 1) (t := 1) (by simp)]
  simp

theorem triggered_forgets_old_lifetime :
    Lifetime.triggered (fun j => j ≠ 1) (fun _ => False) (fun j => j ≠ 0) 2 := by
  rw [Lifetime.triggered_dual,
    Lifetime.since_reset (P := fun j => j ≠ 1) (t := 1) (by simp)]
  simp

/-- The old predecessor-bearing clock has the same state on the first and
second repeat, while two nested previous operators distinguish them. -/
def singleState : Lasso Unit 1 0 where
  identities := ⟨0, fun _ => (), fun _ => none⟩
  loop := 0
  live _ _ := true
  deref _ _ _ _ := false

theorem equal_clock_different_past :
    singleState.clock 1 = singleState.clock 2 ∧
      ¬ Temporal.previous (Temporal.previous (fun _ => True)) 1 ∧
      Temporal.previous (Temporal.previous (fun _ => True)) 2 := by
  change singleState.clock 1 = singleState.clock 2 ∧ ¬ False ∧ True
  exact ⟨by decide, by simp, trivial⟩

/-- A permanent root and a child live at zero, absent at one, and live thereafter.
This fixture supplies ownership/birth data, not a complete structural model. -/
def rebirthTrace : Trace Unit Bool where
  identities := ⟨false, fun _ => (), fun x => if x then some false else none⟩
  live t := {x | x = false ∨ (x = true ∧ (t = 0 ∨ 2 ≤ t))}
  deref _ _ _ _ := False

def rebirthHeads (t : Nat) : Set Bool := {x | x = true ∧ (t = 0 ∨ 2 ≤ t)}

def birthValue (t : Nat) (_ : Bool) : Option (Set Bool) :=
  if t = 0 ∨ t = 2 then some {true} else none

theorem rebirth_membership (t : Nat) (x : Bool) :
    x ∈ rebirthHeads t ↔ x = true ∧ x ∈ rebirthTrace.live t := by
  cases x <;> simp [rebirthHeads, rebirthTrace]

-- [utest->req~behavioral-initializer-birth-test~1]
theorem rebirth_equations_allow_later_missing_rhs :
    Initializers.Past.Equations rebirthHeads (fun _ _ => True) (fun _ _ => true) birthValue := by
  apply (Initializers.Past.equations_agree rebirthTrace rebirthHeads (fun x => x = true)
    (fun _ _ => True) rebirth_membership (fun _ _ _ => trivial) _ _).mpr
  intro t x hx birth
  have identity : x = true := hx.1
  subst x
  have time : t = 0 ∨ t = 2 := by
    cases t with
    | zero => exact Or.inl rfl
    | succ k =>
      have boundary := (rebirthTrace.starts_succ k true).mp birth
      have current : k + 1 = 0 ∨ 2 ≤ k + 1 := by simpa [rebirthTrace] using boundary.1
      have absent : ¬ (k = 0 ∨ 2 ≤ k) := by simpa [rebirthTrace] using boundary.2
      omega
  simp [birthValue, time]

theorem later_rhs_missing : birthValue 3 true = none := by simp [birthValue]

/-- A changing filter can acquire a live object without that object being born. -/
theorem filtered_membership_is_not_birth :
    ¬ rebirthTrace.Starts (3 + 1) true ∧
      ¬ Lifetime.previous (fun _ => True) (fun t => t = 4) (3 + 1) := by
  simp [Trace.starts_succ, rebirthTrace, Lifetime.previous]

/-- Undefinedness at an inactive birth is allowed by the declaration guard. -/
theorem inactive_equation_permits_undefined (target : Set Nat) :
    False → (none : Option (Set Nat)) = some target := False.elim

/-- In contrast, strict implication rejects an undefined RHS under a false guard. -/
theorem inactive_strict_implication_rejected {C : Type} {U : Type u}
    (τ : Trace C U) (ρ : Environment U 0) (t : Nat) :
    ¬ (Formula.implies (.not .truth) (.atom ()) : Formula (fun _ => Unit) (fun _ => Empty) 0).Satisfies
      τ { atom := fun _ _ _ => none, domain := fun d => nomatch d } true ρ t := by
  simp [Formula.Satisfies, Formula.Defined]

end Clafer.Behavioral.PastExamples
