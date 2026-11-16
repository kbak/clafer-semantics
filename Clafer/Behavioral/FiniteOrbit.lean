module

public import Clafer.Behavioral.Orbit
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Reachable-orbit search with cycle detection

The cardinality bound is proved, while execution stops at the first repeated
state. The state space itself is never enumerated. This supports products of
history monitors without turning their cardinality into a practical time cutoff.
-/

@[expose] public section
namespace Clafer.Behavioral.FiniteOrbit
variable {S : Type} [DecidableEq S]

/-- Ordinary strong until along a deterministic orbit. -/
def Until (f : S → S) (a b : S → Bool) (s : S) : Prop :=
  ∃ k, b (f^[k] s) = true ∧ ∀ i, i < k → a (f^[i] s) = true

omit [DecidableEq S] in
theorem until_step (f : S → S) (a b : S → Bool) (s : S) :
    Until f a b s ↔ b s = true ∨ (a s = true ∧ Until f a b (f s)) := by
  constructor
  · rintro ⟨k, hb, ha⟩
    cases k with
    | zero => exact Or.inl hb
    | succ k =>
      refine Or.inr ⟨ha 0 (by omega), k, ?_, ?_⟩
      · simpa only [Function.iterate_succ_apply] using hb
      · intro i hi
        simpa only [Function.iterate_succ_apply] using ha (i + 1) (by omega)
  · rintro (hb | ⟨ha, k, hb, rest⟩)
    · exact ⟨0, hb, by omega⟩
    · refine ⟨k + 1, ?_, ?_⟩
      · simpa only [Function.iterate_succ_apply] using hb
      · intro i hi
        cases i with
        | zero => exact ha
        | succ i => simpa only [Function.iterate_succ_apply] using rest i (by omega)

-- [impl->req~behavioral-past-verification~1]
def scan (f : S → S) (a b : S → Bool) : Nat → Finset S → S → Bool :=
  Nat.rec (fun _ _ => false) (fun _ next seen s =>
    if s ∈ seen then false
    else if b s then true
    else if a s then next (insert s seen) (f s) else false)

omit [DecidableEq S] in
private theorem no_goal_of_closed (f : S → S) (b : S → Bool) (seen : Finset S)
    (closed : ∀ x ∈ seen, f x ∈ seen) (noGoal : ∀ x ∈ seen, b x = false)
    (s : S) (hs : s ∈ seen) : ∀ k, b (f^[k] s) = false := by
  have live : ∀ k, f^[k] s ∈ seen := by
    intro k
    induction k with
    | zero => exact hs
    | succ k ih => simpa only [Function.iterate_succ_apply'] using closed _ ih
  exact fun k => noGoal _ (live k)

-- [proof->req~behavioral-past-verification~1]
theorem scan_agrees [Finite S] (f : S → S) (a b : S → Bool) (fuel : Nat)
    (seen : Finset S) (s : S)
    (closed : ∀ x ∈ seen, f x ∈ seen ∨ f x = s)
    (noGoal : ∀ x ∈ seen, b x = false)
    (budget : Nat.card S ≤ seen.card + fuel) :
    scan f a b fuel seen s = true ↔ Until f a b s := by
  classical
  let _ := Fintype.ofFinite S
  have repeated (seen : Finset S) (s : S)
      (closed : ∀ x ∈ seen, f x ∈ seen ∨ f x = s)
      (noGoal : ∀ x ∈ seen, b x = false) (hs : s ∈ seen) : ¬ Until f a b s := by
    have hc : ∀ x ∈ seen, f x ∈ seen := fun x hx =>
      (closed x hx).elim id (fun eq => eq.symm ▸ hs)
    rintro ⟨k, hb, _⟩
    have hn := no_goal_of_closed f b seen hc noGoal s hs k
    simp [hn] at hb
  induction fuel generalizing seen s with
  | zero =>
    have hs : s ∈ seen := by
      by_contra h
      have hcard := (insert s seen).card_le_univ
      simp only [Finset.card_insert_of_notMem h, ← Nat.card_eq_fintype_card] at hcard
      omega
    change false = true ↔ Until f a b s
    simp only [Bool.false_eq_true, false_iff]
    exact repeated seen s closed noGoal hs
  | succ fuel ih =>
    by_cases hs : s ∈ seen
    · simp only [scan, ite_eq_left hs, Bool.false_eq_true, false_iff]
      exact repeated seen s closed noGoal hs
    · have stepClosed : ∀ x ∈ insert s seen, f x ∈ insert s seen ∨ f x = f s := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Or.inr rfl
        · exact Or.inl ((closed x hx).elim (fun h => Finset.mem_insert_of_mem h)
            (fun h => h.symm ▸ Finset.mem_insert_self _ _))
      by_cases hb : b s = true
      · simp only [scan, ite_eq_right hs, hb, ↓reduceIte, true_iff]
        exact (until_step f a b s).mpr (Or.inl hb)
      · have hb' : b s = false := by simpa using hb
        have stepNoGoal : ∀ x ∈ insert s seen, b x = false := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hb'
          · exact noGoal x hx
        have stepBudget : Nat.card S ≤ (insert s seen).card + fuel := by
          rw [Finset.card_insert_of_notMem hs]
          omega
        by_cases ha : a s = true
        · simp only [scan, ite_eq_right hs, hb', ha, ↓reduceIte]
          exact (ih _ _ stepClosed stepNoGoal stepBudget).trans (by
            rw [until_step f a b s]
            simp only [hb', ha, Bool.false_eq_true, false_or, true_and])
        · have ha' : a s = false := by simpa using ha
          simp only [scan, ite_eq_right hs, hb', ha', ↓reduceIte, Bool.false_eq_true, false_iff]
          rw [until_step]
          simp [hb', ha']

/-- The supplied bound is independently proved; it is not an input horizon. -/
def untilB (bound : Nat) (f : S → S) (a b : S → Bool) (s : S) : Bool :=
  scan f a b bound ∅ s

theorem until_iff [Finite S] (bound : Nat) (h : Nat.card S ≤ bound)
    (f : S → S) (a b : S → Bool) (s : S) :
    untilB bound f a b s = true ↔ Until f a b s :=
  scan_agrees f a b bound ∅ s (by simp) (by simp) (by simpa using h)

end Clafer.Behavioral.FiniteOrbit
