module

public import Clafer.Behavioral.Lowering
public import Mathlib.Data.Fintype.Pigeonhole

/-!
# Exact finite-orbit temporal evaluation

A deterministic finite orbit has a representative of every future observation
among its first `card S` positions. This is a proved state-space bound, not a
user-selected time cutoff. It applies to the history-expanded lasso as well.
-/

@[expose] public section
namespace Clafer.Behavioral.Orbit
open Function
variable {S : Type} [Fintype S]

-- [proof->req~behavioral-finite-checker~1]
/-- A shortest visit cannot repeat a state: deleting the intervening cycle
would give an earlier visit to the same endpoint. -/
theorem representative (f : S → S) (s : S) (m : Nat) :
    ∃ k, k < Fintype.card S ∧ k ≤ m ∧ f^[k] s = f^[m] s := by
  classical
  have hex : ∃ k, f^[k] s = f^[m] s := ⟨m, rfl⟩
  let k := Nat.find hex
  have hk : f^[k] s = f^[m] s := Nat.find_spec hex
  have hkm : k ≤ m := Nat.find_min' hex rfl
  have inj : Function.Injective (fun i : Fin (k + 1) => f^[i.val] s) := by
    intro i j hij
    suffices h : ∀ a b : Nat, a ≤ k → b ≤ k →
        f^[a] s = f^[b] s → ¬ a < b by
      apply Fin.ext
      have h₁ := h i j (by omega) (by omega) hij
      have h₂ := h j i (by omega) (by omega) hij.symm
      omega
    intro a b ha hb hab hablt
    have heq : f^[a + (k - b)] s = f^[k] s := by
      rw [Nat.add_comm a, Function.iterate_add_apply, hab,
        ← Function.iterate_add_apply, Nat.sub_add_cancel hb]
    exact (Nat.find_min hex (show a + (k - b) < k by omega)) (heq.trans hk)
  have hc := Fintype.card_le_of_injective _ inj
  simp only [Fintype.card_fin] at hc
  exact ⟨k, by omega, hkm, hk⟩

-- [impl->req~behavioral-finite-checker~1]
def some (f : S → S) (p : S → Bool) (s : S) : Bool :=
  decide (∃ k : Fin (Fintype.card S), p (f^[k.val] s) = true)

def every (f : S → S) (p : S → Bool) (s : S) : Bool :=
  decide (∀ k : Fin (Fintype.card S), p (f^[k.val] s) = true)

def untilB (f : S → S) (a b : S → Bool) (s : S) : Bool :=
  decide (∃ k : Fin (Fintype.card S), b (f^[k.val] s) = true ∧
    ∀ i : Fin k.val, a (f^[i.val] s) = true)

-- [proof->req~behavioral-finite-checker~1]
theorem some_iff (f : S → S) (p : S → Bool) (s : S) :
    some f p s = true ↔ ∃ k, p (f^[k] s) = true := by
  simp only [some, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k.val, hk⟩
  · rintro ⟨m, hm⟩
    obtain ⟨k, hk, _, he⟩ := representative f s m
    exact ⟨⟨k, hk⟩, he.symm ▸ hm⟩

theorem every_iff (f : S → S) (p : S → Bool) (s : S) :
    every f p s = true ↔ ∀ k, p (f^[k] s) = true := by
  simp only [every, decide_eq_true_eq]
  constructor
  · intro h m
    obtain ⟨k, hk, _, he⟩ := representative f s m
    exact he ▸ h ⟨k, hk⟩
  · intro h k; exact h k.val

theorem until_iff (f : S → S) (a b : S → Bool) (s : S) :
    untilB f a b s = true ↔ ∃ k, b (f^[k] s) = true ∧
      ∀ i, i < k → a (f^[i] s) = true := by
  simp only [untilB, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hb, ha⟩
    exact ⟨k.val, hb, fun i hi => ha ⟨i, hi⟩⟩
  · rintro ⟨m, hb, ha⟩
    obtain ⟨k, hk, hkm, he⟩ := representative f s m
    exact ⟨⟨k, hk⟩, he.symm ▸ hb, fun i => ha i.val (Nat.lt_of_lt_of_le i.isLt hkm)⟩
end Clafer.Behavioral.Orbit
