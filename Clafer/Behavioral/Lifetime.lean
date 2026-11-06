module

public import Clafer.Behavioral.Trace

/-!
# Parent-bounded temporal operators

Behavioral paper §5 Definition 4 and §6.1, changed by pinned erratum T2.
Source interval meanings are separate from the ordinary infinite-time operators
used in lowering. A gap terminates an interval even if the identity reappears.
-/

@[expose] public section
namespace Clafer.Behavioral

abbrev Signal := Nat → Prop

namespace Temporal
def next (a : Signal) (t : Nat) : Prop := a (t + 1)
def eventually (a : Signal) (t : Nat) : Prop := ∃ j, t ≤ j ∧ a j
def always (a : Signal) (t : Nat) : Prop := ∀ j, t ≤ j → a j
def strongUntil (a b : Signal) (t : Nat) : Prop :=
  ∃ j, t ≤ j ∧ b j ∧ ∀ k, t ≤ k → k < j → a k
def weakUntil (a b : Signal) (t : Nat) : Prop := always a t ∨ strongUntil a b t
end Temporal

namespace Lifetime
-- [impl->req~behavioral-formula-denotation~1]
/-- Inclusive uninterrupted portion of the *current* parent lifetime. -/
def Through (P : Signal) (t j : Nat) : Prop := ∀ k, t ≤ k → k ≤ j → P k

def next (P a : Signal) (t : Nat) : Prop := P (t + 1) → a (t + 1)

/-- Either the parent ends, or the body occurs within its uninterrupted life. -/
def eventually (P a : Signal) (t : Nat) : Prop :=
  (∃ j, t ≤ j ∧ ¬ P j) ∨ ∃ j, t ≤ j ∧ Through P t j ∧ a j

def always (P a : Signal) (t : Nat) : Prop :=
  ∀ j, t ≤ j → Through P t j → a j

def strongUntil (P a b : Signal) (t : Nat) : Prop :=
  ∃ j, t ≤ j ∧ (¬ P j ∨ b j) ∧ ∀ k, t ≤ k → k < j → P k ∧ a k

def weakUntil (P a b : Signal) (t : Nat) : Prop := always P a t ∨ strongUntil P a b t

-- [proof->req~behavioral-formula-denotation~1]
theorem next_lower (P a : Signal) (t : Nat) :
    next P a t ↔ Temporal.next (fun j => ¬ P j ∨ a j) t := by
  classical
  simp [next, Temporal.next, imp_iff_not_or]

theorem eventually_lower (P a : Signal) (t : Nat) :
    eventually P a t ↔ Temporal.eventually (fun j => ¬ P j ∨ a j) t := by
  classical
  constructor
  · rintro (⟨j, hj, hp⟩ | ⟨j, hj, _, ha⟩)
    · exact ⟨j, hj, Or.inl hp⟩
    · exact ⟨j, hj, Or.inr ha⟩
  · rintro ⟨j, hj, hp | ha⟩
    · exact Or.inl ⟨j, hj, hp⟩
    · by_cases h : Through P t j
      · exact Or.inr ⟨j, hj, h, ha⟩
      · simp only [Through, not_forall] at h
        obtain ⟨k, hk, _, hp⟩ := h
        exact Or.inl ⟨k, hk, hp⟩

/-- Weak until stops at the first absent state; it does not restart later. -/
theorem always_lower (P a : Signal) (t : Nat) :
    always P a t ↔ Temporal.weakUntil (fun j => P j ∧ a j) (fun j => ¬ P j) t := by
  classical
  constructor
  · intro h
    by_cases hp : ∀ j, t ≤ j → P j
    · exact Or.inl (fun j hj => ⟨hp j hj, h j hj (fun k hk _ => hp k hk)⟩)
    · have hex : ∃ j, t ≤ j ∧ ¬ P j := by simpa using hp
      let j := Nat.find hex
      have hj := Nat.find_spec hex
      refine Or.inr ⟨j, hj.1, hj.2, ?_⟩
      intro k hk hkj
      have before : ∀ l, t ≤ l → l < j → P l := by
        intro l hl hlj
        by_contra hn
        exact (Nat.find_min hex hlj) ⟨hl, hn⟩
      exact ⟨before k hk hkj, h k hk (fun l hl hlk => before l hl (lt_of_le_of_lt hlk hkj))⟩
  · rintro (h | ⟨j, hj, hp, h⟩) k hk hs
    · exact (h k hk).2
    · have hkj : k < j := by
        by_contra hn
        exact hp (hs j hj (Nat.le_of_not_gt hn))
      exact (h k hk hkj).2

theorem until_lower (P a b : Signal) (t : Nat) :
    strongUntil P a b t ↔ Temporal.strongUntil (fun j => P j ∧ a j) (fun j => ¬ P j ∨ b j) t :=
  Iff.rfl

-- [proof->req~behavioral-formula-denotation~1]
/-- Once absent at `d`, no later reappearance can extend this interval. -/
theorem not_through_after_end {P : Signal} {t d j : Nat}
    (htd : t ≤ d) (hdj : d ≤ j) (hd : ¬ P d) : ¬ Through P t j :=
  fun h => hd (h d htd hdj)

theorem eventually_cancel {P a : Signal} {t d : Nat}
    (htd : t ≤ d) (hd : ¬ P d) : eventually P a t := Or.inl ⟨d, htd, hd⟩

theorem always_before_end {P a : Signal} {t d : Nat}
    (htd : t ≤ d) (hd : ¬ P d) :
    always P a t ↔ ∀ j, t ≤ j → j < d → Through P t j → a j := by
  constructor
  · exact fun h j hj _ hs => h j hj hs
  · intro h j hj hs
    have hjd : j < d := by
      by_contra hn
      exact not_through_after_end htd (Nat.le_of_not_gt hn) hd hs
    exact h j hj hjd hs

theorem until_witness_before_end {P a b : Signal} {t d : Nat}
    (htd : t ≤ d) (hd : ¬ P d) : strongUntil P a b t ↔
      ∃ j, t ≤ j ∧ j ≤ d ∧ (¬ P j ∨ b j) ∧
        ∀ k, t ≤ k → k < j → P k ∧ a k := by
  constructor
  · rintro ⟨j, hj, hb, h⟩
    have hjd : j ≤ d := by
      by_contra hn
      exact hd (h d htd (Nat.lt_of_not_ge hn)).1
    exact ⟨j, hj, hjd, hb, h⟩
  · rintro ⟨j, hj, _, hb, h⟩
    exact ⟨j, hj, hb, h⟩

-- [proof->req~behavioral-signed-normalization~1]
/-- Persistent-parent assumptions restore the classical F/G contradiction. -/
theorem persistent_eventually_not_always_not {P a : Signal} {t : Nat}
    (hp : ∀ j, t ≤ j → P j) :
    eventually P a t → ¬ always P (fun j => ¬ a j) t := by
  rintro (⟨j, hj, hn⟩ | ⟨j, hj, _, ha⟩) hg
  · exact hn (hp j hj)
  · exact hg j hj (fun k hk _ => hp k hk) ha

@[simp] theorem next_true (a : Signal) (t : Nat) :
    next (fun _ => True) a t ↔ Temporal.next a t := by simp [next, Temporal.next]
@[simp] theorem eventually_true (a : Signal) (t : Nat) :
    eventually (fun _ => True) a t ↔ Temporal.eventually a t := by
  simp [eventually, Through, Temporal.eventually]
@[simp] theorem always_true (a : Signal) (t : Nat) :
    always (fun _ => True) a t ↔ Temporal.always a t := by simp [always, Through, Temporal.always]
@[simp] theorem until_true (a b : Signal) (t : Nat) :
    strongUntil (fun _ => True) a b t ↔ Temporal.strongUntil a b t := by simp [strongUntil, Temporal.strongUntil]
@[simp] theorem weakUntil_true (a b : Signal) (t : Nat) :
    weakUntil (fun _ => True) a b t ↔ Temporal.weakUntil a b t := by
  simp [weakUntil, Temporal.weakUntil]
end Lifetime
end Clafer.Behavioral
