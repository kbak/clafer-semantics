module

public import Clafer.Behavioral.Lifetime

/-! # Past operators within the parent's current lifetime

Extension of behavioral §5 Definitions 3–5 / §6.1, selected in issue #187.
The interval definitions are independent of the guarded ordinary-past encoding.
Supplementary compiler source: gsdlab/clafer@186d8e0a350e4c8895b1c489eb587fa3a1bc2b61,
issue #127. The guard is the original attachment's parent presence, not the
quantified object's presence. An intervening absent state separates lifetimes.
-/

@[expose] public section
namespace Clafer.Behavioral

namespace Temporal

-- [impl->req~behavioral-past-foundation~1]
def previous (a : Signal) : Nat → Prop
  | 0 => False
  | t + 1 => a t

def weakPrevious (a : Signal) : Nat → Prop
  | 0 => True
  | t + 1 => a t

def once (a : Signal) (t : Nat) : Prop := ∃ j, j ≤ t ∧ a j
def historically (a : Signal) (t : Nat) : Prop := ∀ j, j ≤ t → a j
def since (a b : Signal) (t : Nat) : Prop :=
  ∃ j, j ≤ t ∧ b j ∧ ∀ k, j < k → k ≤ t → a k
def triggered (a b : Signal) (t : Nat) : Prop :=
  ∀ j, j ≤ t → (∀ k, j < k → k ≤ t → ¬ a k) → b j

-- [proof->req~behavioral-past-foundation~1]
theorem triggered_dual (a b : Signal) (t : Nat) :
    triggered a b t ↔ ¬ since (fun j => ¬ a j) (fun j => ¬ b j) t := by
  classical
  constructor
  · rintro h ⟨j, hj, hb, ha⟩
    exact hb (h j hj ha)
  · intro h j hj ha
    by_contra hb
    exact h ⟨j, hj, hb, ha⟩

end Temporal

namespace Lifetime

-- [impl->req~behavioral-past-foundation~1]
/-- Strong previous has no witness at time zero or immediately after a gap.
The current-state presence premise belongs to attachment, not this operator. -/
def previous (P a : Signal) : Nat → Prop
  | 0 => False
  | t + 1 => P t ∧ a t

def weakPrevious (P a : Signal) : Nat → Prop
  | 0 => True
  | t + 1 => P t → a t

def once (P a : Signal) (t : Nat) : Prop :=
  ∃ j, j ≤ t ∧ Through P j t ∧ a j

def historically (P a : Signal) (t : Nat) : Prop :=
  ∀ j, j ≤ t → Through P j t → a j

def since (P a b : Signal) (t : Nat) : Prop :=
  ∃ j, j ≤ t ∧ Through P j t ∧ b j ∧ ∀ k, j < k → k ≤ t → a k

def triggered (P a b : Signal) (t : Nat) : Prop :=
  ∀ j, j ≤ t → Through P j t → (∀ k, j < k → k ≤ t → ¬ a k) → b j

-- [proof->req~behavioral-past-foundation~1]
theorem previous_lower (P a : Signal) (t : Nat) :
    previous P a t ↔ Temporal.previous (fun j => P j ∧ a j) t := by
  cases t <;> rfl

theorem weakPrevious_lower (P a : Signal) (t : Nat) :
    weakPrevious P a t ↔ ¬ Temporal.previous (fun j => P j ∧ ¬ a j) t := by
  classical
  cases t <;> simp [weakPrevious, Temporal.previous]

theorem since_lower (P a b : Signal) (t : Nat) :
    since P a b t ↔ Temporal.since (fun j => P j ∧ a j) (fun j => P j ∧ b j) t := by
  constructor
  · rintro ⟨j, hj, live, hb, ha⟩
    exact ⟨j, hj, ⟨live j le_rfl hj, hb⟩,
      fun k hjk hkt => ⟨live k (Nat.le_of_lt hjk) hkt, ha k hjk hkt⟩⟩
  · rintro ⟨j, hj, ⟨hp, hb⟩, h⟩
    refine ⟨j, hj, ?_, hb, fun k hjk hkt => (h k hjk hkt).2⟩
    intro k hjk hkt
    rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
    · exact hp
    · exact (h k hlt hkt).1

theorem once_lower (P a : Signal) (t : Nat) :
    once P a t ↔ Temporal.since P (fun j => P j ∧ a j) t := by
  constructor
  · rintro ⟨j, hj, live, ha⟩
    exact ⟨j, hj, ⟨live j le_rfl hj, ha⟩,
      fun k hjk hkt => live k (Nat.le_of_lt hjk) hkt⟩
  · rintro ⟨j, hj, ⟨hp, ha⟩, h⟩
    refine ⟨j, hj, ?_, ha⟩
    intro k hjk hkt
    rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
    · exact hp
    · exact h k hlt hkt

theorem historically_dual (P a : Signal) (t : Nat) :
    historically P a t ↔ ¬ once P (fun j => ¬ a j) t := by
  classical
  constructor
  · rintro h ⟨j, hj, live, ha⟩
    exact ha (h j hj live)
  · intro h j hj live
    by_contra ha
    exact h ⟨j, hj, live, ha⟩

theorem historically_lower (P a : Signal) (t : Nat) :
    historically P a t ↔ ¬ Temporal.since P (fun j => P j ∧ ¬ a j) t := by
  rw [historically_dual, once_lower]

theorem triggered_dual (P a b : Signal) (t : Nat) :
    triggered P a b t ↔ ¬ since P (fun j => ¬ a j) (fun j => ¬ b j) t := by
  classical
  constructor
  · rintro h ⟨j, hj, live, hb, ha⟩
    exact hb (h j hj live ha)
  · intro h j hj live ha
    by_contra hb
    exact h ⟨j, hj, live, hb, ha⟩

theorem triggered_lower (P a b : Signal) (t : Nat) :
    triggered P a b t ↔
      ¬ Temporal.since (fun j => P j ∧ ¬ a j) (fun j => P j ∧ ¬ b j) t := by
  rw [triggered_dual, since_lower]

theorem previous_dual (P a : Signal) (t : Nat) :
    ¬ previous P a t ↔ weakPrevious P (fun j => ¬ a j) t := by
  cases t <;> simp [previous, weakPrevious, not_and]

@[simp] theorem previous_true (a : Signal) (t : Nat) :
    previous (fun _ => True) a t ↔ Temporal.previous a t := by
  cases t <;> simp [previous, Temporal.previous]

@[simp] theorem weakPrevious_true (a : Signal) (t : Nat) :
    weakPrevious (fun _ => True) a t ↔ Temporal.weakPrevious a t := by
  cases t <;> simp [weakPrevious, Temporal.weakPrevious]

@[simp] theorem once_true (a : Signal) (t : Nat) :
    once (fun _ => True) a t ↔ Temporal.once a t := by
  simp [once, Through, Temporal.once]

@[simp] theorem historically_true (a : Signal) (t : Nat) :
    historically (fun _ => True) a t ↔ Temporal.historically a t := by
  simp [historically, Through, Temporal.historically]

@[simp] theorem since_true (a b : Signal) (t : Nat) :
    since (fun _ => True) a b t ↔ Temporal.since a b t := by
  simp [since, Through, Temporal.since]

@[simp] theorem triggered_true (a b : Signal) (t : Nat) :
    triggered (fun _ => True) a b t ↔ Temporal.triggered a b t := by
  simp [triggered, Through, Temporal.triggered]

-- [proof->req~behavioral-past-foundation~1]
/-- A missing current parent leaves no active interval for once/since. -/
theorem once_absent {P a : Signal} {t : Nat} (absent : ¬ P t) : ¬ once P a t := by
  rintro ⟨j, hj, live, _⟩
  exact absent (live t hj le_rfl)

theorem since_absent {P a b : Signal} {t : Nat} (absent : ¬ P t) : ¬ since P a b t := by
  rintro ⟨j, hj, live, _, _⟩
  exact absent (live t hj le_rfl)

theorem historically_absent {P a : Signal} {t : Nat} (absent : ¬ P t) :
    historically P a t := by
  intro j hj live
  exact (absent (live t hj le_rfl)).elim

theorem triggered_absent {P a b : Signal} {t : Nat} (absent : ¬ P t) :
    triggered P a b t := by
  intro j hj live _
  exact (absent (live t hj le_rfl)).elim

/-- The witness cannot cross a gap, even if the parent reappears afterwards. -/
theorem once_after_gap {P a : Signal} {gap t : Nat} (before : gap ≤ t)
    (absent : ¬ P gap) :
    once P a t ↔ ∃ j, gap < j ∧ j ≤ t ∧ Through P j t ∧ a j := by
  constructor
  · rintro ⟨j, hj, live, ha⟩
    have after : gap < j := by
      by_contra h
      exact absent (live gap (Nat.le_of_not_gt h) before)
    exact ⟨j, after, hj, live, ha⟩
  · rintro ⟨j, _, hj, live, ha⟩
    exact ⟨j, hj, live, ha⟩

theorem since_after_gap {P a b : Signal} {gap t : Nat} (before : gap ≤ t)
    (absent : ¬ P gap) :
    since P a b t ↔ ∃ j, gap < j ∧ j ≤ t ∧ Through P j t ∧ b j ∧
      ∀ k, j < k → k ≤ t → a k := by
  constructor
  · rintro ⟨j, hj, live, hb, ha⟩
    have after : gap < j := by
      by_contra h
      exact absent (live gap (Nat.le_of_not_gt h) before)
    exact ⟨j, after, hj, live, hb, ha⟩
  · rintro ⟨j, _, hj, live, hb, ha⟩
    exact ⟨j, hj, live, hb, ha⟩

@[simp] theorem once_zero (P a : Signal) : once P a 0 ↔ P 0 ∧ a 0 := by
  simp [once, Through]

@[simp] theorem since_zero (P a b : Signal) : since P a b 0 ↔ P 0 ∧ b 0 := by
  simp [since, Through]
  intros
  omega

-- [proof->req~behavioral-past-foundation~1]
theorem once_reset {P a : Signal} {t : Nat} (absent : ¬ P t) :
    once P a (t + 1) ↔ P (t + 1) ∧ a (t + 1) := by
  rw [once_after_gap (Nat.le_succ t) absent]
  constructor
  · rintro ⟨j, hj, hjt, live, ha⟩
    have eq : j = t + 1 := by omega
    subst j
    exact ⟨live (t + 1) le_rfl le_rfl, ha⟩
  · rintro ⟨hp, ha⟩
    refine ⟨t + 1, by omega, le_rfl, ?_, ha⟩
    intro k hk hkt
    have eq : k = t + 1 := by omega
    simpa only [eq] using hp

theorem since_reset {P a b : Signal} {t : Nat} (absent : ¬ P t) :
    since P a b (t + 1) ↔ P (t + 1) ∧ b (t + 1) := by
  rw [since_after_gap (Nat.le_succ t) absent]
  constructor
  · rintro ⟨j, hj, hjt, live, hb, _⟩
    have eq : j = t + 1 := by omega
    subst j
    exact ⟨live (t + 1) le_rfl le_rfl, hb⟩
  · rintro ⟨hp, hb⟩
    refine ⟨t + 1, by omega, le_rfl, ?_, hb, ?_⟩
    · intro k hk hkt
      have eq : k = t + 1 := by omega
      simpa only [eq] using hp
    · intro k hk hkt
      omega

end Lifetime
end Clafer.Behavioral
