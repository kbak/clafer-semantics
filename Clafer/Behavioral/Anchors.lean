module

public import Clafer.Behavioral.PartialCompatibility

/-! # Birth, death and implicit attachment

Behavioral §§4.1/6.1, with T7/T9. An anchor tests the retained context's
current lifetime boundary. Its body can still start parent-bounded obligations.
-/

@[expose] public section
namespace Clafer.Behavioral.Anchors
universe u
variable {A D : Nat → Type} {C : Type} {U : Type u}

-- [impl->req~behavioral-modifiers~1]
def AtBirths (τ : Trace C U) (O : PartialObservation A D U)
    (contexts : Nat → Set U) (a : Formula A D 0) : Prop :=
  ∀ t c, c ∈ contexts t → τ.Starts t c → a.Satisfies τ O true (.closed c) t

def AtDeaths (τ : Trace C U) (O : PartialObservation A D U)
    (contexts : Nat → Set U) (a : Formula A D 0) : Prop :=
  ∀ t c, c ∈ contexts t → τ.Ends t c → a.Satisfies τ O true (.closed c) t

-- [proof->req~behavioral-modifiers~1]
theorem initially_at_births (τ : Trace C U) (O : PartialObservation A D U)
    (contexts : Nat → Set U) (a : Formula A D 0) :
    a.initially.PartialAttached τ O contexts ↔ AtBirths τ O contexts a := by
  constructor
  · intro h t c hc birth
    have ha := h t c hc birth.1
    exact ⟨ha.1 birth, ha.2 birth⟩
  · intro h t c hc _
    exact ⟨fun birth => (h t c hc birth).1, fun birth => (h t c hc birth).2⟩

theorem finally_at_deaths (τ : Trace C U) (O : PartialObservation A D U)
    (contexts : Nat → Set U) (a : Formula A D 0) :
    a.finally.PartialAttached τ O contexts ↔ AtDeaths τ O contexts a := by
  constructor
  · intro h t c hc death
    have ha := h t c hc death.1
    exact ⟨ha.1 death, ha.2 death⟩
  · intro h t c hc _
    exact ⟨fun death => (h t c hc death).1, fun death => (h t c hc death).2⟩

/-- No death means no final observation, including no definedness obligation. -/
theorem finally_vacuous (τ : Trace C U) (O : PartialObservation A D U)
    (contexts : Nat → Set U) (a : Formula A D 0)
    (noDeath : ∀ t c, c ∈ contexts t → ¬ τ.Ends t c) :
    a.finally.PartialAttached τ O contexts := by
  rw [finally_at_deaths]
  exact fun t c hc death => (noDeath t c hc death).elim

theorem birth_zero (τ : Trace C U) (O : PartialObservation A D U)
    (contexts : Nat → Set U) (a : Formula A D 0)
    (h : AtBirths τ O contexts a) {c : U} (hc : c ∈ contexts 0) (live : c ∈ τ.live 0) :
    a.Satisfies τ O true (.closed c) 0 := h 0 c hc ((τ.starts_zero c).mpr live)

theorem birth_again (τ : Trace C U) (O : PartialObservation A D U)
    (contexts : Nat → Set U) (a : Formula A D 0)
    (h : AtBirths τ O contexts a) {c : U} {t : Nat} (hc : c ∈ contexts (t + 1))
    (absent : c ∉ τ.live t) (live : c ∈ τ.live (t + 1)) :
    a.Satisfies τ O true (.closed c) (t + 1) :=
  h (t + 1) c hc ((τ.starts_succ t c).mpr ⟨live, absent⟩)

/-- Under the permanent root, an unanchored eventuality is recurrence. -/
-- [proof->req~behavioral-patterns~1]
theorem root_recurrence (τ : Trace C U) (O : Observation A D U)
    (a : Formula A D 0) (live : ∀ t, τ.identities.root ∈ τ.live t) :
    a.eventually.Attached τ O (fun _ => {τ.identities.root}) ↔
      ∀ t, ∃ j, t ≤ j ∧ a.denote τ O true (.closed τ.identities.root) j := by
  simp only [Formula.Attached, Set.mem_singleton_iff, forall_eq, live, true_implies,
    Formula.denote, ↓reduceIte]
  apply forall_congr'
  intro t
  simp [Lifetime.eventually, Lifetime.Through, Trace.parentPresent_root, Environment.closed]

/-- The same eventuality anchored at the permanent root is a one-time future
existence requirement. This theorem concerns total observations; strict partial
observations additionally retain their active-interval definedness requirement. -/
theorem root_anchored_existence (τ : Trace C U) (O : Observation A D U)
    (a : Formula A D 0) (live : ∀ t, τ.identities.root ∈ τ.live t) :
    a.eventually.initially.Attached τ O (fun _ => {τ.identities.root}) ↔
      ∃ j, a.denote τ O true (.closed τ.identities.root) j := by
  have starts : ∀ t, τ.Starts t τ.identities.root ↔ t = 0 := by
    intro t
    constructor
    · rintro ⟨_, h | ⟨k, _, absent⟩⟩
      · exact h
      · exact (absent (live k)).elim
    · rintro rfl; exact (τ.starts_zero _).mpr (live 0)
  simp [Formula.Attached, Formula.denote, starts, live, Environment.closed,
    Lifetime.eventually, Lifetime.Through, Trace.parentPresent_root]

end Clafer.Behavioral.Anchors
