module

public import Clafer.Behavioral.Transitions
public import Clafer.Behavioral.FormulaExamples

/-! # Nonvacuous transition sequences

T2–T4: the checked cycling trace supplies source disappearance, parent
cancellation and reappearance. Independent observations distinguish each state
and guard; mutations remove a required intermediate state or an entry guard.
-/

@[expose] public section
namespace Clafer.Behavioral.TransitionExamples
open Transitions Examples

abbrev A (_ : Nat) := Fin 4
abbrev D (_ : Nat) := Unit
abbrev F := Formula A D 0
def atom (i : Fin 4) : F := .atom i
def context : F := .truth
def root : Environment (Fin 8) 0 := .closed 0

def timed : Observation A D (Fin 8) where
  atom a _ t := t = a.val
  domain _ _ _ := ∅

def sequence : Chain A D 0 :=
  .link (atom 0) none .immediate (.link (atom 1) (some (atom 1)) .immediate (.stop (atom 2)))

-- [utest->req~behavioral-transition-sugar~1]
theorem three_states : (sequence.expand context).denote cycling timed true root 0 := by
  simp [sequence, Chain.expand, Chain.sequence_stop, Chain.sequence_link, precondition, step, Formula.denote,
    polarity, atom, timed, Lifetime.next, root, Environment.closed]

def missingMiddle : Observation A D (Fin 8) :=
  { timed with atom := fun a _ t => a ≠ 1 ∧ t = a.val }

-- [utest->req~behavioral-transition-sugar~1]
theorem missing_middle_rejected :
    ¬ (sequence.expand context).denote cycling missingMiddle true root 0 := by
  simp [sequence, Chain.expand, Chain.sequence_stop, Chain.sequence_link, precondition, step, Formula.denote,
    polarity, atom, missingMiddle, Lifetime.next, root, Environment.closed]
  exact cycling.parentPresent_root 1

theorem nested_implication_bug :
    (Formula.implies (atom 0) (.next (.implies (atom 1) (.next (atom 2))))).denote
      cycling missingMiddle true root 0 := by
  simp [Formula.denote, polarity, atom, missingMiddle, Lifetime.next, root, Environment.closed]

theorem first_source_conditional :
    (sequence.expand context).denote cycling timed true root 7 := by
  exact Or.inl (by decide : ¬ (7 = 0))

def missingGuard : Chain A D 0 :=
  .link (atom 0) none .immediate (.link (atom 1) (some (atom 3)) .immediate (.stop (atom 2)))

theorem subsequent_guard_required :
    ¬ (missingGuard.expand context).denote cycling timed true root 0 := by
  simp [missingGuard, Chain.expand, Chain.sequence_stop, Chain.sequence_link, precondition, step, Formula.denote,
    polarity, atom, timed, Lifetime.next, root, Environment.closed]
  exact cycling.parentPresent_root 1

def delayed : Observation A D (Fin 8) where
  atom a _ t := if a = 0 then t < 3 else if a = 1 then t = 0 else t = 3
  domain _ _ _ := ∅

def guardedEventual : Chain A D 0 :=
  .link (atom 0) (some (atom 1)) .eventual (.stop (atom 2))

theorem entry_guard_need_not_persist :
    (guardedEventual.expand context).denote cycling delayed true root 0 := by
  apply Or.inr
  refine ⟨3, by omega, Or.inr ?_, ?_⟩
  · simp [Chain.sequence_stop, atom, Formula.denote, polarity, delayed]
  · intro k _ hk
    exact ⟨cycling.parentPresent_root k, trivial, by simpa [atom, Formula.denote, polarity, delayed] using hk⟩

/-- A declaration-like source dies at state 1 while its parent survives. -/
def liveSource : Observation A D (Fin 8) where
  atom a ρ t := if a = 0 then ρ.this ∈ cycling.live t else False
  domain _ _ _ := ∅

def leave : Chain A D 0 := .link (atom 0) none .immediate (.stop (atom 1))

theorem source_death_not_cancellation :
    ¬ (leave.expand (atom 0)).denote cycling liveSource true (.closed 3) 0 := by
  simp [leave, Chain.expand, Chain.sequence_stop, precondition, step, Formula.denote, polarity, atom,
    liveSource, Lifetime.next, Trace.ParentPresent, Environment.closed, cycling, pool, phaseLive]

/-- Skip the intermediate context-only death: the live source and its parent
both disappear on the next edge. Every selected snapshot remains admitted. -/
def parentGap : Trace (Fin 4) (Fin 8) where
  identities := cycling.identities
  live t := cycling.live (2 * t)
  deref t := cycling.deref (2 * t)

theorem parentGap_valid : parentGap.Valid Examples.model where
  identities := cycling_valid.identities
  root_live t := cycling_valid.root_live (2 * t)
  parent_live t := cycling_valid.parent_live (2 * t)
  states t := by
    have h := cycling_valid.states (2 * t)
    exact ⟨h.typed, h.root_head, h.root_separate, h.inherits, h.abstracts,
      h.parents, h.references, h.keys, h.multiplicities, h.groups, h.disjoint⟩

def gapSource : Observation A D (Fin 8) where
  atom a ρ t := if a = 0 then ρ.this ∈ parentGap.live t else False
  domain _ _ _ := ∅

-- [utest->req~behavioral-transition-sugar~1]
theorem parent_death_cancels :
    (3 : Fin 8) ∈ parentGap.live 0 ∧
    (leave.expand (atom 0)).denote parentGap gapSource true (.closed 3) 0 := by
  refine ⟨by simp [parentGap, cycling, phaseLive], Or.inr ?_⟩
  intro hp
  simp [Trace.ParentPresent, Environment.closed, parentGap, cycling, pool, phaseLive] at hp

theorem false_entry_guard_vacuous :
    ((Chain.link (atom 0) (some (atom 1)) .immediate (.stop (atom 2))).expand context).denote
      cycling timed true root 0 := by
  exact Or.inl (Or.inr (by decide : ¬ (0 = 1)))

/-- Even though the parent ends at 2, source disappearance at 1 is too early
for an eventual transition whose target never holds. -/
theorem eventual_source_disappearance_rejected :
    ¬ ((Chain.link (atom 0) none .eventual (.stop (atom 1))).expand (atom 0)).denote
      cycling liveSource true (.closed 3) 0 := by
  rintro (absent | ⟨j, _, stop, before⟩)
  · exact absent (by simp [liveSource,
      Environment.closed, cycling, phaseLive])
  · by_cases hj : 1 < j
    · have bad := (before 1 (by omega) hj).2.1
      simp [atom, Formula.denote, polarity, liveSource, Environment.closed, cycling, phaseLive] at bad
    · have hp : cycling.ParentPresent 3 j := by
        have : j = 0 ∨ j = 1 := by omega
        rcases this with rfl | rfl <;> simp [Trace.ParentPresent, cycling, pool, phaseLive]
      rcases stop with gone | target
      · exact gone hp
      · simp [atom, Formula.denote, polarity, liveSource] at target

theorem reappearance_new_obligation :
    ¬ (leave.expand (atom 0)).denote cycling liveSource true (.closed 3) 3 := by
  simp [leave, Chain.expand, Chain.sequence_stop, precondition, step, Formula.denote, polarity, atom,
    liveSource, Lifetime.next, Trace.ParentPresent, Environment.closed, cycling, pool, phaseLive]


/-- Required sequence composition also covers mixed immediate/eventual arrows. -/
-- [utest->req~behavioral-transition-sugar~1]
theorem mixed_sequence :
    ((Chain.link (atom 0) none .immediate
      (.link (atom 1) (some (atom 1)) .eventual (.stop (atom 2)))).expand context).denote
        cycling timed true root 0 := by
  apply Or.inr
  intro _
  rw [Chain.sequence_link, Chain.sequence_stop]
  refine ⟨⟨rfl, rfl⟩, 2, by omega, Or.inr rfl, ?_⟩
  intro k hk hkt
  have he : k = 1 := by omega
  subst k
  exact ⟨cycling.parentPresent_root 1, trivial, rfl⟩

end Clafer.Behavioral.TransitionExamples
