module

public import Clafer.Behavioral.Orbit
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod

/-!
# Finite lassos and their independent infinite unfolding

Behavioral paper §5 Definitions 2–5 / §6.2, amended by T1/T7/T13.
Identity, direct type and parent are shared across every state. Presence and
references may change, including on the last-to-loop edge. The finite clock
retains the previous position to distinguish time zero and first loop entry.
-/

@[expose] public section
namespace Clafer.Behavioral

-- [impl->req~behavioral-lassos~1]
/-- `last + 1` stored states, an optional empty prefix, and a nonempty loop.
The object inventory includes absent and unused identities. -/
structure Lasso (C : Type) (size last : Nat) where
  identities : Identities C (Fin size)
  loop : Fin (last + 1)
  live : Fin (last + 1) → Fin size → Bool
  deref : Fin (last + 1) → C → Fin size → Fin size → Bool

namespace Lasso
variable {C : Type} {size last : Nat} (L : Lasso C size last)

abbrev Position (last : Nat) := Fin (last + 1)
abbrev Clock (last : Nat) := Position last × Option (Position last)

def next (i : Position last) : Position last :=
  if h : i.val < last then ⟨i.val + 1, by omega⟩ else L.loop

def step (s : Clock last) : Clock last := (L.next s.1, some s.1)

def start : Clock last := (0, none)

def clock (t : Nat) : Clock last := L.step^[t] start

@[simp] theorem clock_zero : L.clock 0 = start := rfl
@[simp] theorem clock_succ (t : Nat) : L.clock (t + 1) = L.step (L.clock t) :=
  Function.iterate_succ_apply' _ _ _

theorem clock_add (t k : Nat) : L.clock (t + k) = L.step^[k] (L.clock t) := by
  rw [Nat.add_comm, clock, Function.iterate_add_apply]
  rfl

-- [proof->req~behavioral-lassos~1]
theorem clock_first (t : Nat) (h : t ≤ last) : (L.clock t).1 = ⟨t, by omega⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [clock_succ, step]
    rw [ih (by omega)]
    simp [next, show t < last by omega]

-- [impl->req~behavioral-lassos~1]
def unfold : Trace C (Fin size) where
  identities := L.identities
  live t := {x | L.live (L.clock t).1 x = true}
  deref t d x y := L.deref (L.clock t).1 d x y = true

/-- The observed predecessor is history, not the loop predecessor on first entry. -/
def starts (s : Clock last) (x : Fin size) : Bool :=
  L.live s.1 x && match s.2 with
    | none => true
    | some p => !L.live p x

def ends (s : Clock last) (x : Fin size) : Bool :=
  L.live s.1 x && !L.live (L.next s.1) x

def parentPresent (s : Clock last) (x : Fin size) : Bool :=
  decide (x = L.identities.root) ||
    match L.identities.parent x with
    | none => false
    | some p => L.live s.1 p

-- [proof->req~behavioral-lassos~1]
theorem starts_agrees (t : Nat) (x : Fin size) :
    L.starts (L.clock t) x = true ↔ L.unfold.Starts t x := by
  cases t with
  | zero => simp [starts, start, Trace.starts_zero, unfold]
  | succ t => simp [starts, step, Trace.starts_succ, unfold]

theorem ends_agrees (t : Nat) (x : Fin size) :
    L.ends (L.clock t) x = true ↔ L.unfold.Ends t x := by
  simp [ends, Trace.Ends, unfold, step]

theorem parentPresent_agrees (t : Nat) (x : Fin size) :
    L.parentPresent (L.clock t) x = true ↔ L.unfold.ParentPresent x t := by
  cases hp : L.identities.parent x <;>
    simp [parentPresent, Trace.ParentPresent, unfold, hp]

/-- A slot as an infinite constant trace, used only to express its static checks. -/
def state (i : Position last) : Trace C (Fin size) where
  identities := L.identities
  live _ := {x | L.live i x = true}
  deref _ d x y := L.deref i d x y = true

-- [impl->req~behavioral-lassos~1]
/-- All stored states must satisfy the unchanged structural snapshot contract.
The finite clock adds no no-reappearance or reference-stability restriction. -/
def Valid {n : Nat} (m : Semantics.EffectiveCore n) (L : Lasso (Fin n) size last) : Prop :=
  L.identities.Valid m ∧
  (∀ i, L.live i L.identities.root = true) ∧
  (∀ i x p, L.live i x = true → L.identities.parent x = some p → L.live i p = true) ∧
  ∀ i, (L.state i).StateValid m 0

-- [proof->req~behavioral-lassos~1]
theorem valid_unfold {n : Nat} (m : Semantics.EffectiveCore n)
    (L : Lasso (Fin n) size last) (h : L.Valid m) : L.unfold.Valid m where
  identities := h.1
  root_live t := h.2.1 (L.clock t).1
  parent_live t := h.2.2.1 (L.clock t).1
  states t := by
    rcases h.2.2.2 (L.clock t).1 with ⟨ht, hr, hs, hi, ha, hp, he, hk, hm, hg, hd⟩
    exact ⟨ht, hr, hs, hi, ha, hp, he, hk, hm, hg, hd⟩

-- [proof->req~behavioral-lassos~1]
theorem valid_iff_unfold {n : Nat} (m : Semantics.EffectiveCore n)
    (L : Lasso (Fin n) size last) : L.Valid m ↔ L.unfold.Valid m := by
  refine ⟨L.valid_unfold m, fun h => ?_⟩
  have atSlot (i : Position last) : (L.clock i.val).1 = i := L.clock_first i.val (by omega)
  refine ⟨h.identities, ?_, ?_, ?_⟩
  · intro i
    have hi := h.root_live i.val
    change L.live (L.clock i.val).1 L.identities.root = true at hi
    simpa only [atSlot] using hi
  · intro i x p hx hp
    have hi := h.parent_live i.val x p
    change (L.live (L.clock i.val).1 x = true → _ → L.live (L.clock i.val).1 p = true) at hi
    rw [atSlot] at hi
    exact hi hx hp
  · intro i
    rcases h.states i.val with ⟨ht, hr, hs, hi, ha, hp, he, hk, hm, hg, hd⟩
    have eqRaw : L.unfold.raw m i.val = (L.state i).raw m 0 := by
      simp only [Trace.raw, Trace.ParentAt, unfold, state, atSlot]
    rw [eqRaw] at ht hr hs hi ha hp he hk hm hg hd
    exact ⟨ht, hr, hs, hi, ha, hp, he, hk, hm, hg, hd⟩

/-- Range-check the loop before constructing a lasso. Empty state arrays have no
representation here and must be rejected by the caller's parser. -/
def loopIndex (states index : Nat) : Option (Fin states) :=
  if h : index < states then some ⟨index, h⟩ else none

-- [proof->req~behavioral-lassos~1]
theorem loopIndex_none (states index : Nat) :
    loopIndex states index = none ↔ states ≤ index := by
  simp [loopIndex]

end Lasso
end Clafer.Behavioral
