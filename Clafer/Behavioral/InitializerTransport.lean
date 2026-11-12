module

public import Clafer.Behavioral.PartialObservation

/-! # Original-context initializer observations

Behavioral §5 Definitions 4–5 / §6.1, T2/T7–T9 and the accepted #171 RHS
transport contract. A generated child binder has a separate attachment frame.
The original identity is retained, never reconstructed through live navigation.
The interface accepts any resolved partial value observation, including formulas
inside value conditions; it is not restricted to the candidate collection grammar.
-/

@[expose] public section
namespace Clafer.Behavioral.Initializers.Transport
universe u v

abbrev Value (U : Type u) (α : Type v) (n : Nat) :=
  Environment U n → Nat → Option α

-- [impl->req~behavioral-environments~1]
/-- Slot zero belongs to the generated child binder. Source variables occupy
successor slots, independently of names. `origin` is the original attachment. -/
structure Frame (U : Type u) (n : Nat) where
  origin : U
  child : Environment U (n + 1)

def move {U : Type u} {n : Nat} (ρ : Environment U n) (x : U) : Frame U n :=
  ⟨ρ.this, ⟨x, (ρ.push {x}).lookup⟩⟩

def Frame.restore {U : Type u} {n : Nat} (f : Frame U n) : Environment U n :=
  ⟨f.origin, fun i => f.child.lookup i.succ⟩

/-- A source binder is inserted after the generated slot, avoiding capture. -/
def Frame.push {U : Type u} {n : Nat} (f : Frame U n) (S : Set U) : Frame U (n + 1) :=
  move (f.restore.push S) f.child.this

def moved {U : Type u} {α : Type v} {n : Nat} (e : Value U α n)
    (f : Frame U n) (t : Nat) : Option α := e f.restore t

-- [proof->req~behavioral-environments~1]
@[simp] theorem restore_move {U : Type u} {n : Nat} (ρ : Environment U n) (x : U) :
    (move ρ x).restore = ρ := by cases ρ; rfl

@[simp] theorem restore_push {U : Type u} {n : Nat} (f : Frame U n) (S : Set U) :
    (f.push S).restore = f.restore.push S := restore_move _ _

/-- Equality of the complete partial observation, for every source evaluator
and time. In particular this proves preservation of `none` and `some ∅`.
There is no assumed equality of observations on the two sides. -/
theorem observation_preserved {U : Type u} {α : Type v} {n : Nat}
    (e : Value U α n) (ρ : Environment U n) (x : U) (t : Nat) :
    moved e (move ρ x) t = e ρ t := by simp [moved]

theorem binder_preserved {U : Type u} {α : Type v} {n : Nat}
    (e : Value U α (n + 1)) (ρ : Environment U n) (x : U) (S : Set U) (t : Nat) :
    moved e ((move ρ x).push S) t = e (ρ.push S) t := by simp [moved]

-- [impl->req~behavioral-formula-denotation~1]
/-- A value condition is a raw Boolean barrier, with the complete strict
formula domain. Signed source negation outside a value never rewrites it. -/
noncomputable def condition {C : Type} {U : Type u} {A D : Nat → Type} {n : Nat}
    (τ : Trace C U) (O : PartialObservation A D U) (c : Formula A D n) : Value U Bool n := by
  classical
  exact fun ρ t => if c.Defined τ O ρ t then some (decide (c.raw τ O.canonical ρ t)) else none

/-- Strict in the condition and both values, even the unselected branch. -/
def choose {α : Type v} (c : Option Bool) (yes no : Option α) : Option α :=
  match c, yes, no with
  | some b, some a, some z => some (if b then a else z)
  | _, _, _ => none

noncomputable def conditional {C : Type} {U : Type u} {α : Type v}
    {A D : Nat → Type} {n : Nat} (τ : Trace C U) (O : PartialObservation A D U)
    (c : Formula A D n) (yes no : Value U α n) : Value U α n :=
  fun ρ t => choose (condition τ O c ρ t) (yes ρ t) (no ρ t)

-- [proof->req~behavioral-reference-atoms~1]
theorem choose_defined {α : Type v} (c : Option Bool) (a b : Option α) :
    (∃ x, choose c a b = some x) ↔
      (∃ p, c = some p) ∧ (∃ x, a = some x) ∧ (∃ y, b = some y) := by
  cases c <;> cases a <;> cases b <;> simp [choose]

theorem conditional_preserved {C : Type} {U : Type u} {α : Type v}
    {A D : Nat → Type} {n : Nat} (τ : Trace C U) (O : PartialObservation A D U)
    (c : Formula A D n) (a b : Value U α n) (ρ : Environment U n) (x : U) (t : Nat) :
    moved (conditional τ O c a b) (move ρ x) t = conditional τ O c a b ρ t :=
  observation_preserved _ _ _ _

/-- The source formula, including quantifiers, captures, all temporal
operators and anchors, is evaluated in the restored original environment. -/
theorem formula_preserved {C : Type} {U : Type u} {A D : Nat → Type} {n : Nat}
    (τ : Trace C U) (O : PartialObservation A D U) (a : Formula A D n)
    (ρ : Environment U n) (x : U) (t : Nat) (s : Bool) :
    a.Satisfies τ O s (move ρ x).restore t ↔ a.Satisfies τ O s ρ t := by simp

-- [impl->req~behavioral-initializer-contract~1]
inductive Origin where
  | root | parent
  deriving DecidableEq

/-- Selection depends on the authored declaration view, not the subtype's
location. A parentless abstract uses root even for a nested concrete head. -/
def original {C : Type} {U : Type u} (ids : Identities C U) : Origin → U → Option U
  | .root, _ => some ids.root
  | .parent, x => ids.parent x

/-- Construct a frame from resolved ownership; missing ownership stays absent.
The fixed identity map is used once, outside any future RHS navigation. -/
def attach {C : Type} {U : Type u} {n : Nat} (ids : Identities C U)
    (origin : Origin) (captures : Fin n → Set U) (x : U) : Option (Frame U n) :=
  (original ids origin x).map (fun p => move ⟨p, captures⟩ x)

-- [proof->req~behavioral-environments~1]
theorem attach_parent {C : Type} {U : Type u} {n : Nat} (ids : Identities C U)
    (captures : Fin n → Set U) (x p : U) (owned : ids.parent x = some p) :
    attach ids .parent captures x = some (move ⟨p, captures⟩ x) := by
  simp [attach, original, owned]

theorem attach_root {C : Type} {U : Type u} {n : Nat} (ids : Identities C U)
    (captures : Fin n → Set U) (x : U) :
    attach ids .root captures x = some (move ⟨ids.root, captures⟩ x) := rfl

theorem attached_parent_observation {C : Type} {U : Type u} {α : Type v} {n : Nat}
    (ids : Identities C U) (e : Value U α n) (captures : Fin n → Set U)
    (x p : U) (owned : ids.parent x = some p) (t : Nat) :
    (attach ids .parent captures x).bind (fun f => moved e f t) = e ⟨p, captures⟩ t := by
  rw [attach_parent ids captures x p owned]
  simp [observation_preserved]

end Clafer.Behavioral.Initializers.Transport
