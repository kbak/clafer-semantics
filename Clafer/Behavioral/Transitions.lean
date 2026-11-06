module

public import Clafer.Behavioral.PartialCompatibility

/-! # Resolved transitions and required sequences

Juodisius et al. §6.1, pp. 2:31–32, amended by 0.5.7 T2–T4.
The first source/guard is conditional; subsequent links are obligations.
`context` is the resolved presence test for the retained attachment instance.
Guards are tested on entry and are not part of the eventual persistence condition.
-/

@[expose] public section
namespace Clafer.Behavioral.Transitions
universe u
variable {A D : Nat → Type} {C : Type} {U : Type u} {n : Nat}

inductive Arrow where
  | immediate | eventual
  deriving DecidableEq

-- [impl->req~behavioral-transition-sugar~1]
inductive Chain (A D : Nat → Type) (n : Nat) where
  | stop (target : Formula A D n)
  | link (source : Formula A D n) (guard : Option (Formula A D n))
      (arrow : Arrow) (rest : Chain A D n)

def precondition (source : Formula A D n) (guard : Option (Formula A D n)) : Formula A D n :=
  match guard with
  | none => source
  | some g => .and source g

def step (context source target : Formula A D n) : Arrow → Formula A D n
  | .immediate => .next target
  | .eventual => .strongUntil (.and context source) target

/-- Direct well-founded recursion avoids a generated unsafe compiler helper.
The measure concerns syntax size only, never trace length or a temporal bound. -/
def Chain.sequence (context : Formula A D n) (chain : Chain A D n) : Formula A D n :=
  (measure (fun c : Chain A D n => sizeOf c)).wf.fix
    (fun c go => match c with
      | .stop target => target
      | .link source guard arrow rest => .and (precondition source guard)
          (step context source (go rest (by change sizeOf _ < sizeOf _; simp +arith)) arrow)) chain

@[simp] theorem Chain.sequence_stop (context target : Formula A D n) :
    (Chain.stop target).sequence context = target := by
  unfold sequence
  rw [WellFounded.fix_eq]

@[simp] theorem Chain.sequence_link (context source : Formula A D n) (guard) (arrow)
    (rest : Chain A D n) :
    (Chain.link source guard arrow rest).sequence context =
      .and (precondition source guard) (step context source (rest.sequence context) arrow) := by
  unfold sequence
  rw [WellFounded.fix_eq]

def Chain.expand (context : Formula A D n) : Chain A D n → Formula A D n
  | .stop target => target
  | .link source guard arrow rest =>
      .implies (precondition source guard) (step context source (rest.sequence context) arrow)

/-- Independent signed entry test, including temporal guards. -/
def entry (τ : Trace C U) (O : Observation A D U) (source : Formula A D n)
    (guard : Option (Formula A D n)) (s : Bool) (ρ : Environment U n) (t : Nat) : Prop :=
  match guard with
  | none => source.denote τ O s ρ t
  | some g => if s then source.denote τ O true ρ t ∧ g.denote τ O true ρ t
      else source.denote τ O false ρ t ∨ g.denote τ O false ρ t

/-- A step interprets the required suffix directly. Negative eventual steps
use the signed U dual; they are not classical failure after cancellation. -/
def advance (τ : Trace C U) (O : Observation A D U) (context source : Formula A D n)
    (arrow : Arrow) (s : Bool) (ρ : Environment U n) (target : Bool → Signal) : Signal :=
  match arrow with
  | .immediate => Lifetime.next (τ.ParentPresent ρ.this) (target s)
  | .eventual => if s then
      Lifetime.strongUntil (τ.ParentPresent ρ.this)
        (fun j => context.denote τ O true ρ j ∧ source.denote τ O true ρ j) (target true)
    else Lifetime.weakUntil (τ.ParentPresent ρ.this) (target false)
      (fun j => (context.denote τ O false ρ j ∨ source.denote τ O false ρ j) ∧ target false j)

-- [impl->req~behavioral-transition-sugar~1]
noncomputable def Chain.required (τ : Trace C U) (O : Observation A D U) (context : Formula A D n)
    (ρ : Environment U n) : Chain A D n → Bool → Signal
  | .stop target, s => target.denote τ O s ρ
  | .link source guard arrow rest, s => fun t => if s then
      entry τ O source guard true ρ t ∧ advance τ O context source arrow true ρ (rest.required τ O context ρ) t
    else entry τ O source guard false ρ t ∨ advance τ O context source arrow false ρ (rest.required τ O context ρ) t

noncomputable def Chain.meaning (τ : Trace C U) (O : Observation A D U) (context : Formula A D n)
    (ρ : Environment U n) : Chain A D n → Bool → Signal
  | .stop target, s => target.denote τ O s ρ
  | .link source guard arrow rest, s => fun t => if s then
      entry τ O source guard false ρ t ∨ advance τ O context source arrow true ρ (rest.required τ O context ρ) t
    else entry τ O source guard true ρ t ∧ advance τ O context source arrow false ρ (rest.required τ O context ρ) t

-- [proof->req~behavioral-transition-sugar~1]
theorem precondition_agrees (τ : Trace C U) (O : Observation A D U)
    (source : Formula A D n) (guard) (s) (ρ) (t) :
    (precondition source guard).denote τ O s ρ t ↔ entry τ O source guard s ρ t := by
  cases guard <;> cases s <;> rfl

theorem step_agrees (τ : Trace C U) (O : Observation A D U)
    (context source target : Formula A D n) (arrow) (s) (ρ) (t) :
    (step context source target arrow).denote τ O s ρ t ↔
      advance τ O context source arrow s ρ (fun s => target.denote τ O s ρ) t := by
  cases arrow <;> cases s <;> rfl

theorem Chain.sequence_agrees (τ : Trace C U) (O : Observation A D U)
    (context : Formula A D n) (chain : Chain A D n) (ρ) (s) (t) :
    (chain.sequence context).denote τ O s ρ t ↔ chain.required τ O context ρ s t := by
  induction chain generalizing s t with
  | stop => rw [Chain.sequence_stop]; rfl
  | link source guard arrow rest ih =>
      have he : (fun s => (rest.sequence context).denote τ O s ρ) =
          rest.required τ O context ρ := funext fun s => funext fun t => propext (ih s t)
      cases s <;> simp only [Chain.sequence_link, Formula.denote, Bool.false_eq_true,
        ↓reduceIte, precondition_agrees, step_agrees, he, Chain.required]

-- [proof->req~behavioral-transition-sugar~1]
theorem Chain.expand_agrees (τ : Trace C U) (O : Observation A D U)
    (context : Formula A D n) (chain : Chain A D n) (ρ) (s) (t) :
    (chain.expand context).denote τ O s ρ t ↔ chain.meaning τ O context ρ s t := by
  cases chain with
  | stop => rfl
  | link source guard arrow rest =>
      have he : (fun s => (rest.sequence context).denote τ O s ρ) =
          rest.required τ O context ρ :=
        funext fun s => funext fun t => propext (rest.sequence_agrees τ O context ρ s t)
      cases s <;> simp only [Chain.expand, Formula.denote, Bool.false_eq_true,
        ↓reduceIte, precondition_agrees, step_agrees, he, Chain.meaning]

/-- Preserve the original strict partial domain alongside the normalized core.
In particular, a false first source never erases an undefined guard/target. -/
-- [proof->req~behavioral-transition-sugar~1]
theorem Chain.partial_agrees (τ : Trace C U) (O : PartialObservation A D U)
    (context : Formula A D n) (chain : Chain A D n) (ρ) (s) (t) :
    (chain.expand context).Satisfies τ O s ρ t ↔
      (chain.expand context).Defined τ O ρ t ∧ chain.meaning τ O.canonical context ρ s t := by
  rw [Formula.Satisfies, chain.expand_agrees]

/-- Signed normalization interface over the executable surface expansion. -/
noncomputable def Chain.normalize (context : Formula A D n) (chain : Chain A D n) (s : Bool) :=
  (chain.expand context).normalize s

theorem Chain.normalize_agrees (τ : Trace C U) (O : Observation A D U)
    (context : Formula A D n) (chain : Chain A D n) (ρ) (s) (t) :
    (chain.normalize context s).raw τ O ρ t ↔ chain.meaning τ O context ρ s t := by
  rw [Chain.normalize, Formula.normalize_agrees, chain.expand_agrees]

-- [proof->req~behavioral-transition-sugar~1]
theorem Chain.lower_agrees (τ : Trace C U) (O : Observation A D U)
    (context : Formula A D n) (chain : Chain A D n) (ρ) (s) (t) :
    (chain.normalize context s).lower.eval τ O ρ t ↔ chain.meaning τ O context ρ s t := by
  rw [Formula.lower_agrees, chain.normalize_agrees]

/-- The source of a declaration arrow is this particular live instance. The
same `presence` supplies the persistence condition for an eventual arrow. -/
def presence (C : Type) {n : Nat} : Formula (SetAtom C) (SetExpr C) n :=
  .atom (.inhabited .this)

def declaration {C : Type} {n : Nat}
    (guard : Option (Formula (SetAtom C) (SetExpr C) n)) (arrow : Arrow)
    (rest : Chain (SetAtom C) (SetExpr C) n) : Formula (SetAtom C) (SetExpr C) n :=
  (Chain.link (presence C) guard arrow rest).expand (presence C)

theorem presence_agrees {k : Nat} (m : Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) (ρ : Environment U n) (t : Nat) (s : Bool) :
    (presence (Fin k)).denote τ (.sets m τ) s ρ t ↔ polarity s (ρ.this ∈ τ.live t) := by
  cases s <;> simp [presence, Formula.denote, polarity, Observation.sets,
    SetAtom.eval, SetExpr.eval, Set.Nonempty]

end Clafer.Behavioral.Transitions
