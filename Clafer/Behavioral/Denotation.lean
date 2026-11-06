module

public import Clafer.Behavioral.Formula
public import Clafer.Behavioral.Lifetime

/-!
# Independent signed source meaning

Paper §5 Definitions 4–5, §6.1, with T2/T7 and D1. `raw` interprets ordinary
Boolean connectives classically and is used inside one/lone barriers. `denote`
gives the two source polarities directly; it does not call normalization/lowering.
-/

@[expose] public section
namespace Clafer.Behavioral
universe u

def polarity (positive : Bool) (p : Prop) : Prop := if positive then p else ¬ p

namespace Formula
variable {A D : Nat → Type} {C : Type} {U : Type u}

-- [impl->req~behavioral-formula-denotation~1]
/-- Classical Boolean interpretation of a body, with T2-bounded temporal nodes.
Only counting barriers use this directly as source meaning. -/
noncomputable def raw (τ : Trace C U) (O : Observation A D U) {n} :
    Formula A D n → Environment U n → Nat → Prop
  | .truth, _, _ => True
  | .atom a, ρ, t => O.atom a ρ t
  | .not a, ρ, t => ¬ a.raw τ O ρ t
  | .and a b, ρ, t => a.raw τ O ρ t ∧ b.raw τ O ρ t
  | .or a b, ρ, t => a.raw τ O ρ t ∨ b.raw τ O ρ t
  | .implies a b, ρ, t => a.raw τ O ρ t → b.raw τ O ρ t
  | .iff a b, ρ, t => (a.raw τ O ρ t ↔ b.raw τ O ρ t)
  | .xor a b, ρ, t => ¬ (a.raw τ O ρ t ↔ b.raw τ O ρ t)
  | .ite c a b, ρ, t =>
      (c.raw τ O ρ t → a.raw τ O ρ t) ∧ (¬ c.raw τ O ρ t → b.raw τ O ρ t)
  | .next a, ρ, t => Lifetime.next (τ.ParentPresent ρ.this) (a.raw τ O ρ) t
  | .eventually a, ρ, t => Lifetime.eventually (τ.ParentPresent ρ.this) (a.raw τ O ρ) t
  | .always a, ρ, t => Lifetime.always (τ.ParentPresent ρ.this) (a.raw τ O ρ) t
  | .strongUntil a b, ρ, t => Lifetime.strongUntil (τ.ParentPresent ρ.this) (a.raw τ O ρ) (b.raw τ O ρ) t
  | .weakUntil a b, ρ, t => Lifetime.weakUntil (τ.ParentPresent ρ.this) (a.raw τ O ρ) (b.raw τ O ρ) t
  | .initially a, ρ, t => τ.Starts t ρ.this → a.raw τ O ρ t
  | .finally a, ρ, t => τ.Ends t ρ.this → a.raw τ O ρ t
  | .quant q d a, ρ, t => q.eval (O.domain d ρ t) (fun x => a.raw τ O (ρ.push {x}) t)
  | .letSet d a, ρ, t => a.raw τ O (ρ.push (O.domain d ρ t)) t

-- [impl->req~behavioral-signed-normalization~1]
/-- Independent signed clauses. A source negation switches polarity; it is
not Lean negation of the interpreted parent-bounded proposition. -/
noncomputable def denote (τ : Trace C U) (O : Observation A D U) {n} :
    Formula A D n → Bool → Environment U n → Nat → Prop
  | .truth, s, _, _ => polarity s True
  | .atom a, s, ρ, t => polarity s (O.atom a ρ t)
  | .not a, s, ρ, t => a.denote τ O (!s) ρ t
  | .and a b, s, ρ, t => if s then
      a.denote τ O true ρ t ∧ b.denote τ O true ρ t else
      a.denote τ O false ρ t ∨ b.denote τ O false ρ t
  | .or a b, s, ρ, t => if s then
      a.denote τ O true ρ t ∨ b.denote τ O true ρ t else
      a.denote τ O false ρ t ∧ b.denote τ O false ρ t
  | .implies a b, s, ρ, t => if s then
      a.denote τ O false ρ t ∨ b.denote τ O true ρ t else
      a.denote τ O true ρ t ∧ b.denote τ O false ρ t
  | .iff a b, s, ρ, t => if s then
      (a.denote τ O false ρ t ∨ b.denote τ O true ρ t) ∧
      (b.denote τ O false ρ t ∨ a.denote τ O true ρ t) else
      (a.denote τ O true ρ t ∧ b.denote τ O false ρ t) ∨
      (b.denote τ O true ρ t ∧ a.denote τ O false ρ t)
  | .xor a b, s, ρ, t => if s then
      (a.denote τ O true ρ t ∧ b.denote τ O false ρ t) ∨
      (a.denote τ O false ρ t ∧ b.denote τ O true ρ t) else
      (a.denote τ O false ρ t ∨ b.denote τ O true ρ t) ∧
      (a.denote τ O true ρ t ∨ b.denote τ O false ρ t)
  | .ite c a b, s, ρ, t => if s then
      (c.denote τ O false ρ t ∨ a.denote τ O true ρ t) ∧
      (c.denote τ O true ρ t ∨ b.denote τ O true ρ t) else
      (c.denote τ O true ρ t ∧ a.denote τ O false ρ t) ∨
      (c.denote τ O false ρ t ∧ b.denote τ O false ρ t)
  | .next a, s, ρ, t => Lifetime.next (τ.ParentPresent ρ.this) (a.denote τ O s ρ) t
  | .eventually a, s, ρ, t => if s then
      Lifetime.eventually (τ.ParentPresent ρ.this) (a.denote τ O true ρ) t else
      Lifetime.always (τ.ParentPresent ρ.this) (a.denote τ O false ρ) t
  | .always a, s, ρ, t => if s then
      Lifetime.always (τ.ParentPresent ρ.this) (a.denote τ O true ρ) t else
      Lifetime.eventually (τ.ParentPresent ρ.this) (a.denote τ O false ρ) t
  | .strongUntil a b, s, ρ, t => if s then
      Lifetime.strongUntil (τ.ParentPresent ρ.this) (a.denote τ O true ρ) (b.denote τ O true ρ) t else
      Lifetime.weakUntil (τ.ParentPresent ρ.this) (b.denote τ O false ρ)
        (fun j => a.denote τ O false ρ j ∧ b.denote τ O false ρ j) t
  | .weakUntil a b, s, ρ, t => if s then
      Lifetime.weakUntil (τ.ParentPresent ρ.this) (a.denote τ O true ρ) (b.denote τ O true ρ) t else
      Lifetime.strongUntil (τ.ParentPresent ρ.this) (b.denote τ O false ρ)
        (fun j => a.denote τ O false ρ j ∧ b.denote τ O false ρ j) t
  | .initially a, s, ρ, t => τ.Starts t ρ.this → a.denote τ O s ρ t
  | .finally a, s, ρ, t => τ.Ends t ρ.this → a.denote τ O s ρ t
  | .quant .all d a, s, ρ, t => if s then
      ∀ x ∈ O.domain d ρ t, a.denote τ O true (ρ.push {x}) t else
      ∃ x ∈ O.domain d ρ t, a.denote τ O false (ρ.push {x}) t
  | .quant .some d a, s, ρ, t => if s then
      ∃ x ∈ O.domain d ρ t, a.denote τ O true (ρ.push {x}) t else
      ∀ x ∈ O.domain d ρ t, a.denote τ O false (ρ.push {x}) t
  | .quant .no d a, s, ρ, t => if s then
      ∀ x ∈ O.domain d ρ t, a.denote τ O false (ρ.push {x}) t else
      ∃ x ∈ O.domain d ρ t, a.denote τ O true (ρ.push {x}) t
  | .quant .one d a, s, ρ, t =>
      polarity s (Quantifier.one.eval (O.domain d ρ t) (fun x => a.raw τ O (ρ.push {x}) t))
  | .quant .lone d a, s, ρ, t =>
      polarity s (Quantifier.lone.eval (O.domain d ρ t) (fun x => a.raw τ O (ρ.push {x}) t))
  | .letSet d a, s, ρ, t => a.denote τ O s (ρ.push (O.domain d ρ t)) t

-- [impl->req~behavioral-formula-denotation~1]
/-- T2/T9 implicit always: every live applicable context starts an obligation.
The body retains that context even when it later disappears. -/
def Attached (τ : Trace C U) (O : Observation A D U) (contexts : Nat → Set U)
    (a : Formula A D 0) : Prop :=
  ∀ t c, c ∈ contexts t → c ∈ τ.live t → a.denote τ O true (.closed c) t

-- [proof->req~behavioral-signed-normalization~1]
theorem double_negation (τ : Trace C U) (O : Observation A D U) {n}
    (a : Formula A D n) (s : Bool) (ρ : Environment U n) (t : Nat) :
    a.not.not.denote τ O s ρ t ↔ a.denote τ O s ρ t := by
  simp [denote]

theorem persistent_eventually_consistent (τ : Trace C U) (O : Observation A D U) {n}
    (a : A n) (ρ : Environment U n) (t : Nat)
    (hp : ∀ j, t ≤ j → τ.ParentPresent ρ.this j) :
    (eventually (atom a)).denote τ O true ρ t →
      ¬ (not (eventually (atom a))).denote τ O true ρ t := by
  exact Lifetime.persistent_eventually_not_always_not hp
end Formula
end Clafer.Behavioral
