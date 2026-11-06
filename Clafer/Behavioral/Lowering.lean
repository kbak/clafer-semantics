module

public import Clafer.Behavioral.Normalization

/-!
# Lowering to ordinary infinite-time temporal logic

This core has classical negation and unbounded temporal operators. Explicit
parent and context-lifetime atoms implement T2/T7. `lower` accepts raw Boolean
formulas (including counting bodies); source callers normalize first.
-/

@[expose] public section
namespace Clafer.Behavioral
universe u

inductive LowerAtom (A : Nat → Type) (n : Nat) where
  | source (a : A n)
  | parentPresent
  | starts
  | ends

-- [impl->req~behavioral-signed-normalization~1]
inductive Core (A D : Nat → Type) : Nat → Type where
  | truth : Core A D n
  | atom (a : LowerAtom A n) : Core A D n
  | not (a : Core A D n) : Core A D n
  | and (a b : Core A D n) : Core A D n
  | or (a b : Core A D n) : Core A D n
  | next (a : Core A D n) : Core A D n
  | eventually (a : Core A D n) : Core A D n
  | always (a : Core A D n) : Core A D n
  | strongUntil (a b : Core A D n) : Core A D n
  | weakUntil (a b : Core A D n) : Core A D n
  | quant (q : Quantifier) (d : D n) (a : Core A D (n + 1)) : Core A D n
  | letSet (d : D n) (a : Core A D (n + 1)) : Core A D n

namespace Core
variable {A D : Nat → Type} {C : Type} {U : Type u}

noncomputable def eval (τ : Trace C U) (O : Observation A D U) {n} : Core A D n → Environment U n → Nat → Prop
  | .truth, _, _ => True
  | .atom (.source a), ρ, t => O.atom a ρ t
  | .atom .parentPresent, ρ, t => τ.ParentPresent ρ.this t
  | .atom .starts, ρ, t => τ.Starts t ρ.this
  | .atom .ends, ρ, t => τ.Ends t ρ.this
  | .not a, ρ, t => ¬ a.eval τ O ρ t
  | .and a b, ρ, t => a.eval τ O ρ t ∧ b.eval τ O ρ t
  | .or a b, ρ, t => a.eval τ O ρ t ∨ b.eval τ O ρ t
  | .next a, ρ, t => Temporal.next (a.eval τ O ρ) t
  | .eventually a, ρ, t => Temporal.eventually (a.eval τ O ρ) t
  | .always a, ρ, t => Temporal.always (a.eval τ O ρ) t
  | .strongUntil a b, ρ, t => Temporal.strongUntil (a.eval τ O ρ) (b.eval τ O ρ) t
  | .weakUntil a b, ρ, t => Temporal.weakUntil (a.eval τ O ρ) (b.eval τ O ρ) t
  | .quant q d a, ρ, t => q.eval (O.domain d ρ t) (fun x => a.eval τ O (ρ.push {x}) t)
  | .letSet d a, ρ, t => a.eval τ O (ρ.push (O.domain d ρ t)) t
end Core

namespace Formula
variable {A D : Nat → Type}

-- [impl->req~behavioral-signed-normalization~1]
noncomputable def lower {n} : Formula A D n → Core A D n
  | .truth => .truth
  | .atom a => .atom (.source a)
  | .not a => .not a.lower
  | .and a b => .and a.lower b.lower
  | .or a b => .or a.lower b.lower
  | .implies a b => .or (.not a.lower) b.lower
  | .iff a b => .and (.or (.not a.lower) b.lower) (.or (.not b.lower) a.lower)
  | .xor a b => .not (.and (.or (.not a.lower) b.lower) (.or (.not b.lower) a.lower))
  | .ite c a b => .and (.or (.not c.lower) a.lower) (.or (.not (.not c.lower)) b.lower)
  | .next a => .next (.or (.not (.atom .parentPresent)) a.lower)
  | .eventually a => .eventually (.or (.not (.atom .parentPresent)) a.lower)
  | .always a => .weakUntil (.and (.atom .parentPresent) a.lower) (.not (.atom .parentPresent))
  | .strongUntil a b => .strongUntil (.and (.atom .parentPresent) a.lower)
      (.or (.not (.atom .parentPresent)) b.lower)
  | .weakUntil a b => .or
      (.weakUntil (.and (.atom .parentPresent) a.lower) (.not (.atom .parentPresent)))
      (.strongUntil (.and (.atom .parentPresent) a.lower) (.or (.not (.atom .parentPresent)) b.lower))
  | .initially a => .or (.not (.atom .starts)) a.lower
  | .finally a => .or (.not (.atom .ends)) a.lower
  | .quant q d a => .quant q d a.lower
  | .letSet d a => .letSet d a.lower

-- [proof->req~behavioral-signed-normalization~1]
theorem lower_agrees {C : Type} {U : Type u} (τ : Trace C U)
    (O : Observation A D U) {n} (a : Formula A D n) (ρ : Environment U n) (t : Nat) :
    a.lower.eval τ O ρ t ↔ a.raw τ O ρ t := by
  classical
  induction a generalizing t <;>
    simp_all [lower, Core.eval, raw, Quantifier.eval, Lifetime.weakUntil,
      Lifetime.next_lower, Lifetime.eventually_lower, Lifetime.always_lower,
      Lifetime.until_lower, Temporal.next, Temporal.eventually, Temporal.strongUntil,
      Temporal.weakUntil, Temporal.always]
  all_goals tauto

-- [proof->req~behavioral-signed-normalization~1]
/-- End-to-end source agreement: signs are processed *before* parent guards. -/
theorem normalize_lower_agrees {C : Type} {U : Type u} (τ : Trace C U)
    (O : Observation A D U) {n} (a : Formula A D n) (s : Bool)
    (ρ : Environment U n) (t : Nat) :
    (a.normalize s).lower.eval τ O ρ t ↔ a.denote τ O s ρ t :=
  (lower_agrees τ O (a.normalize s) ρ t).trans (normalize_agrees τ O a s ρ t)

theorem attached_lower_agrees {C : Type} {U : Type u} (τ : Trace C U)
    (O : Observation A D U) (contexts : Nat → Set U) (a : Formula A D 0) :
    a.Attached τ O contexts ↔ ∀ t c, c ∈ contexts t → c ∈ τ.live t →
      (a.normalize true).lower.eval τ O (.closed c) t := by
  simp only [Attached, normalize_lower_agrees]
end Formula
end Clafer.Behavioral
