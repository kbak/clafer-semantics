module

public import Clafer.Behavioral.Environment

/-! # Resolved temporal formulas

Behavioral paper §5 Definition 4 / §6.1 and T2. Atom/domain families carry
lexical depth. Names and source resolution are outside this representation.
-/

@[expose] public section
namespace Clafer.Behavioral

inductive Quantifier where
  | all | some | no | one | lone
  deriving DecidableEq

-- [impl->req~behavioral-formula-denotation~1]
inductive Formula (A D : Nat → Type) : Nat → Type where
  | truth : Formula A D n
  | atom (a : A n) : Formula A D n
  | not (a : Formula A D n) : Formula A D n
  | and (a b : Formula A D n) : Formula A D n
  | or (a b : Formula A D n) : Formula A D n
  | implies (a b : Formula A D n) : Formula A D n
  | iff (a b : Formula A D n) : Formula A D n
  | xor (a b : Formula A D n) : Formula A D n
  | ite (c a b : Formula A D n) : Formula A D n
  | next (a : Formula A D n) : Formula A D n
  | eventually (a : Formula A D n) : Formula A D n
  | always (a : Formula A D n) : Formula A D n
  | strongUntil (a b : Formula A D n) : Formula A D n
  | weakUntil (a b : Formula A D n) : Formula A D n
  | initially (a : Formula A D n) : Formula A D n
  | finally (a : Formula A D n) : Formula A D n
  | quant (q : Quantifier) (domain : D n) (body : Formula A D (n + 1)) : Formula A D n
  | letSet (value : D n) (body : Formula A D (n + 1)) : Formula A D n

-- [impl->req~behavioral-environments~1]
/-- A total observation interface. This is not an adapter for partial static
atoms: an adapter must separately establish admissibility and definedness. -/
structure Observation (A D : Nat → Type) (U : Type u) where
  atom : ∀ {n}, A n → Environment U n → Nat → Prop
  domain : ∀ {n}, D n → Environment U n → Nat → Set U

def Observation.sets {k : Nat} {U : Type u} (m : Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) : Observation (SetAtom (Fin k)) (SetExpr (Fin k)) U where
  atom a ρ t := a.eval m τ ρ t
  domain a ρ t := a.eval m τ ρ t

namespace Quantifier
-- [impl->req~behavioral-signed-normalization~1]
/-- Counting distinct captured identities needs no finite-domain assumption. -/
def eval {U : Type u} (q : Quantifier) (S : Set U) (a : U → Prop) : Prop :=
  match q with
  | .all => ∀ x ∈ S, a x
  | .some => ∃ x ∈ S, a x
  | .no => ¬ ∃ x ∈ S, a x
  | .one => ∃! x, x ∈ S ∧ a x
  | .lone => ∀ x ∈ S, ∀ y ∈ S, a x → a y → x = y
end Quantifier
end Clafer.Behavioral
