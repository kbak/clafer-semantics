module

public import Clafer.Behavioral.PartialCompatibility

/-! # Reviewed declaration-initializer profile

Behavioral §6.1 p.2:29, pinned 0.5.7 CheatSheet and Desugarer.desugarInit.
Constant `=` is a presence-guarded equation in the declaration's enclosing
attachment context. The frontend supplies the resolved head and value views;
implicit dereference/name lookup is not repeated here. `:=` is explicitly
unsupported in the adopted profile. Neither form means temporal birth.
-/

@[expose] public section
namespace Clafer.Behavioral.Initializers
universe u

inductive Form where
  | constant | defaultValue
  deriving DecidableEq

-- [impl->req~behavioral-structural-compatibility~1]
def constant {C : Type} {n : Nat} (heads left value : CollectionExpr C n) :
    Formula (PrimitiveExpression.Atom C) (CollectionExpr C) n :=
  .implies (.atom (.inhabited heads)) (.atom (.equal left value))

def elaborate {C : Type} {n : Nat} (form : Form) (heads left value : CollectionExpr C n) :
    Option (Formula (PrimitiveExpression.Atom C) (CollectionExpr C) n) :=
  match form with
  | .constant => some (constant heads left value)
  | .defaultValue => none

-- [proof->req~behavioral-structural-compatibility~1]
theorem default_rejected {C : Type} {n : Nat} (heads left value : CollectionExpr C n) :
    elaborate .defaultValue heads left value = none := rfl

/-- Definedness remains strict even if the head observation is empty. The
presence implication does not hide an undefined arithmetic operand. -/
theorem constant_truth {k n : Nat} {U : Type u} (m : Structural.Core k)
    (τ : Trace (Fin k) U) (R : Constraints.IntegerRealization U) (ρ : Environment U n) (t : Nat)
    (heads left value : CollectionExpr (Fin k) n) (H L V : Set U)
    (hh : PrimitiveExpression.collection m.toEffectiveCore (Structural.observed m τ) R ρ t heads = some H)
    (hl : PrimitiveExpression.collection m.toEffectiveCore (Structural.observed m τ) R ρ t left = some L)
    (hv : PrimitiveExpression.collection m.toEffectiveCore (Structural.observed m τ) R ρ t value = some V) :
    (constant heads left value).Satisfies τ (.primitives m τ R) true ρ t ↔
      (H.Nonempty → L = V) := by
  classical
  simp [constant, Formula.Satisfies, Formula.Defined, Formula.denote, polarity,
    PartialObservation.primitives, PartialObservation.canonical, PartialObservation.complete,
    PrimitiveExpression.Atom.eval, hh, hl, hv, or_iff_not_imp_left]
  intro _
  exact ⟨⟨_, Iff.rfl⟩, ⟨_, Iff.rfl⟩⟩

/-- Ordinary attachment checks every live enclosing context. A temporal
`initially` wrapper would change this contract and must not be inserted. -/
theorem every_live_state {k : Nat} {U : Type u} (m : Structural.Core k)
    (τ : Trace (Fin k) U) (R : Constraints.IntegerRealization U) (contexts : Nat → Set U)
    (heads left value : CollectionExpr (Fin k) 0) :
    Formula.PartialAttached τ (.primitives m τ R) contexts (constant heads left value) ↔
      ∀ t c, c ∈ contexts t → c ∈ τ.live t →
        (constant heads left value).Satisfies τ (.primitives m τ R) true (.closed c) t := Iff.rfl

end Clafer.Behavioral.Initializers
