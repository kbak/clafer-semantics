module

public import Clafer.Behavioral.PartialObservation

/-!
# Set capture and moving a binding across next

Behavioral paper §5 Definition 4 and §6.1, with adopted D1/D3. These are
consequences of the existing captured-value meaning, not a named-syntax
substitution theorem. In particular, lexical capture avoidance alone does not
justify moving evaluation of a domain across a temporal operator.
-/

@[expose] public section
namespace Clafer.Behavioral.Formula
universe u
variable {A D : Nat → Type} {C : Type} {U : Type u} {n : Nat}

-- [proof->req~behavioral-environments~1]
/-- The body sees the value at the binding state, including in temporal uses. -/
theorem letSet_capture (τ : Trace C U) (O : Observation A D U)
    (d : D n) (a : Formula A D (n + 1)) (s : Bool) (ρ : Environment U n) (t : Nat) :
    (letSet d a).denote τ O s ρ t ↔
      a.denote τ O s (ρ.push (O.domain d ρ t)) t := Iff.rfl

-- [proof->req~behavioral-environments~1]
-- [proof->req~behavioral-formula-denotation~1]
/-- Moving capture through next is sound when the two domain values agree.
No body restriction or context reattachment is needed; both source signs work. -/
theorem letSet_next_of_stable (τ : Trace C U) (O : Observation A D U)
    (d : D n) (a : Formula A D (n + 1)) (s : Bool) (ρ : Environment U n) (t : Nat)
    (stable : O.domain d ρ (t + 1) = O.domain d ρ t) :
    (letSet d (.next a)).denote τ O s ρ t ↔
      (next (.letSet d a)).denote τ O s ρ t := by
  simp only [denote, Lifetime.next, Environment.push_this, stable]

-- [proof->req~behavioral-reference-atoms~1]
/-- An unused RHS must still be defined. Erasing it can change the domain even
when no temporal operator or lexical name conflict occurs. -/
theorem letSet_truth_defined (τ : Trace C U) (O : PartialObservation A D U)
    (d : D n) (ρ : Environment U n) (t : Nat) :
    (letSet d truth).Defined τ O ρ t ↔ ∃ S, O.domain d ρ t = some S := by
  simp [Defined]

theorem letSet_undefined_neither (τ : Trace C U) (O : PartialObservation A D U)
    (d : D n) (a : Formula A D (n + 1)) (ρ : Environment U n) (t : Nat)
    (missing : O.domain d ρ t = none) :
    ¬ (letSet d a).Satisfies τ O true ρ t ∧
      ¬ (letSet d a).Satisfies τ O false ρ t := by
  apply undefined_neither
  simp [Defined, missing]

end Clafer.Behavioral.Formula
