module

public import Clafer.Behavioral.Past
public import Clafer.Behavioral.InitializerCandidate

/-! # Birth tests for initializer lowering

Behavioral §5 Definitions 3–5 / §6.1 and the accepted initializer contract.
Issue #187 supplies the past extension; supplementary Haskell source is
gsdlab/clafer@186d8e0a350e4c8895b1c489eb587fa3a1bc2b61, Intermediate/Initializers.hs.
Stable declaration membership and ownership justify testing the captured head
in the preceding state. The RHS remains the original partial observation.
This proves guarded equations, not unrestricted strict object-language implication.
-/

@[expose] public section
namespace Clafer.Behavioral.Initializers.Past
universe u
variable {C : Type} {U : Type u}

-- [proof->req~behavioral-initializer-birth-test~1]
/-- A current head's declaration view must be stable; a constraint-filtered
set that changes membership while the object remains live is insufficient.
`guard` may be parent presence or another enclosing presence implied by the head. -/
theorem birth_iff_not_previous (τ : Trace C U) (heads : Nat → Set U)
    (selected : U → Prop) (P : U → Signal)
    (membership : ∀ t x, x ∈ heads t ↔ selected x ∧ x ∈ τ.live t)
    (guard : ∀ t x, x ∈ heads t → P x t)
    (t : Nat) (x : U) (current : x ∈ heads t) :
    τ.Starts t x ↔ ¬ Lifetime.previous (P x) (fun j => x ∈ heads j) t := by
  have role := ((membership t x).mp current).1
  have live := ((membership t x).mp current).2
  cases t with
  | zero => simp [Trace.starts_zero, Lifetime.previous, live]
  | succ t =>
    rw [Trace.starts_succ]
    change (x ∈ τ.live (t + 1) ∧ x ∉ τ.live t) ↔ ¬ (P x t ∧ x ∈ heads t)
    constructor
    · rintro ⟨_, absent⟩ ⟨_, head⟩
      exact absent ((membership t x).mp head).2
    · intro h
      refine ⟨live, ?_⟩
      intro old
      have head := (membership t x).mpr ⟨role, old⟩
      exact h ⟨guard t x head, head⟩

-- [impl->req~behavioral-initializer-birth-test~1]
/-- Quantification retains the head identity, and the RHS keeps its supplied
original parent/root environment. An inactive guard never demands definedness. -/
def Equations (heads : Nat → Set U) (P : U → Signal)
    (target : Nat → U → U) (rhs : Nat → U → Option (Set U)) : Prop :=
  ∀ t x, x ∈ heads t →
    (¬ Lifetime.previous (P x) (fun j => x ∈ heads j) t) → rhs t x = some {target t x}

-- [proof->req~behavioral-initializer-birth-test~1]
theorem equations_agree (τ : Trace C U) (heads : Nat → Set U)
    (selected : U → Prop) (P : U → Signal)
    (membership : ∀ t x, x ∈ heads t ↔ selected x ∧ x ∈ τ.live t)
    (guard : ∀ t x, x ∈ heads t → P x t)
    (target : Nat → U → U) (rhs : Nat → U → Option (Set U)) :
    Equations heads P target rhs ↔ Candidate.SingleBirths τ heads target rhs := by
  constructor
  · intro h t x hx birth
    exact h t x hx ((birth_iff_not_previous τ heads selected P membership guard t x hx).mp birth)
  · intro h t x hx fresh
    exact h t x hx ((birth_iff_not_previous τ heads selected P membership guard t x hx).mpr fresh)

/-- The birth test is independent of which valid enclosing presence guard is
used. This does not equate the general past operators under different lifetimes. -/
theorem enclosing_guard_agrees (τ : Trace C U) (heads : Nat → Set U)
    (selected : U → Prop) (P Q : U → Signal)
    (membership : ∀ t x, x ∈ heads t ↔ selected x ∧ x ∈ τ.live t)
    (guardP : ∀ t x, x ∈ heads t → P x t)
    (guardQ : ∀ t x, x ∈ heads t → Q x t)
    (target : Nat → U → U) (rhs : Nat → U → Option (Set U)) :
    Equations heads P target rhs ↔ Equations heads Q target rhs :=
  (equations_agree τ heads selected P membership guardP target rhs).trans
    (equations_agree τ heads selected Q membership guardQ target rhs).symm

-- [proof->req~behavioral-initializer-birth-test~1]
/-- A strict implication still requires its RHS domain even when its guard is
false. Therefore a mere birth-test equivalence cannot justify that translation
for arbitrary partial RHS observations. -/
theorem strict_implication_requires_rhs {A D : Nat → Type} {n : Nat}
    (τ : Trace C U) (O : PartialObservation A D U) (a : A n)
    (ρ : Environment U n) (t : Nat) (missing : O.atom a ρ t = none) :
    ¬ (Formula.implies (.not .truth) (.atom a)).Satisfies τ O true ρ t := by
  simp [Formula.Satisfies, Formula.Defined, missing]

end Clafer.Behavioral.Initializers.Past
