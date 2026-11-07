module

public import Clafer.Behavioral.Lowering
public import Clafer.Behavioral.PrimitiveExpression

/-! # Strict partial observations and signed temporal satisfaction

Adopted #126 D3 integration: all Boolean operands and quantified members must
be defined. Temporal operands must be defined throughout the remaining active
parent interval (next only at its next state). Cancellation and inactive lifetime
anchors introduce no operand obligation. This domain is separate from signed
truth; no missing result is interpreted as source false, true, or zero.
-/

@[expose] public section
namespace Clafer.Behavioral
universe u

-- [impl->req~behavioral-reference-atoms~1]
structure PartialObservation (A D : Nat → Type) (U : Type u) where
  atom : ∀ {n}, A n → Environment U n → Nat → Option Prop
  domain : ∀ {n}, D n → Environment U n → Nat → Option (Set U)

namespace PartialObservation
variable {A D : Nat → Type} {U : Type u}

def ofTotal (O : Observation A D U) : PartialObservation A D U where
  atom a ρ t := some (O.atom a ρ t)
  domain a ρ t := some (O.domain a ρ t)

/-- Arbitrary completion for reuse of total denotation. `Formula.Defined`
guards its use, and `extension_agrees` proves completion independence. -/
def complete (O : PartialObservation A D U) (fallback : Observation A D U) : Observation A D U where
  atom a ρ t := (O.atom a ρ t).getD (fallback.atom a ρ t)
  domain a ρ t := (O.domain a ρ t).getD (fallback.domain a ρ t)

def Extends (O : PartialObservation A D U) (T : Observation A D U) : Prop :=
  (∀ n (a : A n) ρ t p, O.atom a ρ t = some p → (T.atom a ρ t ↔ p)) ∧
  (∀ n (d : D n) ρ t S, O.domain d ρ t = some S → T.domain d ρ t = S)

theorem complete_extends (O : PartialObservation A D U) (fallback : Observation A D U) :
    O.Extends (O.complete fallback) := by
  constructor
  · intro n a ρ t p h; simp [complete, h]
  · intro n a ρ t S h; simp [complete, h]

def canonical (O : PartialObservation A D U) : Observation A D U :=
  O.complete ⟨fun _ _ _ => False, fun _ _ _ => ∅⟩

noncomputable def primitives {k : Nat} (m : Structural.Core k) (τ : Trace (Fin k) U)
    (R : Constraints.IntegerRealization U) :
    PartialObservation (PrimitiveExpression.Atom (Fin k)) (CollectionExpr (Fin k)) U where
  atom a ρ t := a.eval m.toEffectiveCore (Structural.observed m τ) R ρ t
  domain a ρ t := PrimitiveExpression.collection m.toEffectiveCore (Structural.observed m τ) R ρ t a

end PartialObservation

namespace Formula
variable {A D : Nat → Type} {C : Type} {U : Type u}

-- [impl->req~behavioral-reference-atoms~1]
noncomputable def Defined (τ : Trace C U) (O : PartialObservation A D U) {n} :
    Formula A D n → Environment U n → Nat → Prop
  | .truth, _, _ => True
  | .atom a, ρ, t => ∃ p, O.atom a ρ t = some p
  | .not a, ρ, t => a.Defined τ O ρ t
  | .and a b, ρ, t | .or a b, ρ, t | .implies a b, ρ, t
  | .iff a b, ρ, t | .xor a b, ρ, t => a.Defined τ O ρ t ∧ b.Defined τ O ρ t
  | .ite c a b, ρ, t => c.Defined τ O ρ t ∧ a.Defined τ O ρ t ∧ b.Defined τ O ρ t
  | .next a, ρ, t => τ.ParentPresent ρ.this (t + 1) → a.Defined τ O ρ (t + 1)
  | .eventually a, ρ, t | .always a, ρ, t =>
      ∀ j, t ≤ j → Lifetime.Through (τ.ParentPresent ρ.this) t j → a.Defined τ O ρ j
  | .strongUntil a b, ρ, t | .weakUntil a b, ρ, t =>
      ∀ j, t ≤ j → Lifetime.Through (τ.ParentPresent ρ.this) t j →
        a.Defined τ O ρ j ∧ b.Defined τ O ρ j
  | .initially a, ρ, t => τ.Starts t ρ.this → a.Defined τ O ρ t
  | .finally a, ρ, t => τ.Ends t ρ.this → a.Defined τ O ρ t
  | .quant _ d a, ρ, t => ∃ S, O.domain d ρ t = some S ∧
      ∀ x ∈ S, a.Defined τ O (ρ.push {x}) t
  | .letSet d a, ρ, t => ∃ S, O.domain d ρ t = some S ∧ a.Defined τ O (ρ.push S) t

-- [impl->req~behavioral-reference-atoms~1]
def Satisfies (τ : Trace C U) (O : PartialObservation A D U) {n}
    (a : Formula A D n) (positive : Bool) (ρ : Environment U n) (t : Nat) : Prop :=
  a.Defined τ O ρ t ∧ a.denote τ O.canonical positive ρ t

def PartialAttached (τ : Trace C U) (O : PartialObservation A D U)
    (contexts : Nat → Set U) (a : Formula A D 0) : Prop :=
  ∀ t c, c ∈ contexts t → c ∈ τ.live t → a.Satisfies τ O true (.closed c) t

-- [proof->req~behavioral-reference-atoms~1]
theorem undefined_neither (τ : Trace C U) (O : PartialObservation A D U) {n}
    (a : Formula A D n) (ρ : Environment U n) (t : Nat) (h : ¬ a.Defined τ O ρ t) :
    ¬ a.Satisfies τ O true ρ t ∧ ¬ a.Satisfies τ O false ρ t :=
  ⟨fun ht => h ht.1, fun hf => h hf.1⟩

theorem total_defined (τ : Trace C U) (O : Observation A D U) {n}
    (a : Formula A D n) (ρ : Environment U n) (t : Nat) :
    a.Defined τ (.ofTotal O) ρ t := by
  induction a generalizing t <;> simp_all [Defined, PartialObservation.ofTotal]
  exact ⟨_, Iff.rfl⟩

theorem total_agrees (τ : Trace C U) (O : Observation A D U) {n}
    (a : Formula A D n) (s : Bool) (ρ : Environment U n) (t : Nat) :
    a.Satisfies τ (.ofTotal O) s ρ t ↔ a.denote τ O s ρ t := by
  have hc : (PartialObservation.ofTotal O).canonical = O := rfl
  simp only [Satisfies, hc, total_defined, true_and]

end Formula

namespace Lifetime
variable {P a b c d : Signal} {t : Nat}

theorem next_congr (h : P (t + 1) → (a (t + 1) ↔ b (t + 1))) :
    next P a t ↔ next P b t :=
  ⟨fun ha hp => (h hp).mp (ha hp), fun hb hp => (h hp).mpr (hb hp)⟩

theorem always_congr (h : ∀ j, t ≤ j → Through P t j → (a j ↔ b j)) :
    always P a t ↔ always P b t :=
  ⟨fun ha j hj hp => (h j hj hp).mp (ha j hj hp),
    fun hb j hj hp => (h j hj hp).mpr (hb j hj hp)⟩

theorem eventually_congr (h : ∀ j, t ≤ j → Through P t j → (a j ↔ b j)) :
    eventually P a t ↔ eventually P b t := by
  unfold eventually
  exact or_congr Iff.rfl (exists_congr fun j => and_congr_right fun hj =>
    and_congr_right fun hp => h j hj hp)

theorem until_congr (ha : ∀ j, t ≤ j → Through P t j → (a j ↔ c j))
    (hb : ∀ j, t ≤ j → Through P t j → (b j ↔ d j)) :
    strongUntil P a b t ↔ strongUntil P c d t := by
  have forward {a b c d : Signal}
      (ha : ∀ j, t ≤ j → Through P t j → (a j ↔ c j))
      (hb : ∀ j, t ≤ j → Through P t j → (b j ↔ d j)) :
      strongUntil P a b t → strongUntil P c d t := by
    rintro ⟨j, hj, stop, before⟩
    have through : ∀ k, t ≤ k → k < j → Through P t k := by
      intro k hk hkj l hl hlk; exact (before l hl (lt_of_le_of_lt hlk hkj)).1
    refine ⟨j, hj, ?_, fun k hk hkj =>
      ⟨(before k hk hkj).1, (ha k hk (through k hk hkj)).mp (before k hk hkj).2⟩⟩
    by_cases hp : P j
    · have hthrough : Through P t j := by
        intro k hk hkj
        rcases eq_or_lt_of_le hkj with rfl | hlt
        · exact hp
        · exact (before k hk hlt).1
      exact Or.inr ((hb j hj hthrough).mp (stop.resolve_left (not_not_intro hp)))
    · exact Or.inl hp
  exact ⟨forward ha hb, forward (fun j hj hp => (ha j hj hp).symm)
    (fun j hj hp => (hb j hj hp).symm)⟩

theorem weakUntil_congr (ha : ∀ j, t ≤ j → Through P t j → (a j ↔ c j))
    (hb : ∀ j, t ≤ j → Through P t j → (b j ↔ d j)) :
    weakUntil P a b t ↔ weakUntil P c d t :=
  or_congr (always_congr ha) (until_congr ha hb)

end Lifetime
end Clafer.Behavioral
