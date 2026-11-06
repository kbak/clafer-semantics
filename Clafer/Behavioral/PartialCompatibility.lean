module

public import Clafer.Behavioral.PartialObservation

/-! Completion independence on the strict domain, including counting barriers,
parent cancellation, and every captured quantifier/let environment. -/

@[expose] public section
namespace Clafer.Behavioral
universe u

theorem Quantifier.congr {U : Type u} (q : Quantifier) (S : Set U) {a b : U → Prop}
    (h : ∀ x ∈ S, a x ↔ b x) : q.eval S a ↔ q.eval S b := by
  have pairs : ∀ x, (x ∈ S ∧ a x) ↔ (x ∈ S ∧ b x) :=
    fun x => and_congr_right (h x)
  cases q <;> simp (config := {contextual := true}) only [Quantifier.eval, h, pairs]

namespace Formula
variable {A D : Nat → Type} {C : Type} {U : Type u}
  (τ : Trace C U) (O : PartialObservation A D U) (L R : Observation A D U)
  (left : O.Extends L) (right : O.Extends R)

-- [proof->req~behavioral-reference-atoms~1]
include left right in
theorem raw_extension_agrees {n} (a : Formula A D n) (ρ : Environment U n) (t : Nat)
    (defined : a.Defined τ O ρ t) : a.raw τ L ρ t ↔ a.raw τ R ρ t := by
  induction a generalizing t with
  | truth => rfl
  | atom a =>
    obtain ⟨p, hp⟩ := defined
    exact (left.1 _ a ρ t p hp).trans (right.1 _ a ρ t p hp).symm
  | not a ih => exact not_congr (ih ρ t defined)
  | and a b iha ihb | or a b iha ihb | implies a b iha ihb
  | iff a b iha ihb | xor a b iha ihb =>
    simp only [raw, iha ρ t defined.1, ihb ρ t defined.2]
  | ite c a b ihc iha ihb =>
    simp only [raw, ihc ρ t defined.1, iha ρ t defined.2.1, ihb ρ t defined.2.2]
  | next a ih => exact Lifetime.next_congr (fun hp => ih ρ (t + 1) (defined hp))
  | eventually a ih => exact Lifetime.eventually_congr (fun j hj hp => ih ρ j (defined j hj hp))
  | always a ih => exact Lifetime.always_congr (fun j hj hp => ih ρ j (defined j hj hp))
  | strongUntil a b iha ihb =>
    exact Lifetime.until_congr (fun j hj hp => iha ρ j (defined j hj hp).1)
      (fun j hj hp => ihb ρ j (defined j hj hp).2)
  | weakUntil a b iha ihb =>
    exact Lifetime.weakUntil_congr (fun j hj hp => iha ρ j (defined j hj hp).1)
      (fun j hj hp => ihb ρ j (defined j hj hp).2)
  | initially a ih | «finally» a ih => exact imp_congr_right (fun ht => ih ρ t (defined ht))
  | quant q d a ih =>
    obtain ⟨S, hs, bodies⟩ := defined
    simp only [raw, left.2 _ d ρ t S hs, right.2 _ d ρ t S hs]
    exact q.congr S (fun x hx => ih (ρ.push {x}) t (bodies x hx))
  | letSet d a ih =>
    obtain ⟨S, hs, body⟩ := defined
    simp only [raw, left.2 _ d ρ t S hs, right.2 _ d ρ t S hs]
    exact ih (ρ.push S) t body

-- [proof->req~behavioral-reference-atoms~1]
include left right in
theorem extension_agrees {n} (a : Formula A D n) (s : Bool) (ρ : Environment U n) (t : Nat)
    (defined : a.Defined τ O ρ t) : a.denote τ L s ρ t ↔ a.denote τ R s ρ t := by
  induction a generalizing s t with
  | truth => rfl
  | atom a =>
    obtain ⟨p, hp⟩ := defined
    have he := (left.1 _ a ρ t p hp).trans (right.1 _ a ρ t p hp).symm
    simp only [denote, polarity, he]
  | not a ih => exact ih (!s) ρ t defined
  | and a b iha ihb | or a b iha ihb | implies a b iha ihb
  | iff a b iha ihb | xor a b iha ihb =>
    cases s <;> simp only [denote, Bool.false_eq_true, ite_true, ite_false,
      iha true ρ t defined.1, iha false ρ t defined.1,
      ihb true ρ t defined.2, ihb false ρ t defined.2]
  | ite c a b ihc iha ihb =>
    cases s <;> simp only [denote, Bool.false_eq_true, ite_true, ite_false,
      ihc true ρ t defined.1, ihc false ρ t defined.1,
      iha true ρ t defined.2.1, iha false ρ t defined.2.1,
      ihb true ρ t defined.2.2, ihb false ρ t defined.2.2]
  | next a ih => exact Lifetime.next_congr (fun hp => ih s ρ (t + 1) (defined hp))
  | eventually a ih =>
    cases s
    · exact Lifetime.always_congr (fun j hj hp => ih false ρ j (defined j hj hp))
    · exact Lifetime.eventually_congr (fun j hj hp => ih true ρ j (defined j hj hp))
  | always a ih =>
    cases s
    · exact Lifetime.eventually_congr (fun j hj hp => ih false ρ j (defined j hj hp))
    · exact Lifetime.always_congr (fun j hj hp => ih true ρ j (defined j hj hp))
  | strongUntil a b iha ihb =>
    cases s
    · exact Lifetime.weakUntil_congr (fun j hj hp => ihb false ρ j (defined j hj hp).2)
        (fun j hj hp => and_congr (iha false ρ j (defined j hj hp).1)
          (ihb false ρ j (defined j hj hp).2))
    · exact Lifetime.until_congr (fun j hj hp => iha true ρ j (defined j hj hp).1)
        (fun j hj hp => ihb true ρ j (defined j hj hp).2)
  | weakUntil a b iha ihb =>
    cases s
    · exact Lifetime.until_congr (fun j hj hp => ihb false ρ j (defined j hj hp).2)
        (fun j hj hp => and_congr (iha false ρ j (defined j hj hp).1)
          (ihb false ρ j (defined j hj hp).2))
    · exact Lifetime.weakUntil_congr (fun j hj hp => iha true ρ j (defined j hj hp).1)
        (fun j hj hp => ihb true ρ j (defined j hj hp).2)
  | initially a ih | «finally» a ih => exact imp_congr_right (fun ht => ih s ρ t (defined ht))
  | quant q d a ih =>
    obtain ⟨S, hs, bodies⟩ := defined
    have dl := left.2 _ d ρ t S hs
    have dr := right.2 _ d ρ t S hs
    have signed (s : Bool) (x : U) (hx : x ∈ S) := ih s (ρ.push {x}) t (bodies x hx)
    have pairs (s : Bool) (x : U) : (x ∈ S ∧ a.denote τ L s (ρ.push {x}) t) ↔
        (x ∈ S ∧ a.denote τ R s (ρ.push {x}) t) := and_congr_right (signed s x)
    have rawAgree (q : Quantifier) := q.congr S (fun x hx =>
      raw_extension_agrees τ O L R left right a (ρ.push {x}) t (bodies x hx))
    cases q <;> cases s <;>
      simp (config := {contextual := true}) only [denote, dl, dr, Bool.false_eq_true,
        ite_true, ite_false, signed, pairs, polarity, rawAgree]
  | letSet d a ih =>
    obtain ⟨S, hs, body⟩ := defined
    simp only [denote, left.2 _ d ρ t S hs, right.2 _ d ρ t S hs]
    exact ih s (ρ.push S) t body

include right in
theorem satisfies_iff_extension {n} (a : Formula A D n) (s : Bool)
    (ρ : Environment U n) (t : Nat) :
    a.Satisfies τ O s ρ t ↔ a.Defined τ O ρ t ∧ a.denote τ R s ρ t := by
  apply and_congr_right
  intro hd
  exact extension_agrees τ O O.canonical R (O.complete_extends _) right a s ρ t hd

/-- The accepted normalization/lowering theorem remains usable with its exact
definedness obligation; lowering alone is not evidence that a formula is defined. -/
theorem satisfies_iff_lowered {n} (a : Formula A D n) (s : Bool)
    (ρ : Environment U n) (t : Nat) :
    a.Satisfies τ O s ρ t ↔ a.Defined τ O ρ t ∧ (a.normalize s).lower.eval τ O.canonical ρ t := by
  exact and_congr_right (fun _ => (normalize_lower_agrees τ O.canonical a s ρ t).symm)

end Formula
end Clafer.Behavioral
