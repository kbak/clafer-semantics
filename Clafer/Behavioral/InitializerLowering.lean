module

public import Clafer.Behavioral.Initializers
public import Clafer.Behavioral.PartialLowering

/-! # Initializers in ordinary past/future core

Behavioral §5 Definitions 3–5 / §6.1 and the accepted initializer clocks.
Birth/end anchors expand into presence and ordinary temporal operators. Both
the source domain and its truth are lowered, so an inactive initializer does
not demand its RHS. Original-context RHS transport remains in the observation
adapter, including temporal conditions and inherited declaration clocks.
-/

@[expose] public section
namespace Clafer.Behavioral
universe u

namespace Core
variable {A D : Nat → Type} {C : Type} {U : Type u}

def birth {n} : Core A D n :=
  .and (.atom .contextPresent) (.not (.previous (.atom .contextPresent)))

def death {n} : Core A D n :=
  .and (.atom .contextPresent) (.next (.not (.atom .contextPresent)))

theorem birth_agrees (τ : Trace C U) (O : Observation A D U) {n}
    (ρ : Environment U n) (t : Nat) : (birth : Core A D n).eval τ O ρ t ↔ τ.Starts t ρ.this := by
  cases t <;> simp [birth, eval, Temporal.previous, Trace.starts_zero, Trace.starts_succ]

theorem death_agrees (τ : Trace C U) (O : Observation A D U) {n}
    (ρ : Environment U n) (t : Nat) : (death : Core A D n).eval τ O ρ t ↔ τ.Ends t ρ.this := Iff.rfl

-- [impl->req~behavioral-past-formulas~1]
noncomputable def expandAnchors {n} : Core A D n → Core A D n
  | .truth => .truth
  | .atom .starts => birth
  | .atom .ends => death
  | .atom a => .atom a
  | .not a => .not a.expandAnchors
  | .and a b => .and a.expandAnchors b.expandAnchors
  | .or a b => .or a.expandAnchors b.expandAnchors
  | .next a => .next a.expandAnchors
  | .eventually a => .eventually a.expandAnchors
  | .always a => .always a.expandAnchors
  | .strongUntil a b => .strongUntil a.expandAnchors b.expandAnchors
  | .weakUntil a b => .weakUntil a.expandAnchors b.expandAnchors
  | .previous a => .previous a.expandAnchors
  | .since a b => .since a.expandAnchors b.expandAnchors
  | .quant q d a => .quant q d a.expandAnchors
  | .letSet d a => .letSet d a.expandAnchors

noncomputable def AnchorFree {n} : Core A D n → Prop
  | .truth => True
  | .atom .starts | .atom .ends => False
  | .atom _ => True
  | .not a | .next a | .eventually a | .always a | .previous a
  | .quant _ _ a | .letSet _ a => a.AnchorFree
  | .and a b | .or a b | .strongUntil a b | .weakUntil a b | .since a b =>
      a.AnchorFree ∧ b.AnchorFree

-- [proof->req~behavioral-past-formulas~1]
theorem expandAnchors_free {n} (a : Core A D n) : a.expandAnchors.AnchorFree := by
  induction a with
  | atom a => cases a <;> simp [expandAnchors, birth, death, AnchorFree]
  | _ => simp_all [expandAnchors, AnchorFree]

theorem expandAnchors_agrees (τ : Trace C U) (O : Observation A D U) {n}
    (a : Core A D n) (ρ : Environment U n) (t : Nat) :
    a.expandAnchors.eval τ O ρ t ↔ a.eval τ O ρ t := by
  induction a generalizing t with
  | atom a =>
    cases a <;> simp only [expandAnchors, birth_agrees, death_agrees, eval]
  | _ => simp_all [expandAnchors, eval, Quantifier.eval, Temporal.next, Temporal.eventually,
      Temporal.always, Temporal.strongUntil, Temporal.weakUntil, Temporal.previous, Temporal.since]

end Core

namespace Initializers

-- [impl->req~behavioral-past-formulas~1]
/-- No initializer or lifetime-anchor operation remains in this core. The
explicit domain guard preserves the accepted inactive-RHS policy. -/
noncomputable def lowerCore {C V : Type} (o : Obligation C V) :
    Core (CheckedAtom (Equation V) (fun _ => Empty)) (fun _ => Empty) 0 :=
  ((expansion o).checkedCore true).expandAnchors

theorem lowerCore_anchorFree {C V : Type} (o : Obligation C V) : (lowerCore o).AnchorFree :=
  Core.expandAnchors_free _

-- [proof->req~behavioral-past-formulas~1]
theorem lowerCore_agrees {C V : Type} {U : Type u} (τ : Trace C U) (v : View U)
    (source : V → Transport.Value U (Set U) 0) (o : Obligation C V)
    (rootLive : ∀ t, τ.identities.root ∈ τ.live t) :
    (∀ t x, x ∈ attachments τ v o t → x ∈ τ.live t →
      (lowerCore o).eval τ (observation τ v source).checked (.closed x) t) ↔
      Meaning τ v source o := by
  simp only [lowerCore, Core.expandAnchors_agrees, Formula.checkedCore_agrees]
  exact expansion_agrees τ v source o rootLive

end Initializers
end Clafer.Behavioral
