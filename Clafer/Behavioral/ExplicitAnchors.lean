module

public import Clafer.Behavioral.InitializerLowering

/-! # Explicit lifetime guards before temporal lowering

Behavioral §§5–6, Definitions 4–5. The surface birth and death tests use the
live-filtered context and parent-bounded temporal operators. Their ordinary
Boolean interpretation is compared to the independent lifetime anchors.
-/

@[expose] public section
namespace Clafer.Behavioral.Formula
universe u
variable {A D : Nat → Type} {C : Type} {U : Type u}

/-- Replace only anchors, retaining all other surface operators and binders. -/
-- [impl->req~behavioral-past-formulas~1]
noncomputable def explicitAnchors (present : ∀ {k}, A k) {n} : Formula A D n → Formula A D n
  | .truth => .truth
  | .atom a => .atom a
  | .not a => .not (a.explicitAnchors present)
  | .next a => .next (a.explicitAnchors present)
  | .eventually a => .eventually (a.explicitAnchors present)
  | .always a => .always (a.explicitAnchors present)
  | .previous a => .previous (a.explicitAnchors present)
  | .weakPrevious a => .weakPrevious (a.explicitAnchors present)
  | .once a => .once (a.explicitAnchors present)
  | .historically a => .historically (a.explicitAnchors present)
  | .and a b => .and (a.explicitAnchors present) (b.explicitAnchors present)
  | .or a b => .or (a.explicitAnchors present) (b.explicitAnchors present)
  | .implies a b => .implies (a.explicitAnchors present) (b.explicitAnchors present)
  | .iff a b => .iff (a.explicitAnchors present) (b.explicitAnchors present)
  | .xor a b => .xor (a.explicitAnchors present) (b.explicitAnchors present)
  | .strongUntil a b => .strongUntil (a.explicitAnchors present) (b.explicitAnchors present)
  | .weakUntil a b => .weakUntil (a.explicitAnchors present) (b.explicitAnchors present)
  | .since a b => .since (a.explicitAnchors present) (b.explicitAnchors present)
  | .triggered a b => .triggered (a.explicitAnchors present) (b.explicitAnchors present)
  | .ite c a b => .ite (c.explicitAnchors present) (a.explicitAnchors present) (b.explicitAnchors present)
  | .initially a =>
    .implies (.and (.atom present) (.not (.previous (.atom present)))) (a.explicitAnchors present)
  | .finally a =>
    .implies (.and (.atom present) (.next (.not (.atom present)))) (a.explicitAnchors present)
  | .quant q d a => .quant q d (a.explicitAnchors present)
  | .letSet d a => .letSet d (a.explicitAnchors present)

-- [proof->req~behavioral-past-formulas~1]
theorem explicitAnchors_free (present : ∀ {k}, A k) {n} (a : Formula A D n) :
    (a.explicitAnchors present).lower.AnchorFree := by
  induction a <;> simp_all [explicitAnchors, lower, Core.AnchorFree]

variable (τ : Trace C U) (O : Observation A D U) (present : ∀ {k}, A k)
variable (observes : ∀ {k} (ρ : Environment U k) t, O.atom present ρ t ↔ ρ.this ∈ τ.live t)
variable (owned : ∀ x t, x ∈ τ.live t → τ.ParentPresent x t)
include observes owned

-- [proof->req~behavioral-past-formulas~1]
theorem explicitAnchors_raw {n} (a : Formula A D n) :
    (a.explicitAnchors present).raw τ O = a.raw τ O := by
  induction a with
  | initially a ih =>
    funext ρ t
    simp only [explicitAnchors, raw, ih, observes]
    cases t with
    | zero => simp [Lifetime.previous, Trace.starts_zero]
    | succ k =>
      simp only [Lifetime.previous, Trace.starts_succ]
      have := owned ρ.this k
      apply propext
      tauto
  | «finally» a ih =>
    funext ρ t
    simp only [explicitAnchors, raw, ih, Lifetime.next, Trace.Ends, observes]
    have := owned ρ.this (t + 1)
    apply propext
    tauto
  | _ => funext ρ t; simp only [explicitAnchors, raw, *]

/-- Compare meanings after the two orders of lowering. A valid trace supplies
the ownership premise via `Trace.context_parent_present`. -/
-- [proof->req~behavioral-past-formulas~1]
theorem explicitAnchors_lower_agrees {n} (a : Formula A D n) (ρ : Environment U n) (t : Nat) :
    (a.explicitAnchors present).lower.eval τ O ρ t ↔ a.lower.expandAnchors.eval τ O ρ t := by
  rw [Core.expandAnchors_agrees, lower_agrees, lower_agrees,
    explicitAnchors_raw τ O present observes owned]

end Clafer.Behavioral.Formula
