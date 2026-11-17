module

public import Clafer.Behavioral.Modifiers
public import Clafer.Behavioral.InitializerLowering

/-! # Modifier obligations in the common temporal core

Behavioral §5 Definitions 3–5 and §§6.1–6.2 p.2:32, with the accepted D5
completion for finalref/finaltarget. Reuse the independent meanings and captured
adjacent-equality expansion in Modifiers. The output retains placement, ordinary
temporal operators, set observations and strict definedness checks. Its types
contain no modifier operation; birth/end atoms are also eliminated.
-/

@[expose] public section
namespace Clafer.Behavioral.Modifiers
universe u
variable {C : Type} {k : Nat} {U : Type u}

-- [impl->req~behavioral-modifiers~1]
/-- A resolved attachment and ordinary checked formula. Neither the formula,
its set observations nor its placement can encode a modifier constructor. -/
structure CoreObligation (C : Type) where
  placement : Placement C
  body : Core (CheckedAtom (SetAtom C) (SetExpr C)) (SetExpr C) 0

def CoreObligation.Holds (m : Structural.Core k) (τ : Trace (Fin k) U)
    (O : PartialObservation (SetAtom (Fin k)) (SetExpr (Fin k)) U)
    (item : CoreObligation (Fin k)) : Prop :=
  ∀ t x, x ∈ item.placement.contexts m τ t → x ∈ τ.live t →
    item.body.eval τ O.checked (.closed x) t

-- [impl->req~behavioral-modifiers~1]
-- [impl->req~behavioral-past-formulas~1]
/-- Erase each rich modifier through the existing expansion. In particular,
`final` emits both head and per-head reference stability, with no finalref left
for a later pass. Strict domains are translated before signed normalization. -/
noncomputable def lowerCore (d : C) (modifier : Modifier) : List (CoreObligation C) :=
  (expand d modifier).map fun item =>
    ⟨item.1, (item.2.checkedCore true).expandAnchors⟩

-- [proof->req~behavioral-modifiers~1]
theorem lowerCore_placements (d : C) (modifier : Modifier) :
    (lowerCore d modifier).map CoreObligation.placement = (expand d modifier).map Prod.fst := by
  simp [lowerCore]

theorem lowerCore_final (d : C) : lowerCore d .final =
    [⟨.all, ((stabilityExpansion (.heads d)).checkedCore true).expandAnchors⟩,
     ⟨.heads d, ((stabilityExpansion (.reference d)).checkedCore true).expandAnchors⟩] := rfl

-- [proof->req~behavioral-past-formulas~1]
theorem lowerCore_anchorFree (d : C) (modifier : Modifier)
    (item : CoreObligation C) (hi : item ∈ lowerCore d modifier) : item.body.AnchorFree := by
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp hi
  exact Core.expandAnchors_free _

-- [proof->req~behavioral-qualification~1]
-- [proof->req~behavioral-environments~1]
/-- Arbitrary partial observations retain exactly the expanded source domain,
including strict implication and the environment created by each capture. -/
theorem lowerCore_partial_agrees (m : Structural.Core k) (τ : Trace (Fin k) U)
    (O : PartialObservation (SetAtom (Fin k)) (SetExpr (Fin k)) U)
    (d : Fin k) (modifier : Modifier) :
    (∀ item ∈ lowerCore d modifier, item.Holds m τ O) ↔
      ∀ item ∈ expand d modifier, item.2.PartialAttached τ O (item.1.contexts m τ) := by
  simp only [lowerCore, List.forall_mem_map, CoreObligation.Holds,
    Core.expandAnchors_agrees, Formula.checkedCore_agrees, Formula.PartialAttached]

/-- The existing inherited-reference set adapter is total. Arbitrary partial
adapters use lowerCore_partial_agrees instead of silently filling missing values. -/
noncomputable def coreObservation (m : Structural.Core k) (τ : Trace (Fin k) U) :
    PartialObservation (SetAtom (Fin k)) (SetExpr (Fin k)) U :=
  .ofTotal (.sets m.toEffectiveCore (Structural.observed m τ))

-- [proof->req~behavioral-modifiers~1]
/-- Equivalence to independent Initial/FinalHeads/FinalRef/FinalTarget, with
structural validity discharging inherited owners and parent-presence guards. -/
theorem lowerCore_agrees (m : Structural.Core k) (τ : Trace (Fin k) U)
    (h : Structural.Valid m τ) (d : Fin k) (modifier : Modifier) :
    (∀ item ∈ lowerCore d modifier, item.Holds m τ (coreObservation m τ)) ↔
      meaning m τ d modifier := by
  rw [lowerCore_partial_agrees]
  simp only [Formula.PartialAttached, coreObservation, Formula.total_agrees]
  exact expand_agrees m τ h d modifier

-- [impl->req~behavioral-qualification~1]
/-- Every effective annotation contributes its complete lowered bundle. -/
def LoweredHolds (m : Structural.Core k) (τ : Trace (Fin k) U)
    (declared : Fin k → Set Modifier)
    (O : PartialObservation (SetAtom (Fin k)) (SetExpr (Fin k)) U) : Prop :=
  ∀ d modifier, Effective m.family declared d modifier →
    ∀ item ∈ lowerCore d modifier, item.Holds m τ O

-- [proof->req~behavioral-modifiers~1]
-- [proof->req~behavioral-qualification~1]
theorem loweredHolds_iff (m : Structural.Core k) (τ : Trace (Fin k) U)
    (h : Structural.Valid m τ) (declared : Fin k → Set Modifier) :
    LoweredHolds m τ declared (coreObservation m τ) ↔ Holds m τ declared := by
  simp only [LoweredHolds, lowerCore_agrees m τ h]
  constructor
  · intro hm d
    exact ⟨hm d .initial, hm d .final, hm d .finalref, hm d .finaltarget⟩
  · intro hm d modifier
    cases modifier with
    | initial => exact (hm d).1
    | final => exact (hm d).2.1
    | finalref => exact (hm d).2.2.1
    | finaltarget => exact (hm d).2.2.2

end Clafer.Behavioral.Modifiers
