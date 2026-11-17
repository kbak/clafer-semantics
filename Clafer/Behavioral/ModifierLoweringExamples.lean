module

public import Clafer.Behavioral.ModifierLowering
public import Clafer.Behavioral.ModifierBoundaryExamples

/-! # Generated finality cores and distinguishing mutations

Behavioral §5 Definitions 3–5 / §§6.1–6.2 p.2:32, with the accepted D5
reference-modifier completion. All structural fixtures below reuse their full
admission proofs. Direct and inherited references share the same tests.
-/

@[expose] public section
namespace Clafer.Behavioral.ModifierLoweringExamples
open Modifiers ModifierBoundaryExamples ReferenceObservation

private instance (c : Case) (i : Fin 3) (p y : Fin 9) : Decidable (targetAt c i p y) := by
  unfold targetAt refAt
  infer_instance

def accepts (b : Bool) (c : Case) (modifier : Modifier) : Prop :=
  ∀ item ∈ lowerCore (2 : Fin 5) modifier,
    item.Holds (model b) (fixture b c).unfold (coreObservation (model b) (fixture b c).unfold)

theorem accepts_iff (b : Bool) (c : Case) (modifier : Modifier) :
    accepts b c modifier ↔ meaning (model b) (fixture b c).unfold 2 modifier :=
  lowerCore_agrees _ _ (admitted b c).2 _ _

-- [utest->req~behavioral-modifiers~1]
theorem replacement_core (b : Bool) :
    accepts b .replace .finalref ∧ accepts b .replace .finaltarget ∧
    ¬ accepts b .replace .final := by
  simp only [accepts_iff, meaning]
  exact ⟨(replacement_both b).1, (replacement_both b).2, replacement_not_final b⟩

-- [utest->req~behavioral-modifiers~1]
theorem swap_core (b : Bool) :
    accepts b .swap .finaltarget ∧ ¬ accepts b .swap .finalref ∧ ¬ accepts b .swap .final := by
  simp only [accepts_iff, meaning]
  exact ⟨(swap_target_only b).1, (swap_target_only b).2, fun h => (swap_target_only b).2 h.2⟩

-- [utest->req~behavioral-modifiers~1]
theorem additions_losses_core (b : Bool) :
    accepts b .addTarget .finalref ∧ ¬ accepts b .addTarget .finaltarget ∧
    accepts b .loseTarget .finalref ∧ ¬ accepts b .loseTarget .finaltarget := by
  simp only [accepts_iff, meaning]
  exact ⟨(adds_target_only b).1, (adds_target_only b).2,
    (loses_target_only b).1, (loses_target_only b).2⟩

-- [utest->req~behavioral-modifiers~1]
theorem repeated_bag_targets_core (b : Bool) :
    bagTargets .bag 0 = {6, 6, 7} ∧ bagTargets .bag 1 = {6, 7, 7} ∧
    accepts b .bag .finaltarget :=
  ⟨(bag_multiplicity b).1, (bag_multiplicity b).2.1,
    (accepts_iff b .bag .finaltarget).mpr (bag_multiplicity b).2.2.1⟩

-- [utest->req~behavioral-qualification~1]
theorem effective_core (b : Bool) :
    LoweredHolds (model b) (fixture b .replace).unfold (annotations b)
      (coreObservation (model b) (fixture b .replace).unfold) ∧
    ¬ LoweredHolds (model b) (fixture b .swap).unfold (annotations b)
      (coreObservation (model b) (fixture b .swap).unfold) ∧
    ¬ LoweredHolds (model b) (fixture b .loseTarget).unfold (annotations b)
      (coreObservation (model b) (fixture b .loseTarget).unfold) := by
  simp only [loweredHolds_iff _ _ (admitted _ _).2]
  exact ⟨(combined_replacement b).1, (neither_modifier_can_be_dropped b).1,
    (neither_modifier_can_be_dropped b).2⟩

-- [utest->req~behavioral-environments~1]
-- [utest->req~behavioral-modifiers~1]
theorem lifetime_resets_core (b : Bool) :
    LoweredHolds (model b) (fixture b .headGap).unfold (annotations b)
      (coreObservation (model b) (fixture b .headGap).unfold) ∧
    LoweredHolds (model b) (fixture b .parentGap).unfold (annotations b)
      (coreObservation (model b) (fixture b .parentGap).unfold) := by
  simp only [loweredHolds_iff _ _ (admitted _ _).2]
  exact ⟨(head_gap_resets b).1, (parent_gap_resets b).1⟩

-- [utest->req~behavioral-modifiers~1]
theorem shallow_core :
    (∀ item ∈ lowerCore (4 : Fin 8) .final,
      item.Holds (StructuralExamples.model false false) (StructuralExamples.trace false)
        (coreObservation (StructuralExamples.model false false) (StructuralExamples.trace false))) ∧
    ¬ FinalRef (StructuralExamples.model false false) (StructuralExamples.trace false) 5 :=
  ⟨(lowerCore_agrees _ _ (StructuralExamples.admitted false false).2 _ _).mpr
    ModifierExamples.inherited_shallow_final, ModifierExamples.inherited_ref_mutation⟩

/-- Incorrect weakening: forbid new targets but allow old targets to vanish. -/
def noAdditions (v : View C) : Formula (SetAtom C) (SetExpr C) 0 :=
  .letSet v.expression (.next (.implies (.atom (.inhabited .this))
    (.atom (.subset v.expression (.var 0)))))

/-- Incorrect lifetime: source next alone follows the attachment's parent,
so this loses the attachment-survival guard. -/
def parentLifetimeOnly (v : View C) : Formula (SetAtom C) (SetExpr C) 0 :=
  .letSet v.expression (.next (.atom (.equal (.var 0) v.expression)))

private theorem noAdditions_step (b : Bool) (c : Case) (p : Fin 9) (t : Nat) :
    (noAdditions (.targets (2 : Fin 5))).denote (fixture b c).unfold
      (.sets (model b).toEffectiveCore (Structural.observed (model b) (fixture b c).unfold))
      true (.closed p) t ↔
    (p ∈ (fixture b c).unfold.live (t + 1) →
      targets (Structural.current (model b) (fixture b c).unfold (t + 1)) 2 p ⊆
        targets (Structural.current (model b) (fixture b c).unfold t) 2 p) := by
  have cap := View.expression_capture (.closed p)
    ((View.targets 2).value (model b) (fixture b c).unfold p t)
    (model b).toEffectiveCore (Structural.observed (model b) (fixture b c).unfold)
    (View.targets 2) (t + 1)
  simp only [noAdditions, Formula.denote, ↓reduceIte, Observation.sets,
    SetAtom.eval, Lifetime.next, polarity, SetExpr.eval, Environment.push_this,
    Environment.push_zero, Environment.closed]
  change (_ → ¬ ({x | x = p ∧ x ∈ (fixture b c).unfold.live (t + 1)} : Set (Fin 9)).Nonempty ∨
    (View.targets 2).expression.eval _ _
      ((Environment.closed p).push ((View.targets 2).value (model b) (fixture b c).unfold p t))
      (t + 1) ⊆ (View.targets 2).value (model b) (fixture b c).unfold p t) ↔ _
  rw [cap]
  have present : ({x | x = p ∧ x ∈ (fixture b c).unfold.live (t + 1)} : Set (Fin 9)).Nonempty ↔
      p ∈ (fixture b c).unfold.live (t + 1) :=
    ⟨fun ⟨_, hx, hl⟩ => hx ▸ hl, fun hp => ⟨p, rfl, hp⟩⟩
  rw [present]
  change ((fixture b c).unfold.ParentPresent p (t + 1) →
    p ∉ (fixture b c).unfold.live (t + 1) ∨
    (View.targets 2).value (model b) (fixture b c).unfold p (t + 1) ⊆
      (View.targets 2).value (model b) (fixture b c).unfold p t) ↔ _
  rw [targets_value _ _ (admitted b c).2, targets_value _ _ (admitted b c).2]
  constructor
  · intro h hp
    exact (h (Structural.Valid.context_parent_present _ _ (admitted b c).2 hp)).resolve_left
      (not_not_intro hp)
  · intro h _
    classical
    exact (em (p ∈ (fixture b c).unfold.live (t + 1))).elim
      (fun hp => Or.inr (h hp)) Or.inl

-- [utest->req~behavioral-modifiers~1]
/-- The mutated generated core accepts a fully admitted target-loss trace at
every attachment/time; the correct bundle rejects that very trace. -/
theorem missing_loss_prevention (b : Bool) :
    (∀ t p, p ∈ (fixture b .loseTarget).unfold.live t →
      (((noAdditions (.targets (2 : Fin 5))).checkedCore true).expandAnchors).eval
        (fixture b .loseTarget).unfold
        (coreObservation (model b) (fixture b .loseTarget).unfold).checked (.closed p) t) ∧
    ¬ accepts b .loseTarget .finaltarget := by
  refine ⟨?_, (additions_losses_core b).2.2.2⟩
  intro t p _
  rw [Core.expandAnchors_agrees, Formula.checkedCore_agrees]
  rw [coreObservation, Formula.total_agrees, noAdditions_step]
  intro _ y hy
  rw [targets_at] at hy ⊢
  simp only [Lasso.clock_succ, Lasso.step] at hy
  generalize ((fixture b .loseTarget).clock t).1 = i at *
  exact (by decide : ∀ b i p y, targetAt .loseTarget ((fixture b .loseTarget).next i) p y →
    targetAt .loseTarget i p y) b i p y hy

-- [utest->req~behavioral-modifiers~1]
-- [utest->req~behavioral-past-formulas~1]
/-- Parent 1 disappears while its parent (root) survives. Omitting the own-life
guard wrongly compares the old nonempty image with the empty absent-state image. -/
theorem wrong_lifetime_rejects_reset (b : Bool) :
    accepts b .parentGap .finaltarget ∧
    ¬ (((parentLifetimeOnly (.targets (2 : Fin 5))).checkedCore true).expandAnchors).eval
      (fixture b .parentGap).unfold
      (coreObservation (model b) (fixture b .parentGap).unfold).checked (.closed 1) 0 := by
  refine ⟨?_, ?_⟩
  · exact (accepts_iff b .parentGap .finaltarget).mpr
      (((parent_gap_resets b).1 2).2.2.2 ((effective_both b 2 .finaltarget).mpr (by simp)))
  rw [Core.expandAnchors_agrees, Formula.checkedCore_agrees, coreObservation, Formula.total_agrees]
  simp only [parentLifetimeOnly, Formula.denote, Observation.sets, SetAtom.eval, Lifetime.next,
    polarity, ↓reduceIte, SetExpr.eval, Environment.push_zero]
  change ¬ (_ → (View.targets 2).value (model b) (fixture b .parentGap).unfold 1 0 =
    (View.targets 2).expression.eval _ _
      ((Environment.closed 1).push ((View.targets 2).value (model b) (fixture b .parentGap).unfold 1 0)) 1)
  rw [View.expression_capture]
  change ¬ (_ → (View.targets 2).value (model b) (fixture b .parentGap).unfold 1 0 =
    (View.targets 2).value (model b) (fixture b .parentGap).unfold 1 1)
  rw [targets_value _ _ (admitted b .parentGap).2, targets_value _ _ (admitted b .parentGap).2]
  intro h
  have root : (fixture b .parentGap).unfold.ParentPresent (1 : Fin 9) 1 := by
    refine Or.inr ⟨0, rfl, ?_⟩
    change live .parentGap ((fixture b .parentGap).clock 1).1 0 = true
    cases b <;> decide
  have eq := h root
  have old := (targets_at b .parentGap 0 1 6).mpr (by cases b <;> decide)
  have bad := (targets_at b .parentGap 1 1 6).mp (Set.ext_iff.mp eq 6 |>.mp old)
  exact (by cases b <;> decide : ¬ targetAt .parentGap ((fixture b .parentGap).clock 1).1 1 6) bad

/-- Deliberately incomplete adapter: sets and presence retain their actual
values, but equality is unavailable, including when the attachment is absent. -/
noncomputable def missingComparison (b : Bool) :
    PartialObservation (SetAtom (Fin 5)) (SetExpr (Fin 5)) (Fin 9) where
  atom a ρ t := match a with
    | .equal _ _ => none
    | a => (coreObservation (model b) (fixture b .parentGap).unfold).atom a ρ t
  domain := (coreObservation (model b) (fixture b .parentGap).unfold).domain

-- [utest->req~behavioral-qualification~1]
-- [utest->req~behavioral-environments~1]
/-- The attachment's absence makes the survival antecedent false, but its
parent still lives. Strict source implication must still demand the comparison. -/
theorem strict_partial_survival_guard (b : Bool) :
    (1 : Fin 9) ∉ (fixture b .parentGap).unfold.live 1 ∧
    ∃ item ∈ lowerCore (2 : Fin 5) .finaltarget,
      ¬ item.body.eval (fixture b .parentGap).unfold (missingComparison b).checked (.closed 1) 0 := by
  refine ⟨?_, ⟨.all, ((stabilityExpansion (.targets 2)).checkedCore true).expandAnchors⟩,
    by simp [lowerCore, expand], ?_⟩
  · change ¬ live .parentGap ((fixture b .parentGap).clock 1).1 1 = true
    cases b <;> decide
  · rw [Core.expandAnchors_agrees, Formula.checkedCore_agrees]
    intro h
    obtain ⟨S, _, hd⟩ := h.1
    have root : (fixture b .parentGap).unfold.ParentPresent (1 : Fin 9) 1 := by
      refine Or.inr ⟨0, rfl, ?_⟩
      change live .parentGap ((fixture b .parentGap).clock 1).1 0 = true
      cases b <;> decide
    have missing := (hd root).2
    change ∃ p, (none : Option Prop) = some p at missing
    simp at missing

end Clafer.Behavioral.ModifierLoweringExamples
