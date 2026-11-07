module

public import Clafer.Behavioral.FiniteComposition
public import Clafer.Behavioral.ModifierExamples
public import Clafer.Behavioral.PropertyExamples
public import Clafer.Behavioral.PatternExamples

/-! # Composed behavioral qualification witnesses

The independently admitted machine/reference inventory has repeated bag heads,
replacement and reappearance. Full model checks distinguish cancellation from
a persistent parent; richer inherited finality is checked in the source model.
Separate partial tables expose domain failures hidden by truth-only lowering.
-/

@[expose] public section
namespace Clafer.Behavioral.QualificationExamples
open Properties

set_option maxRecDepth 16384
set_option maxHeartbeats 600000

noncomputable def program {A D : Nat → Type} {n : Nat} (a : Formula A D n) (sign : Bool) :
    a.Program sign := ⟨a.domainFormula.lower, (a.normalize sign).lower.mapAtoms CheckedAtom.value, rfl, rfl⟩

def model := Structural.Core.ofEffective Examples.model
abbrev A := SetAtom (Fin 4)
abbrev D := SetExpr (Fin 4)
abbrev F := Formula A D 0

def never : F := .eventually (.not .truth)
def cancellationBodies (i : Fin 2) : F := if i = 0 then never else never.not
def constraints (i : Fin 2) : Constraint (Fin 4) A D (Fin 8) :=
  .nested model 2 (cancellationBodies i)
def noModifiers : Fin 0 → Constraint (Fin 4) A D (Fin 8) := Fin.elim0

noncomputable def bundle (L : Lasso (Fin 4) 8 3) : FiniteBundle L constraints :=
  ⟨fun i => Constraint.finiteNested model L 2 _ (program (cancellationBodies i) true)⟩
def emptyBundle (L : Lasso (Fin 4) 8 3) : FiniteBundle L noModifiers := ⟨fun i => Fin.elim0 i⟩

def observations (τ : Trace (Fin 4) (Fin 8)) : PartialObservation A D (Fin 8) :=
  .ofTotal (.sets Examples.model τ)
def finiteObservations (L : Lasso (Fin 4) 8 3) :=
  FinitePartialObservation.ofTotal (FiniteObservation.sets Examples.model L)
def adapter (L : Lasso (Fin 4) 8 3) : FinitePartialAdapter L (observations L.unfold) :=
  ⟨finiteObservations L, FinitePartialObservation.ofTotal_agrees _ _ _ (FiniteObservation.sets_agrees _ _)⟩

theorem empty_modifiers : Set.range noModifiers = modifierConstraints model (fun _ => ∅) := by
  ext c
  simp [noModifiers, modifierConstraints, Modifiers.Effective]

def cancellationModel : Model (Fin 4) A D (Fin 8) :=
  Model.behavioral model (fun _ => ∅) observations (Set.range constraints)

noncomputable def check (loop : Fin 4) : Bool :=
  let L := LassoExamples.cycle loop
  commonCheck Examples.model (bundle L) (emptyBundle L) (finiteObservations L) (finiteObservations L)

theorem check_agrees (loop : Fin 4) : check loop = true ↔
    cancellationModel.Satisfies (LassoExamples.cycle loop).unfold := by
  let L := LassoExamples.cycle loop
  have observed := Structural.observed_common L.unfold Examples.model_supported (LassoExamples.cycle_valid loop)
  let G : FinitePartialAdapter L (.ofTotal (.sets Examples.model (Structural.observed model L.unfold))) :=
    { observations := finiteObservations L
      agrees := by
        rw [show model = Structural.Core.ofEffective Examples.model from rfl, observed]
        exact (adapter L).agrees }
  exact commonCheck_correct Examples.model Examples.model_wellFormed Examples.model_supported (by decide)
    (fun _ => ∅) observations (bundle L) (emptyBundle L) empty_modifiers (adapter L) G

-- [utest->req~behavioral-qualification~1]
theorem replaceable_both_signs : check 0 = true := by
  simp [check, commonCheck, bodyCheck, bundle, emptyBundle, FiniteBundle.domain,
    FiniteBundle.value, Constraint.Finite.domain, Constraint.Finite.value,
    Constraint.finiteNested, program, constraints, cancellationBodies, never,
    Formula.domainFormula, Formula.normalize, Formula.lower, Core.mapAtoms, Core.attachedFinite]
  decide

-- [utest->req~behavioral-qualification~1]
theorem stable_parent_rejected : check 3 = false := by
  simp [check, commonCheck, bodyCheck, bundle, emptyBundle, FiniteBundle.domain,
    FiniteBundle.value, Constraint.Finite.domain, Constraint.Finite.value,
    Constraint.finiteNested, program, constraints, cancellationBodies, never,
    Formula.domainFormula, Formula.normalize, Formula.lower, Core.mapAtoms, Core.attachedFinite]
  decide

theorem full_replaceable_model : cancellationModel.Satisfies (LassoExamples.cycle 0).unfold :=
  (check_agrees 0).mp replaceable_both_signs

theorem full_stable_rejection : ¬ cancellationModel.Satisfies (LassoExamples.cycle 3).unfold := by
  intro h
  have yes := (check_agrees 3).mpr h
  rw [stable_parent_rejected] at yes
  contradiction

/-- This is an admitted richer model with inherited references and an inherited
effective final modifier. Changing its target violates the full model. -/
def inheritedModifiers (d : Fin 8) : Set Modifiers.Modifier :=
  if d = 7 then {.final} else ∅

theorem effective_is_final (d : Fin 8) (modifier : Modifiers.Modifier)
    (h : Modifiers.Effective (StructuralExamples.model false false).family inheritedModifiers d modifier) :
    modifier = .final := by
  obtain ⟨a, _, ha⟩ := h
  simp only [inheritedModifiers] at ha
  split_ifs at ha with he
  · exact ha
  · exact ha.elim

def inheritedModel : Model (Fin 8) (SetAtom (Fin 8)) (SetExpr (Fin 8)) (Fin 7) :=
  Model.behavioral (StructuralExamples.model false false) inheritedModifiers
    (fun τ => .ofTotal (.sets (StructuralExamples.model false false).toEffectiveCore
      (Structural.observed (StructuralExamples.model false false) τ))) ∅

-- [utest->req~behavioral-qualification~1]
theorem inherited_full_model : inheritedModel.Satisfies ModifierExamples.fixedInherited := by
  refine ⟨⟨StructuralExamples.model_wellFormed false false,
    ModifierExamples.fixed_inherited_valid, ?_⟩, by simp [inheritedModel, Model.behavioral]⟩
  intro d
  have final : Modifiers.Final (StructuralExamples.model false false) ModifierExamples.fixedInherited d := by
    constructor
    · intro p i j _ _; rfl
    · intro x _ i j _ _; rfl
  refine ⟨?_, fun _ => final, ?_, ?_⟩
  · intro h; cases effective_is_final d .initial h
  · intro h; cases effective_is_final d .finalref h
  · intro h; cases effective_is_final d .finaltarget h

theorem inherited_mutation_rejected : ¬ inheritedModel.Satisfies (StructuralExamples.trace false) := by
  intro h
  have effective : Modifiers.Effective (StructuralExamples.model false false).family inheritedModifiers 5 .final :=
    Modifiers.effective_inherited _ _ (by decide) (Modifiers.effective_own _ _ 7 .final (by simp [inheritedModifiers]))
  exact ModifierExamples.inherited_ref_mutation ((h.1.2.2 5).2.1 effective).2

namespace Partial
abbrev A (_ : Nat) := Unit
abbrev D (_ : Nat) := Unit
abbrev F := Formula A D 0
def L := LassoExamples.cycle 0
def atom : F := .atom ()

def table (missingAfter : Fin 4) (truth : Bool) : FinitePartialObservation A D 8 3 where
  atom _ _ s := if s.1 < missingAfter then some truth else none
  domain _ _ _ := some ∅

def source (missingAfter : Fin 4) (truth : Bool) : PartialObservation A D (Fin 8) where
  atom _ _ t := if (L.clock t).1 < missingAfter then some (truth = true) else none
  domain _ _ _ := some ∅

def adapter (missingAfter : Fin 4) (truth : Bool) : FinitePartialAdapter L (source missingAfter truth) where
  observations := table missingAfter truth
  agrees := ⟨by intros; simp [table, source], by intros; simp [table, source]⟩

noncomputable def check (a : F) (missingAfter : Fin 4) (truth : Bool) (context : Fin 8 := 3)
    (t : Nat := 0) (sign : Bool := true) : Formula.Program.Result :=
  (program a sign).check L (table missingAfter truth) (.closed context) t

-- [utest->req~behavioral-qualification~1]
theorem strict_false_implication : check (.implies (.not .truth) atom) 0 false = .undefined := by
  simp [check, program, atom, Formula.Program.check, Formula.domainFormula, Formula.lower,
    Formula.normalize, Core.mapAtoms, FinitePartialObservation.checked, table, Lasso.clock_zero, Lasso.start]

theorem early_truth_still_undefined : check atom.eventually 1 true = .undefined := by
  simp [check, program, atom, Formula.Program.check, Formula.domainFormula, Formula.lower,
    Formula.normalize, Core.mapAtoms]
  decide

theorem cancelled_domain_both_signs :
    check atom.eventually 2 false = .satisfied ∧ check atom.eventually 2 false 3 0 false = .satisfied := by
  simp [check, program, atom, Formula.Program.check, Formula.domainFormula, Formula.lower,
    Formula.normalize, Core.mapAtoms]
  decide

theorem rebirth_new_domain : check atom.eventually 2 false 3 3 = .undefined := by
  simp [check, program, atom, Formula.Program.check, Formula.domainFormula, Formula.lower,
    Formula.normalize, Core.mapAtoms]
  decide

theorem defined_false_distinct : check atom 1 false = .violated := by
  simp [check, program, atom, Formula.Program.check, Formula.domainFormula, Formula.lower,
    Formula.normalize, Core.mapAtoms, FinitePartialObservation.checked, table, Lasso.clock_zero, Lasso.start]

def missingDomain : FinitePartialObservation A D 8 3 :=
  { table 3 true with domain := fun _ _ _ => none }

-- [utest->req~behavioral-qualification~1]
theorem missing_domain_not_empty :
    (program (.quant .all () .truth : F) true).check L missingDomain (.closed 0) 0 = .undefined ∧
    (program (.letSet () .truth : F) true).check L missingDomain (.closed 0) 0 = .undefined := by
  simp [program, Formula.Program.check, Formula.domainFormula, Formula.lower,
    Formula.normalize, Core.mapAtoms, FinitePartialObservation.checked, missingDomain]

def mixedMembers : FinitePartialObservation A D 8 3 where
  atom _ ρ _ := if ∃ v, (4 : Fin 8) ∈ ρ.lookup v then none else some true
  domain _ _ _ := some {3, 4}

theorem every_counted_member_defined (q : Quantifier) :
    (program (.quant q () (.atom ()) : F) true).check L mixedMembers (.closed 0) 0 = .undefined := by
  cases q <;> simp [program, Formula.Program.check, Formula.domainFormula, Formula.lower,
    Formula.normalize, Core.mapAtoms, FinitePartialObservation.checked, mixedMembers,
    Quantifier.finite, FiniteEnvironment.push, FiniteEnvironment.closed]

-- [utest->req~behavioral-qualification~1]
theorem infinite_partial_witness :
    atom.eventually.Satisfies L.unfold (source 2 false) true (.closed 3) 0 ∧
    atom.eventually.Satisfies L.unfold (source 2 false) false (.closed 3) 0 := by
  constructor
  · exact ((program _ true).check_satisfied L (adapter 2 false) (.closed 3) 0).mp cancelled_domain_both_signs.1
  · exact ((program _ false).check_satisfied L (adapter 2 false) (.closed 3) 0).mp cancelled_domain_both_signs.2

end Partial
end Clafer.Behavioral.QualificationExamples
