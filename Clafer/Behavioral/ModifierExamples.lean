module

public import Clafer.Behavioral.Modifiers
public import Clafer.Behavioral.StructuralExamples
public import Clafer.Behavioral.LassoExamples

/-! # Modifier witnesses on admitted traces

A target swap preserves the target image while changing both head assignments.
An inherited reference mutation is visible through the inherited declaration;
finality of its enclosing Port is shallow. Gaps reset only the relevant lifetime.
-/

@[expose] public section
namespace Clafer.Behavioral.ModifierExamples
open Modifiers ReferenceObservation

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def model := Structural.Core.ofEffective Examples.model

def swap : Lasso (Fin 4) 8 1 where
  identities := Examples.pool
  loop := 1
  live _ := (LassoExamples.cycle 0).live 0
  deref t d x y := d == 2 && (x == 3 || x == 4) &&
    y == (if (x == 3) == (t == 0) then 5 else 6)

-- [utest->req~behavioral-modifiers~1]
theorem swap_valid : swap.unfold.Valid Examples.model :=
  (Lasso.valid_iff_unfold _ _).mp ((Lasso.checks_iff _ _).mp (by decide))

theorem swap_admitted : Structural.Admissible model swap.unfold :=
  ⟨Structural.Core.ofEffective_wellFormed Examples.model_wellFormed Examples.model_supported (by decide),
    (Structural.valid_iff_common Examples.model_wellFormed Examples.model_supported (by decide) _).mpr swap_valid⟩

theorem swap_reference (t : Nat) (x y : Fin 8) :
    (Structural.current model swap.unfold t).deref 2 x y ↔ swap.unfold.deref t 2 x y :=
  InheritedReference.declared_agreement _ swap_valid (by decide) x y

theorem swap_heads : FinalHeads model swap.unfold 2 := by
  intro p i j _ _
  rfl

theorem swap_targets (t : Nat) (p : Fin 8) :
    targets (Structural.current model swap.unfold t) 2 p =
      {y | p = 1 ∧ (y = 5 ∨ y = 6)} := by
  ext y
  simp only [targets, assignments, Set.mem_ofPred_eq, swap_reference]
  change (∃ x, ((swap.unfold.raw Examples.model t).contains 2 p x) ∧ swap.unfold.deref t 2 x y) ↔ _
  simp only [Trace.raw, Trace.ParentAt, Lasso.unfold, Set.mem_ofPred_eq]
  generalize (swap.clock t).1 = time
  revert time p y
  decide

-- [utest->req~behavioral-modifiers~1]
theorem swap_finaltarget : FinalTarget model swap.unfold 2 := by
  intro p i j _ _
  exact (swap_targets i p).trans (swap_targets j p).symm

-- [utest->req~behavioral-modifiers~1]
theorem swap_not_finalref : ¬ FinalRef model swap.unfold 2 := by
  intro h
  have eq := h 3 (by exact .refl) 0 1 (by omega) (by
    intro t _ _; change swap.live (swap.clock t).1 3 = true; rfl)
  have link : (Structural.current model swap.unfold 0).deref 2 3 5 :=
    (swap_reference 0 3 5).mpr (by change swap.deref (swap.clock 0).1 2 3 5 = true; decide)
  have bad := (swap_reference 1 3 5).mp (Set.ext_iff.mp eq 5 |>.mp link)
  contradiction

theorem swap_not_final : ¬ Final model swap.unfold 2 := fun h => swap_not_finalref h.2

/-- Parent and head gaps permit a later target without linking separate lives. -/
theorem gap_resets : Stable (fun t => t = 0 ∨ 2 ≤ t) (fun t => if t = 0 then 5 else 6) := by
  rw [stable_iff_adjacent]
  intro t ht hn
  split_ifs <;> simp_all

theorem no_gap_rejects : ¬ Stable (fun _ => True) (fun t => if t = 0 then 5 else 6) := by
  intro h
  have eq := h 0 1 (by omega) (by intro _ _ _; trivial)
  contradiction

/-- The inherited field keeps its actual head and owner; changing that owner's
relation violates finalref even without an annotation directly on the field. -/
-- [utest->req~behavioral-modifiers~1]
theorem inherited_ref_mutation : ¬ FinalRef (StructuralExamples.model false false)
    (StructuralExamples.trace false) 5 := by
  intro h
  have eq := h 3 .refl 0 1 (by omega) (by intro _ _ _; trivial)
  have link := StructuralExamples.inherited_bag_changes_target.1
  have bad := Set.ext_iff.mp eq 5 |>.mp link
  change InheritedReference.deref _ _ _ _ _ at bad
  rw [InheritedReference.deref_owner StructuralExamples.inherited_owner] at bad
  have : (5 : Fin 7) = 6 := bad.2.2.2
  contradiction

/-- Final heads at Port do not recursively freeze its speed-field references. -/
theorem inherited_shallow_heads : FinalHeads (StructuralExamples.model false false)
    (StructuralExamples.trace false) 4 := by
  intro p i j _ _
  rfl

theorem inherited_initial : Initial (StructuralExamples.model false false)
    (StructuralExamples.trace false) 5 := by
  intro t p hp _
  have hp2 : p = 2 := by
    obtain ⟨c, hc, hp⟩ := hp
    have hc3 : c = 3 := by simpa [StructuralExamples.model] using hc.symm
    subst c
    have ha := hp.2
    exact (by decide : ∀ p, (StructuralExamples.model false false).toEffectiveCore.Ancestor
      (StructuralExamples.pool.directType p) 3 → p = 2) p ha
  subst p
  exact ⟨3, ⟨trivial, trivial, rfl⟩, .refl, by decide⟩

theorem inherited_modifier : Effective (StructuralExamples.model false false).family
    (fun d => if d = 7 then {.finalref} else ∅) 5 .finalref :=
  effective_inherited _ _ (by decide) (effective_own _ _ 7 .finalref (by simp))


theorem inherited_shallow_final : Final (StructuralExamples.model false false)
    (StructuralExamples.trace false) 4 := by
  refine ⟨inherited_shallow_heads, ?_⟩
  have empty (t : Nat) (x : Fin 7) :
      {y | (Structural.current (StructuralExamples.model false false)
        (StructuralExamples.trace false) t).deref 4 x y} = ∅ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨o, owner, _⟩
    have noRef := (by decide : ∀ o,
      (StructuralExamples.model false false).toEffectiveCore.Ancestor 4 o →
        (StructuralExamples.model false false).family.reference o = .basic) o owner.ancestor
    exact owner.has_reference noRef
  intro x _ i j _ _
  exact (empty i x).trans (empty j x).symm

/-- A constant snapshot retains the inherited reference assignment. -/
def fixedInherited : Trace (Fin 8) (Fin 7) :=
  {StructuralExamples.trace false with deref := fun _ => (StructuralExamples.trace false).deref 0}

theorem fixed_inherited_valid : Structural.Valid (StructuralExamples.model false false) fixedInherited := by
  have h := (StructuralExamples.admitted false false).2
  refine ⟨⟨h.identities.root_type, h.identities.root_only, h.identities.concrete,
    h.identities.root_parent, h.identities.parent_exists, h.identities.parent_typed⟩,
    h.root_live, h.parent_live, ?_⟩
  intro t
  have st := h.states 0
  exact ⟨st.typed, st.root_head, st.root_separate, st.inherits, st.abstracts,
    st.parents, st.references, st.coherent, st.keys, st.multiplicities, st.groups,
    st.disjoint, st.reachable⟩

theorem fixed_inherited_final : Final (StructuralExamples.model false false) fixedInherited 5 := by
  constructor
  · intro p i j _ _; rfl
  · intro x _ i j _ _; rfl


/-- Both references may change between disconnected lives. The full source
expansion is checked on an admitted infinite lasso, including its loop edge. -/
theorem cycle_finalref : FinalRef model (LassoExamples.cycle 3).unfold 2 := by
  let L := LassoExamples.cycle 3
  have valid := (Structural.valid_iff_common Examples.model_wellFormed
    Examples.model_supported (by decide) L.unfold).mpr (LassoExamples.cycle_valid 3)
  apply (finalRef_agrees model L.unfold valid 2).mp
  have checked : (stabilityExpansion (.reference 2)).Attached L.unfold
      (.sets Examples.model L.unfold) (fun _ => Set.univ) := by
    suffices hc : ((stabilityExpansion (.reference 2)).normalize true).lower.attachedFinite
        L (FiniteObservation.sets Examples.model L) (fun _ => Finset.univ) = true by
      simpa only [Finset.coe_univ] using (Core.normalized_attached_agrees L
        (FiniteObservation.sets Examples.model L) _ (FiniteObservation.sets_agrees _ _)
        (fun _ => Finset.univ) (stabilityExpansion (.reference 2))).mp hc
    simp [Core.attachedFinite, stabilityExpansion, View.expression, Formula.normalize,
      Formula.lower, FiniteObservation.sets, SetAtom.finite]
    decide
  rw [show model = Structural.Core.ofEffective Examples.model from rfl,
    Structural.observed_common _ Examples.model_supported (LassoExamples.cycle_valid 3)]
  intro t x _ hx
  exact checked t x (Set.mem_univ x) hx

def birthFixture (good : Bool) : Lasso (Fin 4) 8 2 where
  identities := Examples.pool
  loop := 2
  live t x := x == 0 || x == 5 || x == 6 || (x == 1 && t != 1) ||
    ((x == 3 || x == 4) && (t == 0 || (good && t == 2)))
  deref t d x y := d == 2 && (x == 3 || x == 4) &&
    (t == 0 || (good && t == 2)) && y == 5

theorem births_valid (good : Bool) : (birthFixture good).unfold.Valid Examples.model :=
  (Lasso.valid_iff_unfold _ _).mp ((Lasso.checks_iff _ _).mp (by decide +revert))

theorem initial_every_birth : Initial model (birthFixture true).unfold 2 := by
  intro t p hp _
  obtain ⟨c, hc, hp⟩ := hp
  have he : c = 1 := by simpa [model, Structural.Core.ofEffective, Examples.model] using hc.symm
  subst c
  change ∃ x, ((birthFixture true).unfold.raw Examples.model t).contains 2 p x
  change (birthFixture true).live ((birthFixture true).clock t).1 p = true ∧
    Examples.model.Ancestor (Examples.pool.directType p) 1 at hp
  simp only [Trace.raw, Trace.ParentAt, Lasso.unfold, Set.mem_ofPred_eq]
  generalize ((birthFixture true).clock t).1 = time at hp ⊢
  exact (by decide : ∀ time p,
    (birthFixture true).live time p = true ∧ Examples.model.Ancestor (Examples.pool.directType p) 1 →
    ∃ x, ((birthFixture true).live time p = true ∧ (birthFixture true).live time x = true ∧
      Examples.pool.parent x = some p) ∧ Examples.model.Ancestor (Examples.pool.directType x) 2 ∧
        Examples.model.family.parent 2 ≠ none) time p hp

-- [utest->req~behavioral-modifiers~1]
theorem initial_rebirth_missing : ¬ Initial model (birthFixture false).unfold 2 := by
  intro h
  have alive : 1 ∈ (birthFixture false).unfold.live 2 := by
    change (birthFixture false).live ((birthFixture false).clock 2).1 1 = true
    decide
  have dead : 1 ∉ (birthFixture false).unfold.live 1 := by
    change ¬ (birthFixture false).live ((birthFixture false).clock 1).1 1 = true
    decide
  have atBirth := h 2 1 ⟨1, rfl, alive, .refl⟩
    ⟨alive, Or.inr ⟨1, rfl, dead⟩⟩
  obtain ⟨x, hx⟩ := atBirth
  have absent : ¬ ((birthFixture false).unfold.raw Examples.model 2).contains 2 1 x := by
    clear * - x
    simp only [Trace.raw, Trace.ParentAt, Lasso.unfold, Set.mem_ofPred_eq]
    decide +revert
  exact absent hx

end Clafer.Behavioral.ModifierExamples
