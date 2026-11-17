module

public import Clafer.Behavioral.InitializerClockSelection
public import Clafer.Behavioral.InitializerContractExamples
public import Clafer.Behavioral.InitializerProductionExamples

/-! # Explicit-clock classification and lifecycle witnesses

Behavioral §5 Definitions 3–5 / §6.1, extended by #194. Finite targets 6/7/8
stand for distinct values 1/2/7. The bounded parentless fixture keeps the real
inherited head, actual parents and reference observations of LifecycleExamples.
-/

@[expose] public section
namespace Clafer.Behavioral.Initializers.ClockExamples
open DPGraph.Predicates Classification LifecycleExamples ContractExamples

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 4096

-- [utest->req~initializer-clock-selection~1]
/-- Both explicit clocks override every finite/unbounded shorthand, including
zero and exactly-one; omission still distinguishes the old abstract clocks. -/
theorem classification_matrix :
    (∀ a p : Bool, ∀ r ∈ ([⟨0, .finite 0⟩, optional, one, ⟨0, .finite 3⟩,
        ⟨2, .finite 2⟩, ⟨1, .unbounded⟩, unrestricted] : List Range),
      classify ⟨a, p, some r, .opt⟩ true (some .instance) = .ok .instanceBirth ∧
      classify ⟨a, p, some r, .opt⟩ false (some .collection) =
        .ok (if p then .parentBirth else .globalZero)) ∧
    classify ⟨true, false, none, .opt⟩ true = .ok .instanceBirth ∧
    classify ⟨true, false, some unrestricted, .opt⟩ true = .ok .globalZero ∧
    classify ⟨true, false, some ⟨0, .finite 3⟩, .opt⟩ true = .error .parentlessMultiplicity ∧
    classify ⟨true, false, some ⟨0, .finite 3⟩, .opt⟩ false (some .instance) =
      .error .scalarNotEstablished ∧
    classify ⟨false, true, some unrestricted, .opt⟩ false (some .instance) = .ok .instanceBirth ∧
    (∀ c : Selection, classify ⟨true, false, some ⟨2, .finite 1⟩, .opt⟩ true (some c) =
      .error .invalidMultiplicity) := by
  constructor
  · intro a p r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      cases a <;> cases p <;> exact ⟨rfl, rfl⟩
  · refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro c; cases c <;> rfl

/-- The optional concrete realization keeps its own bound. Only the authored
parentless abstract gains a global aggregate bound. -/
def bounded (r : Range) : AbstractMultiplicity.Core 5 where
  toCore := model false false
  authoredMultiplicity d := if d = 4 then some r else none

theorem bounded_wellFormed (r : Range) (hr : ValidRange r) : (bounded r).source.WellFormed := by
  rcases wellFormed false false with ⟨a, b, c, d, e, f, g, h, i, j, k, _, l, n⟩
  refine ⟨a, b, c, d, e, f, g, ?_, i, j, k, ?_, l, n⟩
  · intro d s o a b edge owner ha hb
    exact h d s o a b edge (((bounded r).owner_iff s o).mp owner) ha hb
  · intro d
    fin_cases d <;> simp [bounded, AbstractMultiplicity.Core.source, model,
      Semantics.AbstractMultiplicity.range, hr]
    all_goals decide

theorem bounded_structural (r : Range) (c : Case) :
    Structural.Valid (bounded r).source (fixture c).unfold := by
  have h := (admitted false false c (Or.inl rfl)).2
  have identities : Structural.IdentitiesValid (bounded r).source (fixture c).unfold := by
    rcases h.identities with ⟨a, b, d, e, f, g⟩
    exact ⟨a, b, d, e, f, g⟩
  refine ⟨identities, h.root_live, h.parent_live, fun t => ?_⟩
  rcases h.states t with ⟨a, b, d, e, f, g, i, j, k, counts, l, n, q⟩
  refine ⟨a, b, d, e, f, g, i, j, ((bounded r).keys_iff _ t).mpr k, ?_, l, n, q⟩
  intro d p hp x hx
  by_cases hd : d = 4
  · subst d
    simp [bounded, AbstractMultiplicity.Core.source, model] at hp
  · have bound : (bounded r).source.family.multiplicity d = (model false false).family.multiplicity d := by
      simp [bounded, AbstractMultiplicity.Core.source, model, hd]
    rw [bound, (bounded r).raw_eq]
    exact counts d p hp x hx

private instance (c : Case) (i : Fin 3) (x : Fin 9) :
    Decidable (x ∈ (((fixture c).state i).raw (model false false).toEffectiveCore 0).head 4) := by
  dsimp only [Trace.raw, Lasso.state, fixture]
  infer_instance

-- [utest->req~initializer-clock-selection~1]
/-- Global 0..3 holds at every state, including a late concrete parent. It
counts heads, never their target image. No initializer premise is used. -/
theorem bounded_admitted (c : Case) :
    AbstractMultiplicity.Admissible (bounded ⟨0, .finite 3⟩) (fixture c).unfold := by
  refine ⟨bounded_wellFormed _ (by decide), bounded_structural _ c, ?_⟩
  intro t d hd
  have eq : d = 4 := by simpa [bounded, model] using hd
  subst d
  change InRange ⟨0, .finite 3⟩
    {x // x ∈ (((fixture c).unfold).raw (model false false).toEffectiveCore t).head 4}
  dsimp only [Trace.raw, Lasso.unfold]
  generalize hi : ((fixture c).clock t).1 = i
  change InRange ⟨0, .finite 3⟩
    {x // x ∈ (((fixture c).state i).raw (model false false).toEffectiveCore 0).head 4}
  rw [inRange_card]
  clear hi t
  decide +revert

/-- Complete parentless view; its context is root even for nested realizations. -/
def globalView (c : Case) : View (Fin 9) where
  contexts _ := {0}
  heads t _ := G c t
  instances := G c
  target := V c

def source (r : Option (Set (Fin 9))) : Unit → Transport.Value (Fin 9) (Set (Fin 9)) 0 :=
  fun _ _ _ => r

def obligation (clock : Initializers.Clock) : Obligation (Fin 5) Unit := ⟨4, .root, clock, ()⟩

-- [utest->req~initializer-clock-selection~1]
theorem bounded_elaboration :
    ClockSelection.elaborate (bounded ⟨0, .finite 3⟩) 4 .initial true () (some .instance) =
      .ok (obligation .instanceBirth) ∧
    ClockSelection.elaborate (bounded ⟨0, .finite 3⟩) 4 .initial false () (some .collection) =
      .ok (obligation .globalZero) ∧
    ClockSelection.elaborate (bounded ⟨0, .finite 3⟩) 4 .initial true () =
      .error .parentlessMultiplicity := ⟨rfl, rfl, rfl⟩

-- [utest->req~initializer-clock-selection~1]
/-- The issue's distinguishing 0..3 trace: the collection is empty at zero;
a nested realization is born later at value 7 (identity 8). -/
theorem late_separates :
    AbstractMultiplicity.Admissible (bounded ⟨0, .finite 3⟩) (fixture .lateParent).unfold ∧
    Meaning (fixture .lateParent).unfold (globalView .lateParent) (source (some {6}))
      (obligation .globalZero) ∧
    ¬ Meaning (fixture .lateParent).unfold (globalView .lateParent) (source (some {6}))
      (obligation .instanceBirth) := by
  refine ⟨bounded_admitted _, ?_, ?_⟩
  · intro present
    obtain ⟨x, hx⟩ := present
    have empty : G .lateParent 0 = ∅ := by
      ext x
      change (live .lateParent 0 x = true ∧ 3 ≤ x.val ∧ x.val < 6) ↔ False
      decide +revert
    exact (Set.notMem_empty x (empty ▸ hx)).elim
  · intro h
    have member : 5 ∈ G .lateParent 1 := by
      change live .lateParent 1 5 = true ∧ 3 ≤ (5 : Fin 9).val ∧ (5 : Fin 9).val < 6
      decide
    have bad := h 1 5 member global_late_parent.2.2.2.1
    have eq : (6 : Fin 9) = 8 := Set.singleton_injective (Option.some.inj bad)
    contradiction

-- [utest->req~initializer-clock-selection~1]
-- [utest->req~behavioral-past-formulas~1]
/-- Check the generated ordinary core, including its definedness component. -/
theorem late_core_separates :
    (∀ t x, x ∈ attachments (fixture .lateParent).unfold (globalView .lateParent)
      (obligation .globalZero) t → x ∈ (fixture .lateParent).unfold.live t →
      (lowerCore (obligation .globalZero)).eval (fixture .lateParent).unfold
        (observation (fixture .lateParent).unfold (globalView .lateParent) (source (some {6}))).checked
        (.closed x) t) ∧
    ¬ (∀ t x, x ∈ attachments (fixture .lateParent).unfold (globalView .lateParent)
      (obligation .instanceBirth) t → x ∈ (fixture .lateParent).unfold.live t →
      (lowerCore (obligation .instanceBirth)).eval (fixture .lateParent).unfold
        (observation (fixture .lateParent).unfold (globalView .lateParent) (source (some {6}))).checked
        (.closed x) t) := by
  have root := (admitted false false .lateParent (Or.inl rfl)).2.root_live
  rw [lowerCore_agrees _ _ _ _ root, lowerCore_agrees _ _ _ _ root]
  exact late_separates.2


-- [utest->req~initializer-clock-selection~1]
/-- Nonvacuous composition uses the structural view constructed by production,
not just a manually supplied View. The global count remains enforced. -/
theorem late_profile_satisfies :
    ClockSelection.Satisfies (bounded ⟨0, .finite 3⟩) (fixture .lateParent).unfold
      (source none) [obligation .globalZero] := by
  refine ⟨bounded_admitted _, ?_⟩
  intro o ho
  have eq : o = obligation .globalZero := by simpa using ho
  subst o
  refine ⟨4, .declared (by decide), ?_⟩
  intro present
  obtain ⟨x, hx⟩ := present
  have heads := (ContractExamples.global_observations .lateParent 0).1
  have member : x ∈ G .lateParent 0 := heads.symm ▸ hx
  change live .lateParent 0 x = true ∧ 3 ≤ x.val ∧ x.val < 6 at member
  have empty : ∀ x : Fin 9, ¬ (live .lateParent 0 x = true ∧ 3 ≤ x.val ∧ x.val < 6) := by decide
  exact (empty x member).elim

theorem late_profile_core :
    ClockSelection.CoreSatisfies (bounded ⟨0, .finite 3⟩) (fixture .lateParent).unfold
      (source none) [obligation .globalZero] :=
  (ClockSelection.core_agrees _ _ _ _).mpr late_profile_satisfies

-- [utest->req~initializer-clock-selection~1]
/-- Defined-empty and undefined are distinct observations, but both are ignored
at an empty selected global birth, even if heads arrive with a later parent. -/
theorem inactive_global (r : Option (Set (Fin 9))) :
    Meaning (fixture .lateParent).unfold (globalView .lateParent) (source r)
      (obligation .globalZero) := by
  intro present
  obtain ⟨x, hx⟩ := present
  change live .lateParent 0 x = true ∧ 3 ≤ x.val ∧ x.val < 6 at hx
  exact ((by decide : ∀ x : Fin 9,
    ¬ (live .lateParent 0 x = true ∧ 3 ≤ x.val ∧ x.val < 6)) x hx).elim

/-- Explicit collection at an optional concrete declaration overrides its old
per-instance shorthand. Inherited obligations retain the complete original view. -/
theorem narrowed_collection_elaboration (required : Bool) :
    Structure.elaborate (model true required) 4 .initial (some unrestricted) false ()
        (some .collection) = .ok ⟨4, .parent, .parentBirth, ()⟩ ∧
    Structure.elaborate (model true required) 2 .initial
        (some (if required then one else optional)) false () (some .collection) =
      .ok ⟨2, .parent, .parentBirth, ()⟩ := by
  cases required <;> exact ⟨rfl, rfl⟩

theorem inherited_collection_preserved (required : Bool) :
    Structure.Effective (model true required)
      (fun d => if d = 4 then {⟨4, .parent, .parentBirth, ()⟩} else ∅) 2
        (⟨4, .parent, .parentBirth, ()⟩ : Obligation (Fin 5) Unit) :=
  Structure.effective_inherited _ _ (show (model true required).family.super 2 = some 4 from by cases required <;> decide)
    (Structure.effective_own _ _ _ _ (by simp))

-- [utest->req~initializer-clock-selection~1]
/-- Both finite and unbounded authored bounds select the same explicit clock;
the lowered inherited obligation consequently retains the late-birth witness. -/
theorem inherited_narrowing :
    Classification.classify ⟨true, true, some one, .opt⟩ false (some .collection) =
      .ok .parentBirth ∧
    Classification.classify ⟨true, true, some unrestricted, .opt⟩ false (some .collection) =
      .ok .parentBirth ∧
    Structural.Admissible (model true true) (fixture .replace).unfold ∧
    Candidate.CollectionBirths (fixture .replace).unfold (fun _ => {1})
      (H .replace) (T .replace) (fun t _ => if t = 0 then some {6} else some {7}) ∧
    ¬ Candidate.SingleBirths (fixture .replace).unfold (G .replace) (V .replace)
      (fun _ _ => some {6}) :=
  ⟨rfl, rfl, exactly_one_replacement⟩

-- [utest->req~initializer-clock-selection~1]
/-- A global collection sees both actual parents together. Choosing an instance
clock on that abstract still applies scalar admission before any evaluation. -/
theorem cross_parent_collection :
    ClockSelection.elaborate (bounded ⟨0, .finite 3⟩) 4 .initial false () (some .collection) =
      .ok (obligation .globalZero) ∧
    AbstractMultiplicity.Admissible (bounded ⟨0, .finite 3⟩) (fixture .cross).unfold ∧
    Meaning (fixture .cross).unfold (globalView .cross) (source (some {6, 7}))
      (obligation .globalZero) := by
  refine ⟨rfl, bounded_admitted _, ?_⟩
  have h := global_cross_parent.2.1 0 0 rfl
    (((fixture .cross).unfold.starts_zero 0).mpr (by change live .cross 0 0 = true; decide))
  exact h

end Clafer.Behavioral.Initializers.ClockExamples
