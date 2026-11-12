module

public import Clafer.Behavioral.InitializerLifecycleExamples
public import Clafer.Behavioral.InitializerCandidateExamples

/-! # Accepted initializer contract regressions

Behavioral §5 Definitions 2–5, §6.1 and #170. The finite target names in
lifecycle fixtures represent distinct source values. Arithmetic definedness is
checked separately in InitializerCandidateExamples using the integer evaluator;
this module checks scalar admission without reinterpreting arithmetic. -/

@[expose] public section
namespace Clafer.Behavioral.Initializers.ContractExamples
open Candidate LifecycleExamples

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def H (c : Case) (t : Nat) (p : Fin 9) : Set (Fin 9) :=
  {x | headAt c ((fixture c).clock t).1 p x}
def T (c : Case) (t : Nat) (p : Fin 9) : Set (Fin 9) :=
  {y | targetAt c ((fixture c).clock t).1 p y}
def G (c : Case) (t : Nat) : Set (Fin 9) :=
  {x | live c ((fixture c).clock t).1 x = true ∧ 3 ≤ x.val ∧ x.val < 6}
def V (c : Case) (t : Nat) (x : Fin 9) : Fin 9 := target c ((fixture c).clock t).1 x

private instance (c : Case) (i : Fin 3) (p x : Fin 9) : Decidable (headAt c i p x) := by
  unfold headAt; infer_instance
private instance (c : Case) (i : Fin 3) (p y : Fin 9) : Decidable (targetAt c i p y) := by
  unfold targetAt; infer_instance
private instance (c : Case) (t : Nat) (p x : Fin 9) : Decidable (x ∈ H c t p) := by
  unfold H; infer_instance
private instance (c : Case) (t : Nat) (p x : Fin 9) : Decidable (x ∈ T c t p) := by
  unfold T; infer_instance
private instance (c : Case) (t : Nat) (x : Fin 9) : Decidable (x ∈ G c t) := by
  unfold G; infer_instance

theorem global_observations (c : Case) (t : Nat) :
    G c t = ((fixture c).unfold.raw (model false false).toEffectiveCore t).head 4 ∧
    V c t '' G c t = {y | ∃ x ∈ G c t,
      (Structural.current (model false false) (fixture c).unfold t).deref 4 x y} := by
  constructor
  · ext x
    dsimp only [G, Trace.raw, Lasso.unfold]
    generalize ((fixture c).clock t).1 = i
    dsimp only [fixture]
    clear * - c i x
    decide +revert
  · ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    have refs (x : Fin 9) :
        (Structural.current (model false false) (fixture c).unfold t).deref 4 x y ↔
          x ∈ G c t ∧ V c t x = y := by
      change InheritedReference.deref _ _ _ _ _ ↔ _
      rw [InheritedReference.deref_owner (show InheritedReference.Owner
        (model false false).family 4 4 from .declared (by decide))]
      dsimp only [G, V, Trace.raw, Lasso.unfold]
      generalize ((fixture c).clock t).1 = i
      dsimp only [fixture]
      clear * - c i x y
      decide +revert
    simp only [refs, and_self_left]

private theorem parent_present (c : Case) (t : Nat) : 1 ∈ (fixture c).unfold.live t := by
  change live c ((fixture c).clock t).1 1 = true
  simp [live]

private theorem root_present (c : Case) (t : Nat) : 0 ∈ (fixture c).unfold.live t := by
  change live c ((fixture c).clock t).1 0 = true
  simp [live]

private theorem empty_initial (c : Case) (hc : c = .lateOne ∨ c = .lateTwo ∨ c = .lateParent) :
    H c 0 1 = ∅ := by
  ext x
  dsimp only [H, fixture, Lasso.clock_zero, Lasso.start]
  decide +revert

-- [utest->req~behavioral-initializer-contract~1]
theorem late_one_two_clocks :
    Structural.Admissible (model false false) (fixture .lateOne).unfold ∧
    SingleBirths (fixture .lateOne).unfold (G .lateOne) (V .lateOne) (fun _ _ => some {6}) ∧
    CollectionBirths (fixture .lateOne).unfold (fun _ => {1})
      (H .lateOne) (T .lateOne) (fun _ _ => some {7}) := by
  refine ⟨admitted false false .lateOne (by simp), ?_, ?_⟩
  · intro t x _ _
    rfl
  · rw [permanent_context_iff _ 1 (parent_present .lateOne)]
    rw [empty_initial .lateOne (by simp)]
    exact empty_guard _ _

theorem late_two_rejected_by_inherited :
    Structural.Admissible (model false false) (fixture .lateTwo).unfold ∧
    CollectionBirths (fixture .lateTwo).unfold (fun _ => {1})
      (H .lateTwo) (T .lateTwo) (fun _ _ => some {7}) ∧
    ¬ SingleBirths (fixture .lateTwo).unfold (G .lateTwo) (V .lateTwo) (fun _ _ => some {6}) := by
  refine ⟨admitted false false .lateTwo (by simp), ?_, ?_⟩
  · rw [permanent_context_iff _ 1 (parent_present .lateTwo)]
    rw [empty_initial .lateTwo (by simp)]
    exact empty_guard _ _
  · intro h
    have birth : (fixture .lateTwo).unfold.Starts 1 3 :=
      ((fixture .lateTwo).starts_agrees 1 3).mp (by decide)
    have eq := h 1 3 (by decide : 3 ∈ G .lateTwo 1) birth
    have bad : (6 : Fin 9) = 7 := Set.singleton_injective (Option.some.inj eq)
    contradiction

private theorem initial_six (c : Case) (hc : c = .remove ∨ c = .replace) :
    Guarded (H c 0 1) (T c 0 1) (some {6}) := by
  intro _
  congr 1
  ext y
  dsimp only [T, fixture, Lasso.clock_zero, Lasso.start]
  clear * - c hc y
  decide +revert

-- [utest->req~behavioral-initializer-contract~1]
theorem removal_and_changing_rhs :
    Structural.Admissible (model true false) (fixture .remove).unfold ∧
    CollectionBirths (fixture .remove).unfold (fun _ => {1}) (H .remove) (T .remove)
      (fun t _ => if t = 0 then some {6} else none) ∧ H .remove 1 1 = ∅ := by
  refine ⟨admitted true false .remove (by simp), ?_, ?_⟩
  · rw [permanent_context_iff _ 1 (parent_present .remove)]
    exact initial_six .remove (by simp)
  · ext x
    change headAt .remove 1 1 x ↔ False
    decide +revert

theorem exactly_one_replacement :
    Structural.Admissible (model true true) (fixture .replace).unfold ∧
    CollectionBirths (fixture .replace).unfold (fun _ => {1}) (H .replace) (T .replace)
      (fun t _ => if t = 0 then some {6} else some {7}) ∧
    ¬ SingleBirths (fixture .replace).unfold (G .replace) (V .replace) (fun _ _ => some {6}) := by
  refine ⟨admitted true true .replace (by simp), ?_, ?_⟩
  · rw [permanent_context_iff _ 1 (parent_present .replace)]
    exact initial_six .replace (by simp)
  · intro h
    have birth : (fixture .replace).unfold.Starts 1 4 :=
      ((fixture .replace).starts_agrees 1 4).mp (by decide)
    have eq := h 1 4 (by decide : 4 ∈ G .replace 1) birth
    have bad : (6 : Fin 9) = 8 := Set.singleton_injective (Option.some.inj eq)
    contradiction

-- [utest->req~behavioral-initializer-contract~1]
theorem global_cross_parent :
    Structural.Admissible (model false true) (fixture .cross).unfold ∧
    CollectionBirths (fixture .cross).unfold (fun _ => {0})
      (fun t _ => G .cross t) (fun t _ => V .cross t '' G .cross t)
      (fun _ _ => some {6, 7}) ∧
    ¬ CollectionBirths (fixture .cross).unfold (fun _ => {1, 2})
      (H .cross) (T .cross) (fun _ _ => some {6, 7}) := by
  refine ⟨admitted false true .cross (by simp), ?_, ?_⟩
  · rw [permanent_context_iff _ 0 (root_present .cross)]
    intro _
    congr 1
    ext y
    change (y = 6 ∨ y = 7) ↔ ∃ x, x ∈ G .cross 0 ∧ V .cross 0 x = y
    decide +revert
  · intro h
    have eq := h 0 1 (by simp) ((fixture .cross).unfold.starts_zero 1 |>.mpr (parent_present _ 0))
      ⟨3, by decide⟩
    have bad := Set.ext_iff.mp (Option.some.inj eq) 7 |>.mp (by simp)
    exact (by decide : 7 ∉ T .cross 0 1) bad

theorem global_late_parent :
    Structural.Admissible (model false false) (fixture .lateParent).unfold ∧
    CollectionBirths (fixture .lateParent).unfold (fun _ => {0})
      (fun t _ => G .lateParent t) (fun t _ => V .lateParent t '' G .lateParent t)
      (fun _ _ => none) ∧
    (fixture .lateParent).unfold.Starts 1 2 ∧ (fixture .lateParent).unfold.Starts 1 5 ∧
    V .lateParent 1 5 = 8 := by
  refine ⟨admitted false false .lateParent (by simp), ?_, ?_, ?_, rfl⟩
  · rw [permanent_context_iff _ 0 (root_present .lateParent)]
    have empty : G .lateParent 0 = ∅ := by
      ext x
      change (live .lateParent 0 x = true ∧ 3 ≤ x.val ∧ x.val < 6) ↔ False
      decide +revert
    rw [empty]
    exact empty_guard _ _
  · exact ((fixture .lateParent).starts_agrees 1 2).mp (by decide)
  · exact ((fixture .lateParent).starts_agrees 1 5).mp (by decide)

-- [utest->req~behavioral-initializer-contract~1]
theorem scalar_admission_examples :
    Bounds.scalar (fun (_ : SetExpr (Fin 1) 0) => false) (.literal 1) = true ∧
    Bounds.scalar (fun (_ : SetExpr (Fin 1) 0) => false) (.union (.literal 1) (.literal 1)) = true ∧
    Bounds.scalar (fun (_ : SetExpr (Fin 1) 0) => false) (.union (.literal 1) (.literal 2)) = false ∧
    Bounds.scalar (fun (_ : SetExpr (Fin 1) 0) => false) (.inter (.set (.extent 0)) (.literal 1)) = true ∧
    Bounds.scalar (fun (_ : SetExpr (Fin 1) 0) => false) (.set (.extent 0)) = false ∧
    Bounds.scalar (fun (_ : SetExpr (Fin 1) 0) => true) (.set (.extent 0)) = true ∧
    Bounds.scalar (fun (_ : SetExpr (Fin 1) 0) => false)
      (.integer (.binary .divide (.literal 1) (.literal 0))) = true := by decide

theorem multivalued_abstract_counterexample :
    Guarded ({1, 2} : Set Nat) ((fun x => x) '' {1, 2}) (some {1, 2}) ∧
    ¬ (∀ x ∈ ({1, 2} : Set Nat), (some {1, 2} : Option (Set Nat)) = some {x}) := by
  constructor
  · intro _; simp
  · intro h
    have eq := Option.some.inj (h 1 (by simp))
    have bad := Set.ext_iff.mp eq 2 |>.mp (by simp)
    simp at bad

-- [utest->req~behavioral-initializer-contract~1]
/-- The two inherited/own equations conflict at a nonempty shared birth.
Their late-birth behavior differs because only one clock then fires. -/
theorem distinct_birth_obligations_conflict {U : Type} (heads : Set U)
    (target : U → U) (a b : U) (different : a ≠ b) (present : heads.Nonempty) :
    ¬ (Guarded heads (target '' heads) (some {b}) ∧
      ∀ x ∈ heads, (some {a} : Option (Set U)) = some {target x}) := by
  rintro ⟨collection, singles⟩
  obtain ⟨x, hx⟩ := present
  have each := (Bounds.aggregate_iff_singletons heads target (some {b})
    (by intro S eq; cases eq; exact Set.subsingleton_singleton)).mp collection x hx
  exact different (Set.singleton_injective (Option.some.inj ((singles x hx).trans each.symm)))

/-- Concrete optional declarations with a two-target RHS are well-formed
constraints forcing absence. This is not abstract scalar-admission failure. -/
theorem optional_multitarget_iff_empty {U : Type} (heads : Set U) (target : U → U)
    (one : heads.Subsingleton) (a b : U) (different : a ≠ b) :
    Guarded heads (target '' heads) (some {a, b}) ↔ heads = ∅ := by
  constructor
  · intro guard
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have eq := Option.some.inj (guard ⟨x, hx⟩)
    have ha : a ∈ target '' heads := eq ▸ (by simp : a ∈ ({a, b} : Set U))
    have hb : b ∈ target '' heads := eq ▸ (by simp : b ∈ ({a, b} : Set U))
    obtain ⟨y, hy, hay⟩ := ha
    obtain ⟨z, hz, hbz⟩ := hb
    exact different (hay.symm.trans ((congrArg target (one hy hz)).trans hbz))
  · rintro rfl
    exact empty_guard _ _

/-- A singleton initializer plus a set key forbids two distinct heads. A
mandatory count of two therefore fails independently of scalar admission. -/
theorem set_two_heads_singleton_rejected {U : Type} (heads : Set U) (target : U → U)
    (v x z : U) (key : Set.InjOn target heads) (hx : x ∈ heads) (hz : z ∈ heads)
    (different : x ≠ z) : ¬ Guarded heads (target '' heads) (some {v}) := by
  intro guard
  have each := (Bounds.aggregate_iff_singletons heads target (some {v})
    (by intro S eq; cases eq; exact Set.subsingleton_singleton)).mp guard
  have eq := Set.singleton_injective (Option.some.inj ((each x hx).symm.trans (each z hz)))
  exact different (key hx hz eq)

/-- At the observation/cardinality boundary, two bag heads can both target
one value. The structurally admitted three-head bag fixtures are below. -/
theorem two_bag_heads_singleton :
    Guarded (Set.univ : Set (Fin 2)) ((fun _ : Fin 2 => (0 : Fin 2)) '' Set.univ) (some {0}) ∧
    DPGraph.Predicates.InRange ⟨2, .finite 2⟩ {x : Fin 2 // x ∈ (Set.univ : Set (Fin 2))} := by
  constructor
  · intro _
    simp
  · rw [DPGraph.Predicates.inRange_card]
    decide

/-- Empty parent birth remains possible after narrowing to optional, even
when a nonempty birth cannot realize the two-target initializer. -/
theorem optional_collection_late_outside_rhs :
    Structural.Admissible (model true false) (fixture .lateOne).unfold ∧
    CollectionBirths (fixture .lateOne).unfold (fun _ => {1})
      (H .lateOne) (T .lateOne) (fun _ _ => some {7, 8}) ∧
    (fixture .lateOne).unfold.Starts 1 3 ∧ V .lateOne 1 3 ∉ ({7, 8} : Set (Fin 9)) := by
  refine ⟨admitted true false .lateOne (by simp), ?_, ?_, by decide⟩
  · rw [permanent_context_iff _ 1 (parent_present .lateOne)]
    rw [empty_initial .lateOne (by simp)]
    exact empty_guard _ _
  · exact ((fixture .lateOne).starts_agrees 1 3).mp (by decide)

namespace Bags
open ReferenceObservation ModifierBoundaryExamples DPGraph.Predicates

/-- Starting from a valid snapshot creates a fresh constant trace. This
deliberately tests initialization at a new time zero, not a later observation
within the old parent's lifetime. -/
def restart (c : ModifierBoundaryExamples.Case) (i : Fin 3) : Trace (Fin 5) (Fin 9) :=
  (ModifierBoundaryExamples.fixture true c).state i

theorem restart_admitted (c : ModifierBoundaryExamples.Case) (i : Fin 3) :
    Structural.Admissible (ModifierBoundaryExamples.model true) (restart c i) := by
  have h := ModifierBoundaryExamples.admitted true c
  have clock := (ModifierBoundaryExamples.fixture true c).clock_first i.val (by omega)
  have hs := h.2.states i.val
  have stateEq : ((ModifierBoundaryExamples.fixture true c).clock i.val).1 = i := by
    simpa using clock
  refine ⟨h.1, ?_⟩
  constructor
  · rcases h.2.identities with ⟨a, b, c, d, e, f⟩
    exact ⟨a, b, c, d, e, f⟩
  · intro t
    have hr := h.2.root_live i.val
    change ModifierBoundaryExamples.live c ((ModifierBoundaryExamples.fixture true c).clock i.val).1 0 = true at hr
    change ModifierBoundaryExamples.live c i 0 = true
    simpa only [stateEq] using hr
  · intro t x p hx hp
    change ModifierBoundaryExamples.live c i x = true at hx
    have hx' : x ∈ (ModifierBoundaryExamples.fixture true c).unfold.live i.val := by
      change ModifierBoundaryExamples.live c ((ModifierBoundaryExamples.fixture true c).clock i.val).1 x = true
      simpa only [stateEq] using hx
    have hp' := h.2.parent_live i.val x p hx' hp
    change ModifierBoundaryExamples.live c ((ModifierBoundaryExamples.fixture true c).clock i.val).1 p = true at hp'
    change ModifierBoundaryExamples.live c i p = true
    simpa only [stateEq] using hp'
  · intro t
    rcases hs with ⟨a, b, c, d, e, f, g, h, j, k, l, m, n⟩
    simp only [Structural.Abstracts, Structural.Groups, Structural.Keys,
      Structural.ReferenceCoherent, Trace.raw, Trace.ParentAt, Lasso.unfold,
      stateEq] at a b c d e f g h j k l m n
    exact ⟨a, b, c, d, e, f, g, h, j, k, l, m, n⟩

def heads0 (c : ModifierBoundaryExamples.Case) (i : Fin 3) : Set (Fin 9) :=
  heads (Structural.current (ModifierBoundaryExamples.model true) (restart c i) 0) 2 1
def targets0 (c : ModifierBoundaryExamples.Case) (i : Fin 3) : Set (Fin 9) :=
  targets (Structural.current (ModifierBoundaryExamples.model true) (restart c i) 0) 2 1

theorem targets0_at (c : ModifierBoundaryExamples.Case) (i : Fin 3) (y : Fin 9) :
    y ∈ targets0 c i ↔ ModifierBoundaryExamples.targetAt c i 1 y := by
  have h := ModifierBoundaryExamples.targets_at true c i.val 1 y
  have clock : ((ModifierBoundaryExamples.fixture true c).clock i.val).1 = i := by
    simpa using (ModifierBoundaryExamples.fixture true c).clock_first i.val (by omega)
  simpa only [targets0, targets, assignments, heads, Structural.current,
    Structural.observed, Trace.raw, Trace.ParentAt, restart, Lasso.state, Lasso.unfold,
    clock] using h

private instance (c : ModifierBoundaryExamples.Case) (i : Fin 3) (y : Fin 9) :
    Decidable (ModifierBoundaryExamples.targetAt c i 1 y) := by
  unfold ModifierBoundaryExamples.targetAt ModifierBoundaryExamples.refAt
  infer_instance

-- [utest->req~behavioral-initializer-contract~1]
/-- Both A,A,B and A,B,B are admitted at a fresh parent birth, with the
original exact-three multiplicity and group constraints still enforced. -/
theorem repeated_bag_birth (i : Fin 3) :
    Structural.Admissible (ModifierBoundaryExamples.model true) (restart .bag i) ∧
    CollectionBirths (restart .bag i) (fun _ => {1})
      (fun _ _ => heads0 .bag i) (fun _ _ => targets0 .bag i) (fun _ _ => some {6, 7}) := by
  refine ⟨restart_admitted .bag i, ?_⟩
  rw [permanent_context_iff _ 1 (fun _ => by
    change ModifierBoundaryExamples.live .bag i 1 = true
    decide +revert)]
  intro _
  congr 1
  ext y
  rw [targets0_at]
  change (y = 6 ∨ y = 7) ↔ ModifierBoundaryExamples.targetAt .bag i 1 y
  clear * - i y
  decide +revert

theorem missing_and_extra_rejected :
    Structural.Admissible (ModifierBoundaryExamples.model true) (restart .loseTarget 1) ∧
    Structural.Admissible (ModifierBoundaryExamples.model true) (restart .addTarget 1) ∧
    ¬ Guarded (heads0 .loseTarget 1) (targets0 .loseTarget 1) (some {6, 7}) ∧
    ¬ Guarded (heads0 .addTarget 1) (targets0 .addTarget 1) (some {6, 7}) := by
  refine ⟨restart_admitted _ _, restart_admitted _ _, ?_, ?_⟩
  · intro h
    have present : (heads0 .loseTarget 1).Nonempty := by
      refine ⟨3, ?_⟩
      change (((restart .loseTarget 1).raw (ModifierBoundaryExamples.model true).toEffectiveCore 0).contains 2 1 3)
      dsimp only [Trace.raw, Trace.ParentAt, restart, Lasso.state]
      decide
    have bad := Set.ext_iff.mp (Option.some.inj (h present)) 6 |>.mp (by simp)
    rw [targets0_at] at bad
    exact (by decide : ¬ ModifierBoundaryExamples.targetAt .loseTarget 1 1 6) bad
  · intro h
    have present : (heads0 .addTarget 1).Nonempty := by
      refine ⟨3, ?_⟩
      change (((restart .addTarget 1).raw (ModifierBoundaryExamples.model true).toEffectiveCore 0).contains 2 1 3)
      dsimp only [Trace.raw, Trace.ParentAt, restart, Lasso.state]
      decide
    have extra : 8 ∈ targets0 .addTarget 1 := (targets0_at _ _ _).mpr (by decide)
    have bad := Set.ext_iff.mp (Option.some.inj (h present)) 8 |>.mpr extra
    simp at bad

theorem cardinality_not_waived :
    ¬ CountInRange ⟨3, .finite 3⟩ 0 ∧ ¬ CountInRange ⟨3, .finite 3⟩ 2 ∧
    CountInRange ⟨3, .finite 3⟩ 3 := by decide

theorem repeated_bag_conflicts_with_key :
    ¬ (∀ x ∈ heads0 .bag 0, ∀ z ∈ heads0 .bag 0,
      ModifierBoundaryExamples.target .bag 0 x = ModifierBoundaryExamples.target .bag 0 z → x = z) := by
  intro key
  have h2 : 2 ∈ heads0 .bag 0 := by
    change (((restart .bag 0).raw (ModifierBoundaryExamples.model true).toEffectiveCore 0).contains 2 1 2)
    dsimp only [Trace.raw, Trace.ParentAt, restart, Lasso.state]
    decide
  have h3 : 3 ∈ heads0 .bag 0 := by
    change (((restart .bag 0).raw (ModifierBoundaryExamples.model true).toEffectiveCore 0).contains 2 1 3)
    dsimp only [Trace.raw, Trace.ParentAt, restart, Lasso.state]
    decide
  have bad := key 2 h2 3 h3 rfl
  contradiction

end Bags
end Clafer.Behavioral.Initializers.ContractExamples
