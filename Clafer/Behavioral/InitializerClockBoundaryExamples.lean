module

public import Clafer.Behavioral.InitializerClockExamples
public import Clafer.Behavioral.AbstractMultiplicityExamples

/-! # Explicit clocks: bags, rebirth and the static compatibility boundary

Behavioral §5 Definitions 3–5 / §6.1 and #194. These witnesses use production
structural views of an admitted exact-three bag, including inherited references.
-/

@[expose] public section
namespace Clafer.Behavioral.Initializers.ClockBoundaryExamples
open DPGraph.Predicates ModifierBoundaryExamples

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 4096

def τ (c : Case) := (fixture true c).unfold

theorem owner : InheritedReference.Owner (model true).family 2 4 :=
  .inherited (by decide) (by decide) (.declared (by decide))

noncomputable def view (c : Case) : View (Fin 9) :=
  Structure.view (model true) (τ c) (admitted true c).2 owner

def equation (clock : Initializers.Clock) : Obligation (Fin 5) Unit :=
  ⟨2, .parent, clock, ()⟩

def source := ClockExamples.source

-- [utest->req~initializer-clock-selection~1]
theorem explicit_elaboration :
    Structure.elaborate (model true) 2 .initial (some ⟨3, .finite 3⟩) false () (some .instance) =
      .ok (equation .instanceBirth) ∧
    Structure.elaborate (model true) 2 .initial (some ⟨3, .finite 3⟩) false () (some .collection) =
      .ok (equation .parentBirth) := ⟨rfl, rfl⟩

private theorem target_eq (c : Case) (t : Nat) (x : Fin 9) (hx : x ∈ (view c).instances t) :
    (view c).target t x = target c ((fixture true c).clock t).1 x := by
  have h := Structure.target_link (model true) (τ c) (admitted true c).2 owner t x hx
  rw [InheritedReference.deref_owner owner] at h
  have eq := h.2
  change (_ && _ && _ && (_ == _)) = true at eq
  simp only [Bool.and_eq_true, beq_iff_eq] at eq
  exact eq.2

private theorem parent_eq (c : Case) (t : Nat) (p : Fin 9) (hp : p ∈ (view c).contexts t) : p = 1 := by
  change live c ((fixture true c).clock t).1 p = true ∧
    (model true).toEffectiveCore.Ancestor (pool.directType p) 1 at hp
  exact (by decide : ∀ c i p, live c i p = true ∧
    (model true).toEffectiveCore.Ancestor (pool.directType p) 1 → p = 1) c _ p hp

private theorem targets_eq (c : Case) (t : Nat) :
    (view c).targets t 1 = {y | targetAt c ((fixture true c).clock t).1 1 y} := by
  change (Structure.view (model true) (τ c) (admitted true c).2 owner).targets t 1 = _
  rw [Structure.target_image (model true) (τ c) (admitted true c).2 owner t 1]
  exact Set.ext (fun y => (targets_at true c t 1 y))

/-- Every fixture begins with a complete three-head collection at targets 6/7. -/
theorem initial_collection (c : Case) : Candidate.Guarded ((view c).heads 0 1)
    ((view c).targets 0 1) (some {6, 7}) := by
  intro _
  rw [targets_eq]
  congr 1
  ext y
  change (y = 6 ∨ y = 7) ↔ targetAt c 0 1 y
  dsimp only [targetAt, refAt]
  clear * - c y
  decide +revert

-- [utest->req~initializer-clock-selection~1]
/-- A,A,B and A,B,B are the same collection target set. Changes after parent
birth are irrelevant to the collection clock; head multiplicity remains three. -/
theorem duplicate_bag_collection : Meaning (τ .bag) (view .bag) (source (some {6, 7}))
    (equation .parentBirth) := by
  intro t p hp birth
  have eq := parent_eq _ _ _ hp
  subst p
  have permanent (j : Nat) : 1 ∈ (τ .bag).live j := by
    change live .bag ((fixture true .bag).clock j).1 1 = true
    simp [live]
  have zero : t = 0 := by
    rcases birth.2 with zero | ⟨k, _, absent⟩
    · exact zero
    · exact (absent (permanent k)).elim
  subst t
  exact initial_collection .bag

-- [utest->req~initializer-clock-selection~1]
/-- Three concrete heads cannot each equal the whole two-target RHS. This is
an admitted constraint conflict, not an abstract scalar-admission diagnostic. -/
theorem plural_each_conflicts :
    ¬ Meaning (τ .bag) (view .bag) (source (some {6, 7})) (equation .instanceBirth) := by
  intro h
  have member : 2 ∈ (view .bag).instances 0 := by
    change live .bag 0 2 = true ∧ (model true).toEffectiveCore.Ancestor (pool.directType 2) 2
    decide
  have birth : (τ .bag).Starts 0 2 := (Trace.starts_zero _ _).mpr member.1
  have bad := h 0 2 member birth
  change some ({6, 7} : Set (Fin 9)) = some {(view .bag).target 0 2} at bad
  rw [target_eq _ _ _ member] at bad
  have singleton := Set.ext_iff.mp (Option.some.inj bad) 7 |>.mp (by simp)
  change (7 : Fin 9) = 6 at singleton
  contradiction

-- [utest->req~initializer-clock-selection~1]
/-- A renewed head lifetime requires a renewed value. The earlier correct
singleton equation cannot discharge the rebirth. -/
theorem head_rebirth_rechecks :
    (τ .headGap).Starts 2 2 ∧
    ¬ Meaning (τ .headGap) (view .headGap)
      (fun _ ρ _ => some {if ρ.this = 1 then (6 : Fin 9) else 8}) (equation .instanceBirth) := by
  have birth : (τ .headGap).Starts 2 2 :=
    ((fixture true .headGap).starts_agrees 2 2).mp (by decide)
  refine ⟨birth, ?_⟩
  intro h
  have member : 2 ∈ (view .headGap).instances 2 := by
    change live .headGap 2 2 = true ∧ (model true).toEffectiveCore.Ancestor (pool.directType 2) 2
    decide
  have bad := h 2 2 member birth
  change some ({6} : Set (Fin 9)) = some {(view .headGap).target 2 2} at bad
  rw [target_eq _ _ _ member] at bad
  have eq : (6 : Fin 9) = 7 := Set.singleton_injective (Option.some.inj bad)
  contradiction

-- [utest->req~initializer-clock-selection~1]
/-- The whole parent collection is checked again after parent absence, using
the same original parent frame and the new complete target image. -/
theorem parent_rebirth_rechecks :
    (τ .parentGap).Starts 2 1 ∧
    ¬ Meaning (τ .parentGap) (view .parentGap) (source (some {6, 7})) (equation .parentBirth) := by
  have birth : (τ .parentGap).Starts 2 1 :=
    ((fixture true .parentGap).starts_agrees 2 1).mp (by decide)
  refine ⟨birth, ?_⟩
  intro h
  have context : 1 ∈ (view .parentGap).contexts 2 := by
    change live .parentGap 2 1 = true ∧ (model true).toEffectiveCore.Ancestor (pool.directType 1) 1
    decide
  have head : 2 ∈ (view .parentGap).heads 2 1 := by
    change (((fixture true .parentGap).unfold).raw (model true).toEffectiveCore 2).contains 2 1 2
    dsimp only [Trace.raw, Trace.ParentAt, Lasso.unfold]
    decide
  have bad := h 2 1 context birth ⟨2, head⟩
  change some ({6, 7} : Set (Fin 9)) = some ((view .parentGap).targets 2 1) at bad
  rw [targets_eq] at bad
  have missing := Set.ext_iff.mp (Option.some.inj bad) 6 |>.mp (by simp)
  change targetAt .parentGap 2 1 6 at missing
  have noSix : ¬ targetAt .parentGap 2 1 6 := by dsimp only [targetAt, refAt]; decide
  exact noSix missing


-- [utest->req~initializer-clock-selection~1]
/-- The head's first birth has the requested value, before its checked rebirth
at a different target. The parent collection likewise succeeds before its gap. -/
theorem initial_values_before_rebirth :
    (view .headGap).target 0 2 = 6 ∧
    Candidate.Guarded ((view .parentGap).heads 0 1) ((view .parentGap).targets 0 1)
      (some {6, 7}) := by
  refine ⟨?_, initial_collection .parentGap⟩
  have member : 2 ∈ (view .headGap).instances 0 := by
    change live .headGap 0 2 = true ∧ (model true).toEffectiveCore.Ancestor (pool.directType 2) 2
    decide
  rw [target_eq _ _ _ member]
  rfl

namespace Constant
open ContractExamples.Bags

noncomputable def v : View (Fin 9) :=
  Structure.view (model true) (restart .bag 0) (restart_admitted .bag 0).2 owner

private theorem targets (t : Nat) : v.targets t 1 = targets0 .bag 0 := by
  rw [v, Structure.target_image (model true) (restart .bag 0) (restart_admitted .bag 0).2 owner t 1]
  rfl

-- [utest->req~initializer-clock-selection~1]
-- [utest->req~behavioral-structural-compatibility~1]
/-- On an admitted constant exact-three bag with A,A,B, aggregate equality
succeeds at every state while explicit per-instance initialization fails.
This rules out an unconditional static-first erasure of an explicit clock. -/
theorem static_disagreement :
    Structural.Admissible (model true) (restart .bag 0) ∧
    Meaning (restart .bag 0) v (source (some {6, 7})) (equation .everyLive) ∧
    ¬ Meaning (restart .bag 0) v (source (some {6, 7})) (equation .instanceBirth) := by
  refine ⟨restart_admitted .bag 0, ?_, ?_⟩
  · intro t p hp _ _
    have eq : p = 1 := by
      change live .bag 0 p = true ∧ (model true).toEffectiveCore.Ancestor (pool.directType p) 1 at hp
      exact (by decide : ∀ p, live .bag 0 p = true ∧
        (model true).toEffectiveCore.Ancestor (pool.directType p) 1 → p = 1) p hp
    subst p
    change some ({6, 7} : Set (Fin 9)) = some (v.targets t 1)
    rw [targets]
    congr 1
    ext y
    rw [targets0_at]
    change (y = 6 ∨ y = 7) ↔ targetAt .bag 0 1 y
    dsimp only [targetAt, refAt]
    decide +revert
  · intro h
    have member : 2 ∈ v.instances 0 := by
      change live .bag 0 2 = true ∧ (model true).toEffectiveCore.Ancestor (pool.directType 2) 2
      decide
    have bad := h 0 2 member ((Trace.starts_zero _ _).mpr member.1)
    change some ({6, 7} : Set (Fin 9)) = some {v.target 0 2} at bad
    have eq := Option.some.inj bad
    have a : (6 : Fin 9) = v.target 0 2 := Set.ext_iff.mp eq 6 |>.mp (by simp)
    have b : (7 : Fin 9) = v.target 0 2 := Set.ext_iff.mp eq 7 |>.mp (by simp)
    have impossible := a.trans b.symm
    contradiction

end Constant

namespace Plural
open AbstractMultiplicityExamples

theorem referenceOwner (r : Option Range) :
    InheritedReference.Owner (core r).source.family 3 1 :=
  .inherited (s := 2) rfl rfl (.inherited (s := 1) rfl rfl (.declared (by intro h; cases h)))

noncomputable def v (r : Option Range) :=
  Structure.view (core r).source (trace (fun _ => true)) (structural_valid r _) (referenceOwner r)

-- [utest->req~initializer-clock-selection~1]
/-- A nonvacuous plural concrete per-instance initializer: four heads under
one parent all target root. Duplicate targets do not require distinct RHSs.
The abstract's finite/unbounded aggregate interval is independent of this clock. -/
theorem each_elaboration (r : Option Range) :
    Structure.elaborate (core r).source 3 .initial (some ⟨4, .finite 4⟩) false ()
      (some .instance) = .ok (⟨3, .parent, .instanceBirth, ()⟩ : Obligation (Fin 7) Unit) := by
  rfl

-- [utest->req~initializer-clock-selection~1]
theorem each_duplicate_targets (r : Option Range) :
    3 ∈ (v r).instances 0 ∧
    Meaning (trace (fun _ => true)) (v r)
      (fun (_ : Unit) _ _ => some {0}) ⟨3, .parent, .instanceBirth, ()⟩ := by
  constructor
  · change present true 3 ∧ (core r).source.toEffectiveCore.Ancestor (pool.directType 3) 3
    exact ⟨Or.inr (Or.inr (Or.inl (by decide))), .refl⟩
  · intro t x hx _
    have link := Structure.target_link (core r).source (trace (fun _ => true))
      (structural_valid r _) (referenceOwner r) t x hx
    rw [InheritedReference.deref_owner (referenceOwner r)] at link
    have value : (v r).target t x = 0 := link.2.2.2.2
    have parent : pool.parent x = some 1 := by
      have typed := hx.2
      exact (by decide : ∀ x, (core none).source.toEffectiveCore.Ancestor (pool.directType x) 3 →
        pool.parent x = some 1) x typed
    change (pool.parent x).bind (fun _ => some ({0} : Set (Fin 11))) = some {(v r).target t x}
    rw [parent, value]
    rfl

-- [utest->req~initializer-clock-selection~1]
theorem finite_unbounded_admitted :
    AbstractMultiplicity.Admissible (core (some ⟨0, .finite 8⟩)) (trace (fun _ => true)) ∧
    AbstractMultiplicity.Admissible (core (some unrestricted)) (trace (fun _ => true)) := by
  constructor
  · refine ⟨wellFormed _ (by decide), structural_valid _ _, fun t => ?_⟩
    rw [at_iff]
    decide
  · refine ⟨wellFormed _ (by decide), structural_valid _ _, fun t => ?_⟩
    rw [at_iff]
    decide

end Plural
end Clafer.Behavioral.Initializers.ClockBoundaryExamples
