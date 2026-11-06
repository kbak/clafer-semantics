module

public import Clafer.Behavioral.Snapshot
public import Clafer.Verification.Examples

/-!
# Behavioral identity and snapshot witnesses

Paper §5 Definitions 2–3/5, corrected by T1/T7/T11. Only this fixture module
uses the structural checker examples; the source Trace/Snapshot APIs do not.
All assertions are kernel checked. No native-decide certificate is used.
-/

@[expose] public section
namespace Clafer.Behavioral.Examples
open Semantics DPGraph.Predicates

/-- Root, machine, bag reference, target. All individual/group bounds allow
absence; the two machine identities may replace each other. -/
def model : EffectiveCore 4 where
  family := {
    root := 0
    parent := fun d => if d = 0 then none else if d = 2 then some 1 else some 0
    reference := fun d => if d = 2 then .bag 3 else .basic
    super := fun _ => none
    origin := fun d => if d = 0 then .syntheticRoot else .user
    isAbstract := fun _ => false
    name := fun d => if d = 0 then "Sing" else "C"
    multiplicity := fun _ => unrestricted }
  id d := ⟨d.val⟩
  group _ := unrestricted

private def certificate : Verification.CoreCertificate 4 where
  parentRank d := if d = 0 then 0 else if d = 2 then 2 else 1
  superRank _ := 0
  unused _ := false

theorem model_wellFormed : model.WellFormed :=
  Verification.admitted_wellFormed _ certificate (by decide) (by decide)

theorem model_supported : model.Supported :=
  Verification.admitted_supported _ certificate (by decide)

-- [impl->req~behavioral-identities~1]
def pool : Identities (Fin 4) (Fin 8) where
  root := 0
  directType x := if x = 0 then 0 else if x = 3 ∨ x = 4 then 2
    else if x = 5 ∨ x = 6 then 3 else 1
  parent x := if x = 0 then none else if x = 3 ∨ x = 4 then some 1 else some 0

theorem pool_valid : pool.Valid model := by
  constructor
  · rfl
  · decide
  · decide
  · rfl
  · decide
  · decide

/-- Phase 0: parent 1 and both bag heads; phase 1: heads absent; phase 2:
parent 2 replaces parent 1; phase 3: the original parent and heads reappear.
Both target identities persist. Identity 7 never appears. -/
def phaseLive (k : Fin 4) (x : Fin 8) : Prop :=
  x = 0 ∨ x = 5 ∨ x = 6 ∨ (x = 1 ∧ k ≠ 2) ∨ (x = 2 ∧ k = 2) ∨
    ((x = 3 ∨ x = 4) ∧ (k = 0 ∨ k = 3))

private instance (k : Fin 4) : DecidablePred (phaseLive k) := fun x => by
  unfold phaseLive
  infer_instance

def phaseDeref (k : Fin 4) (d : Fin 4) (x y : Fin 8) : Prop :=
  d = 2 ∧ (x = 3 ∨ x = 4) ∧ (k = 0 ∨ k = 3) ∧ y = if k = 0 then 5 else 6

private def phase (k : Fin 4) : Trace (Fin 4) (Fin 8) where
  identities := pool
  live _ := {x | phaseLive k x}
  deref _ := phaseDeref k

private theorem unrestricted_range (A : Type) : InRange unrestricted A :=
  ⟨⟨{ toFun := fun i => Fin.elim0 i, inj' := fun i => Fin.elim0 i }⟩, trivial⟩

set_option synthInstance.maxSize 2048 in
private theorem phase_valid (k : Fin 4) : (phase k).StateValid model 0 := by
  constructor
  · exact (by
      dsimp only [Configuration.Typed, Trace.raw, Trace.ParentAt, phase, phaseLive, phaseDeref]
      simp only [Set.mem_ofPred_eq]
      decide : ∀ k, ((phase k).raw model 0).Typed model) k
  · exact (by
      dsimp only [Trace.raw, Trace.ParentAt, phase, phaseLive, phaseDeref]
      simp only [Set.mem_ofPred_eq]
      decide : ∀ k x, x ∈ ((phase k).raw model 0).head model.family.root ↔ x = pool.root) k
  · exact (by
      dsimp only [Trace.raw, Trace.ParentAt, phase, phaseLive, phaseDeref]
      simp only [Set.mem_ofPred_eq]
      decide : ∀ k d, d ≠ model.family.root → pool.root ∉ ((phase k).raw model 0).head d) k
  · exact (by
      dsimp only [Configuration.Inherits, Trace.raw, Trace.ParentAt, phase, phaseLive, phaseDeref]
      simp only [Set.mem_ofPred_eq]
      decide : ∀ k, ((phase k).raw model 0).Inherits model) k
  · exact (by
      dsimp only [Configuration.Abstracts, Trace.raw, Trace.ParentAt, phase, phaseLive, phaseDeref]
      simp only [Set.mem_ofPred_eq]
      decide : ∀ k, ((phase k).raw model 0).Abstracts model) k
  · exact (by
      dsimp only [Configuration.Parents, ExistsUnique, Trace.raw, Trace.ParentAt, phase, phaseLive, phaseDeref]
      simp only [Set.mem_ofPred_eq]
      decide : ∀ k, ((phase k).raw model 0).Parents model) k
  · exact (by
      dsimp only [Configuration.References, ExistsUnique, Trace.raw, Trace.ParentAt, phase, phaseLive, phaseDeref]
      simp only [Set.mem_ofPred_eq]
      decide : ∀ k, ((phase k).raw model 0).References model) k
  · exact (by
      dsimp only [Configuration.Keys, Trace.raw, Trace.ParentAt, phase, phaseLive, phaseDeref]
      simp only [Set.mem_ofPred_eq]
      decide : ∀ k, ((phase k).raw model 0).Keys model) k
  · intro d c hc p hp; exact unrestricted_range _
  · intro d hd p hp; exact unrestricted_range _
  · exact (by
      dsimp only [Configuration.DeclarationDisjoint, Trace.raw, Trace.ParentAt, phase, phaseLive, phaseDeref]
      simp only [Set.mem_ofPred_eq]
      decide : ∀ k, ((phase k).raw model 0).DeclarationDisjoint model) k

-- [impl->req~behavioral-traces~1]
def cycling : Trace (Fin 4) (Fin 8) where
  identities := pool
  live t := {x | phaseLive ⟨t % 4, Nat.mod_lt _ (by decide)⟩ x}
  deref t := phaseDeref ⟨t % 4, Nat.mod_lt _ (by decide)⟩

private instance (t : Nat) (x : Fin 8) : Decidable (x ∈ cycling.live t) := by
  simp only [cycling, Set.mem_ofPred_eq]
  infer_instance

private instance (t : Nat) (d : Fin 4) (x y : Fin 8) :
    Decidable (cycling.deref t d x y) := by
  unfold cycling phaseDeref
  infer_instance

private instance (t : Nat) (x : Fin 8) : Decidable (cycling.Ends t x) := by
  unfold Trace.Ends
  infer_instance

private instance (t : Nat) (p x : Fin 8) : Decidable (cycling.ParentAt t p x) := by
  unfold Trace.ParentAt
  infer_instance

-- [proof->req~behavioral-traces~1]
-- [proof->req~behavioral-identities~1]
theorem cycling_valid : cycling.Valid model where
  identities := pool_valid
  root_live _ := Or.inl rfl
  parent_live t :=
    (by decide : ∀ k x p, phaseLive k x → pool.parent x = some p → phaseLive k p)
      ⟨t % 4, Nat.mod_lt _ (by decide)⟩
  states t := by
    have h := phase_valid ⟨t % 4, Nat.mod_lt _ (by decide)⟩
    exact ⟨h.typed, h.root_head, h.root_separate, h.inherits, h.abstracts,
      h.parents, h.references, h.keys, h.multiplicities, h.groups, h.disjoint⟩

-- [proof->req~behavioral-snapshot-bridge~1]
theorem cycling_admissible : cycling.Admissible model :=
  ⟨model_wellFormed, model_supported, cycling_valid⟩

theorem every_snapshot (t : Nat) :
    StructuralSatisfies model (cycling.snapshot cycling_valid t) :=
  cycling.admissible_projection cycling_admissible t

private instance (t : Nat) (d : Fin 4) (x y : cycling.Live t) :
    Decidable ((cycling.snapshot cycling_valid t).deref d x y) :=
  inferInstanceAs (Decidable (cycling.deref t d x.val y.val))

-- [utest->req~behavioral-traces~1]
-- [utest->req~behavioral-identities~1]
example : cycling.Starts 0 3 ∧ cycling.Ends 0 3 ∧ cycling.Starts 3 3 := by
  constructor
  · exact (cycling.starts_zero 3).mpr (by decide)
  · exact ⟨by decide, (cycling.starts_succ 2 3).mpr (by decide)⟩

example : cycling.ParentAt 0 1 3 ∧ cycling.ParentAt 3 1 3 := by decide

/-- Replacement is a different parent identity. The old child is absent while
its fixed parent is absent; return of identity 1 restores the original ownership. -/
example : 1 ∉ cycling.live 2 ∧ 2 ∈ cycling.live 2 ∧ 3 ∉ cycling.live 2 := by decide

example : cycling.Starts 2 2 ∧ cycling.Ends 2 2 ∧ cycling.Starts 3 1 := by
  exact ⟨(cycling.starts_succ 1 2).mpr (by decide), by decide,
    (cycling.starts_succ 2 1).mpr (by decide)⟩

example : cycling.deref 0 2 3 5 ∧ cycling.deref 3 2 3 6 ∧
    ¬ cycling.deref 3 2 3 5 := by decide

-- [utest->req~behavioral-snapshot-bridge~1]
example : ∀ t, 7 ∉ cycling.live t := by
  intro t
  exact (by decide : ∀ k, ¬ phaseLive k 7) ⟨t % 4, Nat.mod_lt _ (by decide)⟩

/-- The pool presentation fails full ambient coverage, although every live
snapshot satisfies the structural meaning. -/
example : ¬ (cycling.raw model 0).Rooted model := by
  simp only [Configuration.Rooted, Trace.raw, Set.mem_ofPred_eq]
  decide

-- [utest->req~behavioral-identities~1]
/-- A mutation retaining the old child while replacing its parent is invalid. -/
def orphan : Trace (Fin 4) (Fin 8) :=
  { cycling with live := fun t => {x | x ∈ cycling.live t ∨ (t = 2 ∧ x = 3)} }

example : ¬ orphan.Valid model := by
  intro h
  have bad := h.parent_live 2 3 1 (Or.inr ⟨rfl, rfl⟩) rfl
  exact (by simp only [orphan, Set.mem_ofPred_eq]; decide : ¬ (1 ∈ orphan.live 2)) bad

/-- Even a gap cannot permit changing the parent of the same identity. This
rejects a per-state parent-table mutation independently of snapshot checks. -/
example : ¬ ∃ τ : Trace (Fin 4) (Fin 8), τ.ParentAt 0 1 3 ∧ τ.ParentAt 3 2 3 := by
  rintro ⟨τ, hi, hj⟩
  exact (by decide : (1 : Fin 8) ≠ 2) (τ.parent_stable hi hj)

-- [utest->req~behavioral-identities~1]
-- [utest->req~behavioral-snapshot-bridge~1]
/-- Both bag heads survive the live restriction and share the same target. -/
example : ∃ x y z : cycling.Live 0, x ≠ y ∧
    (cycling.snapshot cycling_valid 0).deref 2 x z ∧
    (cycling.snapshot cycling_valid 0).deref 2 y z := by
  exact ⟨⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩,
    cycling.snapshot_distinct 0 (by decide),
    (show cycling.deref 0 2 3 5 from by decide),
    (show cycling.deref 0 2 4 5 from by decide)⟩

/-- A target-only representation would identify these two occurrences. -/
example : ¬ Function.Injective (fun _ : {x : cycling.Live 0 //
    (cycling.snapshot cycling_valid 0).deref 2 x ⟨5, by decide⟩} => (5 : Fin 8)) := by
  intro h
  let a : {x : cycling.Live 0 //
    (cycling.snapshot cycling_valid 0).deref 2 x ⟨5, by decide⟩} := ⟨⟨3, by decide⟩, (show cycling.deref 0 2 3 5 from by decide)⟩
  let b : {x : cycling.Live 0 //
    (cycling.snapshot cycling_valid 0).deref 2 x ⟨5, by decide⟩} := ⟨⟨4, by decide⟩, (show cycling.deref 0 2 4 5 from by decide)⟩
  have he : (3 : Fin 8) = 4 := congrArg (fun x => x.val.val) (h (a₁ := a) (a₂ := b) rfl)
  exact (by decide : (3 : Fin 8) ≠ 4) he

-- [utest->req~behavioral-identities~1]
-- [utest->req~behavioral-snapshot-bridge~1]
/-- The head fiber has two elements; replacing it by its target union loses one. -/
example : InRange ⟨2, .finite 2⟩
    {x : cycling.Live 0 // (cycling.snapshot cycling_valid 0).contains 2 ⟨1, by decide⟩ x} := by
  apply (inRange_iff _ (cycling.fiberEquiv cycling_valid 0 2 ⟨1, by decide⟩)).mpr
  let : DecidablePred (fun x : Fin 8 => (cycling.raw model 0).contains 2 1 x) := fun x => by
    dsimp only [Trace.raw, Trace.ParentAt]
    infer_instance
  rw [inRange_card]
  decide

example : ¬ InRange ⟨2, .finite 2⟩
    {y : Fin 8 // cycling.deref 0 2 3 y ∨ cycling.deref 0 2 4 y} := by
  rw [inRange_card]
  decide

-- [utest->req~behavioral-traces~1]
/-- Targets may change without a new lifetime or a different head. -/
example : cycling.deref 3 2 3 6 ∧ cycling.deref 4 2 3 5 ∧ ¬ cycling.Starts 4 3 := by
  exact ⟨by decide, by decide, fun h => (cycling.starts_succ 3 3).mp h |>.2 (by decide)⟩

/-- Invalid dereferences remain visible in the raw data and are rejected. -/
def dangling : Trace (Fin 4) (Fin 8) :=
  { cycling with deref := fun t d x y => cycling.deref t d x y ∨
      (t = 1 ∧ d = 2 ∧ x = 3 ∧ y = 7) }

example : ¬ dangling.Valid model := by
  intro h
  have bad := ((h.states 1).typed.2 2 3 7 (Or.inr ⟨rfl, rfl, rfl, rfl⟩)).1.1
  exact (by decide : 3 ∉ cycling.live 1) bad

namespace ConstantBag
open Verification.Examples

def identities : Identities (Fin 3) (Fin 4) where
  root := 0
  directType x := if x = 0 then 0 else if x = 1 then 1 else 2
  parent x := if x = 0 then none else some 0

-- [proof->req~behavioral-snapshot-bridge~1]
/-- Concrete direct-type and actual-parent witnesses for an existing structural
bag configuration. Both repeated-target heads are retained by the converse. -/
theorem correspondence : StaticCorrespondence (refs false) (Verification.realize bag) identities := by
  constructor
  · constructor <;> decide
  · rfl
  · dsimp only [Verification.realize]; decide
  · dsimp only [Verification.realize]; decide

example : correspondence.constant.Admissible (refs false) :=
  correspondence.constant_admissible refs_valid refs_supported bag_satisfies

end ConstantBag

namespace ConstantInheritance
open Verification.Examples

def identities : Identities (Fin 6) (Fin 4) where
  root := 0
  directType x := if x = 0 then 0 else if x = 1 then 3 else if x = 2 then 4 else 5
  parent x := if x = 0 then none else if x = 3 then some 1 else some 0

-- [proof->req~behavioral-snapshot-bridge~1]
/-- The direct-type witness reconstructs both overlapping abstract super extents;
parentless abstract roles do not erase actual root/nested ownership. -/
theorem correspondence : StaticCorrespondence inheritance (Verification.realize nested) identities := by
  constructor
  · constructor <;> decide
  · rfl
  · dsimp only [Verification.realize]; decide
  · dsimp only [Verification.realize]; decide

-- [utest->req~behavioral-snapshot-bridge~1]
example : correspondence.constant.Admissible inheritance :=
  correspondence.constant_admissible inheritance_valid inheritance_supported nested_satisfies

end ConstantInheritance
end Clafer.Behavioral.Examples
