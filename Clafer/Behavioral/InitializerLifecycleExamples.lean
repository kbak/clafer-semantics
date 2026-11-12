module

public import Clafer.Behavioral.InitializerClassification
public import Clafer.Behavioral.ModifierBoundaryExamples

/-! # Structurally admitted initializer lifecycle witnesses

Behavioral §5 Definitions 2–5 and §6.1; accepted #170 cases. Abstract X is
either parented or parentless; its concrete realization inherits the reference.
The field is optional or exactly one. Values 6/7/8 stand for 1/2/7 (or 9):
these clock witnesses use opaque target identities, not integer arithmetic. -/

@[expose] public section
namespace Clafer.Behavioral.Initializers.LifecycleExamples
open Semantics DPGraph.Predicates Candidate ReferenceObservation

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 4096

def model (parented required : Bool) : Structural.Core 5 where
  family := {
    root := 0
    parent d := if d = 0 then none else if d = 4 then
      (if parented then some 1 else none) else if d = 2 then some 1 else some 0
    reference d := if d = 4 then .bag 3 else .basic
    super d := if d = 2 then some 4 else none
    origin d := if d = 0 then .syntheticRoot else .user
    isAbstract d := d == 4
    name _ := ""
    multiplicity d := if d = 2 then (if required then one else optional) else unrestricted
    group _ := {} }
  id d := ⟨d.val⟩
  group _ := unrestricted
  authoredAbstract d := d == 4

theorem wellFormed (p r : Bool) : (model p r).WellFormed := by
  constructor
  · decide +revert
  · cases p <;> cases r <;> decide
  · intro d a h; fin_cases d <;> simp [model] at h
  · intro d e a h; fin_cases d <;> simp [model] at h
  · decide +revert
  · decide +revert
  · decide +revert
  · intro d s o a b edge owner ha hb
    have noRef : (model p r).family.reference d = .basic :=
      (by decide : ∀ p r d s, (model p r).family.super d = some s →
        (model p r).family.reference d = .basic) p r d s edge
    simp [noRef, MCS.ReferenceTo.target] at ha
  · exact ⟨fun d => if d = 0 then 0 else if d = 2 ∨ d = 4 then 2 else 1,
      by decide +revert⟩
  · exact ⟨fun d => if d = 2 then 1 else 0, by decide +revert⟩
  · intro a b h; exact Fin.ext (congrArg DeclId.value h)
  · intro d; cases r <;> fin_cases d <;> simp [model, ValidRange, one, optional, unrestricted]
  · intro d; trivial
  · decide +revert

def pool : Identities (Fin 5) (Fin 9) where
  root := 0
  directType x := if x = 0 then 0 else if x.val < 3 then 1 else
    if x.val < 6 then 2 else 3
  parent x := if x = 0 then none else if x = 3 ∨ x = 4 then some 1 else
    if x = 5 then some 2 else some 0

inductive Case where
  | lateOne | lateTwo | remove | replace | cross | lateParent
  deriving DecidableEq

instance : Fintype Case := ⟨{.lateOne, .lateTwo, .remove, .replace, .cross, .lateParent},
  by intro c; cases c <;> simp⟩

def live (c : Case) (t : Fin 3) (x : Fin 9) : Bool :=
  if x = 0 ∨ x = 1 ∨ 6 ≤ x.val then true
  else if x = 2 then c == .cross || (c == .lateParent && t != 0)
  else match c with
    | .lateOne | .lateTwo => x == 3 && t != 0
    | .remove => x == 3 && t == 0
    | .replace => (x == 3 && t == 0) || (x == 4 && t != 0)
    | .cross => x == 3 || x == 5
    | .lateParent => x == 5 && t != 0

def target (c : Case) (t : Fin 3) (x : Fin 9) : Fin 9 :=
  match c with
  | .lateOne | .remove => 6
  | .lateTwo => 7
  | .replace => if t = 0 then 6 else 8
  | .cross => if x = 3 then 6 else 7
  | .lateParent => 8

def fixture (c : Case) : Lasso (Fin 5) 9 2 where
  identities := pool
  loop := 2
  live := live c
  deref t d x y := d == 4 && decide (3 ≤ x.val ∧ x.val < 6) &&
    live c t x && y == target c t x

private theorem unrestricted_range (A : Type) : InRange unrestricted A :=
  ⟨⟨{ toFun := Fin.elim0, inj' := fun i => Fin.elim0 i }⟩, trivial⟩

private instance (p r : Bool) (c : Case) (t : Fin 3) (d : Fin 5) (x : Fin 9) :
    Decidable (x ∈ (((fixture c).state t).raw (model p r).toEffectiveCore 0).head d) := by
  dsimp only [Trace.raw, Lasso.state, fixture]; infer_instance

private instance (p r : Bool) (c : Case) (t : Fin 3) (d : Fin 5) (a x : Fin 9) :
    Decidable (((fixture c).state t).raw (model p r).toEffectiveCore 0 |>.contains d a x) := by
  dsimp only [Trace.raw, Trace.ParentAt, Lasso.state, fixture]; infer_instance

private theorem state_valid (p r : Bool) (c : Case)
    (allowed : r = false ∨ c = .replace ∨ c = .cross) (t : Fin 3) :
    Structural.StateValid (model p r) ((fixture c).state t) 0 := by
  constructor
  · dsimp only [Configuration.Typed, Trace.raw, Trace.ParentAt, Lasso.state, fixture]
    decide +revert
  · dsimp only [Trace.raw, Lasso.state, fixture]; decide +revert
  · dsimp only [Trace.raw, Lasso.state, fixture]; decide +revert
  · dsimp only [Configuration.Inherits, Trace.raw, Lasso.state, fixture]; decide +revert
  · dsimp only [Structural.Abstracts, Trace.raw, Lasso.state, fixture]; decide +revert
  · dsimp only [Configuration.Parents, ExistsUnique, Trace.raw, Trace.ParentAt, Lasso.state, fixture]
    decide +revert
  · dsimp only [Configuration.References, ExistsUnique, Trace.raw, Trace.ParentAt, Lasso.state, fixture]
    decide +revert
  · intro d e x y z hy hz
    simp only [Lasso.state, fixture, Bool.and_eq_true, beq_iff_eq] at hy hz
    exact hy.2.trans hz.2.symm
  · intro d o _ ho
    exact ((by decide : ∀ p r o, ((model p r).family.reference o).kind ≠ .referenceSet) p r o ho).elim
  · intro d a hd x hx
    by_cases h : d = 2
    · subst d
      have ha : a = 1 := by simpa [model] using hd.symm
      subst a
      rw [inRange_card]
      exact (by decide : ∀ p r c t x, (r = false ∨ c = .replace ∨ c = .cross) →
        live c t x = true → (model p r).toEffectiveCore.Ancestor (pool.directType x) 1 →
        CountInRange ((model p r).family.multiplicity 2)
          (Fintype.card {y : Fin 9 // (((fixture c).state t).raw
            (model p r).toEffectiveCore 0).contains 2 x y})) p r c t x allowed hx.1 hx.2
    · simpa only [model, ite_eq_right h] using unrestricted_range
        {y // (((fixture c).state t).raw (model p r).toEffectiveCore 0).contains d x y}
  · intro d _ x
    exact unrestricted_range _
  · dsimp only [Configuration.DeclarationDisjoint, Trace.raw, Lasso.state, fixture]
    decide +revert
  · intro x hx
    have root : (((fixture c).state t).raw (model p r).toEffectiveCore 0).Reaches 0 := .refl
    have edge : ∀ x, live c t x = true → x ≠ 0 → ∃ a,
        (a = 0 ∨ ((a = 1 ∨ a = 2) ∧ live c t a = true)) ∧ ∃ d,
        (((fixture c).state t).raw (model p r).toEffectiveCore 0).contains d a x := by
      dsimp only [Trace.raw, Trace.ParentAt, Lasso.state, fixture]
      clear * - p r c t
      decide +revert
    by_cases h0 : x = 0
    · subst x; exact root
    obtain ⟨a, ha, he⟩ := edge x hx h0
    rcases ha with rfl | ⟨ha, alive⟩
    · exact root.tail he
    · have parentEdge : (((fixture c).state t).raw (model p r).toEffectiveCore 0).contains 1 0 a := by
        dsimp only [Trace.raw, Trace.ParentAt, Lasso.state, fixture]
        exact (by decide : ∀ p r c t a, (a = 1 ∨ a = 2) → live c t a = true →
          (live c t 0 = true ∧ live c t a = true ∧ pool.parent a = some 0) ∧
          (model p r).toEffectiveCore.Ancestor (pool.directType a) 1 ∧
          (model p r).family.parent 1 ≠ none) p r c t a ha alive
      exact (root.tail ⟨1, parentEdge⟩).tail he

-- [utest->req~behavioral-initializer-contract~1]
theorem admitted (p r : Bool) (c : Case)
    (allowed : r = false ∨ c = .replace ∨ c = .cross) :
    Structural.Admissible (model p r) (fixture c).unfold := by
  refine ⟨wellFormed p r, ?_⟩
  constructor
  · constructor <;> dsimp only [Lasso.unfold, fixture] <;> decide +revert
  · intro t; change live c ((fixture c).clock t).1 0 = true; simp [live]
  · intro t
    exact (by decide : ∀ c t x a, live c t x = true →
      pool.parent x = some a → live c t a = true) c _
  · intro t
    have h := state_valid p r c allowed ((fixture c).clock t).1
    exact ⟨h.typed, h.root_head, h.root_separate, h.inherits, h.abstracts,
      h.parents, h.references, h.coherent, h.keys, h.multiplicities, h.groups,
      h.disjoint, h.reachable⟩

def headAt (c : Case) (i : Fin 3) (a x : Fin 9) : Prop :=
  live c i x = true ∧ 3 ≤ x.val ∧ x.val < 6 ∧ pool.parent x = some a

def targetAt (c : Case) (i : Fin 3) (a y : Fin 9) : Prop :=
  ∃ x, headAt c i a x ∧ y = target c i x

private instance (c : Case) (i : Fin 3) (a x : Fin 9) : Decidable (headAt c i a x) := by
  unfold headAt; infer_instance
private instance (c : Case) (i : Fin 3) (a y : Fin 9) : Decidable (targetAt c i a y) := by
  unfold targetAt; infer_instance

theorem observations (p r : Bool) (c : Case) (t : Nat) (a : Fin 9) :
    heads (Structural.current (model p r) (fixture c).unfold t) 2 a =
      {x | headAt c ((fixture c).clock t).1 a x} ∧
    targets (Structural.current (model p r) (fixture c).unfold t) 2 a =
      {y | targetAt c ((fixture c).clock t).1 a y} := by
  have refs (x y : Fin 9) :
      (Structural.current (model p r) (fixture c).unfold t).deref 2 x y ↔
        3 ≤ x.val ∧ x.val < 6 ∧ live c ((fixture c).clock t).1 x = true ∧
          y = target c ((fixture c).clock t).1 x := by
    change InheritedReference.deref _ _ _ _ _ ↔ _
    rw [InheritedReference.deref_owner (show InheritedReference.Owner (model p r).family 2 4
      from .inherited (by decide +revert) (by decide +revert) (.declared (by decide +revert)))]
    dsimp only [Trace.raw, Lasso.unfold]
    generalize ((fixture c).clock t).1 = i
    dsimp only [fixture]
    clear * - p r c i x y
    decide +revert
  constructor
  · ext x
    change (((fixture c).unfold.raw (model p r).toEffectiveCore t).contains 2 a x) ↔ _
    dsimp only [Trace.raw, Trace.ParentAt, Lasso.unfold]
    generalize ((fixture c).clock t).1 = i
    dsimp only [fixture]
    clear * - p r c a x i
    decide +revert
  · ext y
    simp only [targets, assignments, Set.mem_ofPred_eq, refs]
    change (∃ x, (((fixture c).unfold.raw (model p r).toEffectiveCore t).contains 2 a x) ∧ _) ↔ _
    dsimp only [Trace.raw, Trace.ParentAt, Lasso.unfold]
    generalize ((fixture c).clock t).1 = i
    dsimp only [fixture]
    clear * - p r c a y i
    decide +revert

/-- In the parented fixture the inherited abstract collection observes the
same heads and targets as its sole realization. Thus narrowing the concrete
bound does not silently replace the abstract attachment by an unrelated set. -/
theorem parented_abstract_observations (r : Bool) (c : Case) (t : Nat) (a : Fin 9) :
    heads (Structural.current (model true r) (fixture c).unfold t) 4 a =
      {x | headAt c ((fixture c).clock t).1 a x} ∧
    targets (Structural.current (model true r) (fixture c).unfold t) 4 a =
      {y | targetAt c ((fixture c).clock t).1 a y} := by
  have refs (x y : Fin 9) :
      (Structural.current (model true r) (fixture c).unfold t).deref 4 x y ↔
        3 ≤ x.val ∧ x.val < 6 ∧ live c ((fixture c).clock t).1 x = true ∧
          y = target c ((fixture c).clock t).1 x := by
    change InheritedReference.deref _ _ _ _ _ ↔ _
    rw [InheritedReference.deref_owner (show InheritedReference.Owner (model true r).family 4 4
      from .declared (by decide +revert))]
    dsimp only [Trace.raw, Lasso.unfold]
    generalize ((fixture c).clock t).1 = i
    dsimp only [fixture]
    clear * - r c i x y
    decide +revert
  constructor
  · ext x
    change (((fixture c).unfold.raw (model true r).toEffectiveCore t).contains 4 a x) ↔ _
    dsimp only [Trace.raw, Trace.ParentAt, Lasso.unfold]
    generalize ((fixture c).clock t).1 = i
    dsimp only [fixture]
    clear * - r c a x i
    decide +revert
  · ext y
    simp only [targets, assignments, Set.mem_ofPred_eq, refs]
    change (∃ x, (((fixture c).unfold.raw (model true r).toEffectiveCore t).contains 4 a x) ∧ _) ↔ _
    dsimp only [Trace.raw, Trace.ParentAt, Lasso.unfold]
    generalize ((fixture c).clock t).1 = i
    dsimp only [fixture]
    clear * - r c a y i
    decide +revert

end Clafer.Behavioral.Initializers.LifecycleExamples
