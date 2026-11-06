module

public import Clafer.Behavioral.LassoValidation

/-! # Finite total set observations

This adapter implements the already accepted D1 set grammar (behavioral paper
§5 Definition 5 with the departure recorded in the formula contract), including absent
captured values and current navigation. It does not admit partial static atoms.
-/

@[expose] public section
namespace Clafer.Behavioral
open Semantics
variable {k size last n : Nat}

namespace Step
-- [impl->req~behavioral-finite-checker~1]
def finite (m : EffectiveCore k) (L : Lasso (Fin k) size last) (s : Lasso.Clock last) :
    Step (Fin k) → Fin size → Fin size → Bool
  | .parent, x, p => decide (L.identities.parent x = some p) && L.live s.1 p
  | .child d, p, x => (L.candidate m s.1).contains d p x
  | .deref d, x, y => L.live s.1 x && L.live s.1 y && L.deref s.1 d x y

-- [proof->req~behavioral-finite-checker~1]
theorem finite_agrees (m : EffectiveCore k) (L : Lasso (Fin k) size last)
    (s : Step (Fin k)) (t : Nat) (x y : Fin size) :
    s.finite m L (L.clock t) x y = true ↔ s.relation m L.unfold t x y := by
  cases s <;> simp [finite, relation, Lasso.candidate, Trace.raw, Trace.ParentAt,
    Lasso.unfold, and_assoc]
end Step

namespace SetExpr
-- [impl->req~behavioral-finite-checker~1]
def evaluateStep (m : EffectiveCore k) (L : Lasso (Fin k) size last)
    (ρ : FiniteEnvironment size n) (s : Lasso.Clock last)
    (go : SetExpr (Fin k) n → Finset (Fin size)) : SetExpr (Fin k) n → Finset (Fin size)
  | .empty => ∅
  | .this => if L.live s.1 ρ.this then {ρ.this} else ∅
  | .root => {L.identities.root}
  | .var v => ρ.lookup v
  | .extent d => Finset.univ.filter (fun x => L.live s.1 x = true ∧ m.Ancestor (L.identities.directType x) d)
  | .union a b => go a ∪ go b
  | .inter a b => go a ∩ go b
  | .diff a b => go a \ go b
  | .step r a => Finset.univ.filter (fun y => ∃ x ∈ go a, r.finite m L s x y = true)
  | .thisStep r => Finset.univ.filter (fun y => r.finite m L s ρ.this y = true)
-- [impl->req~behavioral-finite-checker~1]
def finite (m : EffectiveCore k) (L : Lasso (Fin k) size last)
    (ρ : FiniteEnvironment size n) (s : Lasso.Clock last) (a : SetExpr (Fin k) n) : Finset (Fin size) :=
  (measure (fun a : SetExpr (Fin k) n => sizeOf a)).wf.fix (C := fun _ => Finset (Fin size))
    (fun a go => match a with
      | .empty => ∅
      | .this => if L.live s.1 ρ.this then {ρ.this} else ∅
      | .root => {L.identities.root}
      | .var v => ρ.lookup v
      | .extent d => Finset.univ.filter (fun x => L.live s.1 x = true ∧ m.Ancestor (L.identities.directType x) d)
      | .union a b => go a (by change sizeOf _ < sizeOf _; simp +arith) ∪
          go b (by change sizeOf _ < sizeOf _; simp +arith)
      | .inter a b => go a (by change sizeOf _ < sizeOf _; simp +arith) ∩
          go b (by change sizeOf _ < sizeOf _; simp +arith)
      | .diff a b => go a (by change sizeOf _ < sizeOf _; simp +arith) \
          go b (by change sizeOf _ < sizeOf _; simp +arith)
      | .step r a => Finset.univ.filter (fun y =>
          ∃ x ∈ go a (by change sizeOf _ < sizeOf _; simp +arith), r.finite m L s x y = true)
      | .thisStep r => Finset.univ.filter (fun y => r.finite m L s ρ.this y = true)) a

theorem finite_eq (m : EffectiveCore k) (L : Lasso (Fin k) size last)
    (ρ : FiniteEnvironment size n) (s : Lasso.Clock last) (a : SetExpr (Fin k) n) :
    a.finite m L ρ s = evaluateStep m L ρ s (finite m L ρ s) a := by
  unfold finite
  rw [WellFounded.fix_eq]
  cases a <;> rfl

variable (m : EffectiveCore k) (L : Lasso (Fin k) size last)
    (ρ : FiniteEnvironment size n) (s : Lasso.Clock last)

@[simp] theorem finite_empty  :
    finite m L ρ s .empty = ∅ := finite_eq m L ρ s _

@[simp] theorem finite_this  :
    finite m L ρ s .this = if L.live s.1 ρ.this then {ρ.this} else ∅ := finite_eq m L ρ s _

@[simp] theorem finite_root  :
    finite m L ρ s .root = {L.identities.root} := finite_eq m L ρ s _

@[simp] theorem finite_var (v : Fin n) :
    finite m L ρ s (.var v) = ρ.lookup v := finite_eq m L ρ s _

@[simp] theorem finite_extent (d : Fin k) :
    finite m L ρ s (.extent d) = Finset.univ.filter (fun x => L.live s.1 x = true ∧ m.Ancestor (L.identities.directType x) d) := finite_eq m L ρ s _

@[simp] theorem finite_union (a b : SetExpr (Fin k) n) :
    finite m L ρ s (.union a b) = a.finite m L ρ s ∪ b.finite m L ρ s := finite_eq m L ρ s _

@[simp] theorem finite_inter (a b : SetExpr (Fin k) n) :
    finite m L ρ s (.inter a b) = a.finite m L ρ s ∩ b.finite m L ρ s := finite_eq m L ρ s _

@[simp] theorem finite_diff (a b : SetExpr (Fin k) n) :
    finite m L ρ s (.diff a b) = a.finite m L ρ s \ b.finite m L ρ s := finite_eq m L ρ s _

@[simp] theorem finite_step (r : Step (Fin k)) (a : SetExpr (Fin k) n) :
    finite m L ρ s (.step r a) = Finset.univ.filter (fun y => ∃ x ∈ a.finite m L ρ s, r.finite m L s x y = true) := finite_eq m L ρ s _

@[simp] theorem finite_thisStep (r : Step (Fin k)) :
    finite m L ρ s (.thisStep r) = Finset.univ.filter (fun y => r.finite m L s ρ.this y = true) := finite_eq m L ρ s _


-- [proof->req~behavioral-finite-checker~1]
theorem finite_agrees (m : EffectiveCore k) (L : Lasso (Fin k) size last)
    (ρ : FiniteEnvironment size n) (t : Nat) (a : SetExpr (Fin k) n) :
    (↑(a.finite m L ρ (L.clock t)) : Set (Fin size)) = a.eval m L.unfold ρ.realize t := by
  induction a with
  | empty => rw [finite_eq]; simp [evaluateStep, eval]
  | this =>
    rw [finite_eq]
    ext x
    by_cases h : L.live (L.clock t).1 ρ.this = true <;>
      simp [evaluateStep, eval, FiniteEnvironment.realize, Lasso.unfold, h] <;> aesop
  | root => rw [finite_eq]; simp [evaluateStep, eval, Lasso.unfold]
  | var v => rw [finite_eq]; rfl
  | extent d => rw [finite_eq]; ext x; simp [evaluateStep, eval, Trace.raw, Lasso.unfold]
  | union a b ia ib => rw [finite_eq]; simpa only [evaluateStep, eval, Finset.coe_union] using congrArg₂ (· ∪ ·) ia ib
  | inter a b ia ib => rw [finite_eq]; simpa only [evaluateStep, eval, Finset.coe_inter] using congrArg₂ (· ∩ ·) ia ib
  | diff a b ia ib => rw [finite_eq]; simpa only [evaluateStep, eval, Finset.coe_sdiff] using congrArg₂ (· \ ·) ia ib
  | step r a ih =>
    rw [finite_eq]
    ext y
    simp only [evaluateStep, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Step.finite_agrees, eval, Step.image, Set.mem_ofPred_eq]
    have hx (x : Fin size) : x ∈ a.finite m L ρ (L.clock t) ↔ x ∈ a.eval m L.unfold ρ.realize t :=
      Set.ext_iff.mp ih x
    simp only [hx]
  | thisStep r =>
    rw [finite_eq]
    ext y
    simp [evaluateStep, eval, Step.image, Step.finite_agrees, FiniteEnvironment.realize]
end SetExpr

namespace SetAtom
-- [impl->req~behavioral-finite-checker~1]
def finite (m : EffectiveCore k) (L : Lasso (Fin k) size last)
    (ρ : FiniteEnvironment size n) (s : Lasso.Clock last) : SetAtom (Fin k) n → Bool
  | .inhabited a => decide (a.finite m L ρ s).Nonempty
  | .equal a b => decide (a.finite m L ρ s = b.finite m L ρ s)
  | .subset a b => decide (a.finite m L ρ s ⊆ b.finite m L ρ s)

-- [proof->req~behavioral-finite-checker~1]
theorem finite_agrees (m : EffectiveCore k) (L : Lasso (Fin k) size last)
    (ρ : FiniteEnvironment size n) (t : Nat) (a : SetAtom (Fin k) n) :
    a.finite m L ρ (L.clock t) = true ↔ a.eval m L.unfold ρ.realize t := by
  cases a <;> simp only [finite, eval, ← SetExpr.finite_agrees m L ρ t]
  · simp
  · simp
  · simp
end SetAtom

namespace FiniteObservation
-- [impl->req~behavioral-finite-checker~1]
def sets (m : EffectiveCore k) (L : Lasso (Fin k) size last) :
    FiniteObservation (SetAtom (Fin k)) (SetExpr (Fin k)) size last where
  atom a ρ s := a.finite m L ρ s
  domain a ρ s := a.finite m L ρ s

-- [proof->req~behavioral-finite-checker~1]
theorem sets_agrees (m : EffectiveCore k) (L : Lasso (Fin k) size last) :
    (sets m L).Agrees L (Observation.sets m L.unfold) where
  atom a ρ t := a.finite_agrees m L ρ t
  domain d ρ t := d.finite_agrees m L ρ t
end FiniteObservation
end Clafer.Behavioral
