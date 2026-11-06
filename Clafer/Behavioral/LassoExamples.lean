module

public import Clafer.Behavioral.Verification
public import Clafer.Behavioral.Examples

/-! # Checked lasso boundaries

Fixtures reuse the accepted guarded model and identity inventory. Kernel-checked
assertions cover original time zero, nonzero prefixes, the loop edge, retained
bindings, cancellation and malformed exact candidates. Exhaustive small-signal
execution is in `tests/behavioral_lasso.lean`.
-/

@[expose] public section
namespace Clafer.Behavioral.LassoExamples
open Examples

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def cert : Clafer.Verification.CoreCertificate 4 where
  parentRank d := if d = 0 then 0 else if d = 2 then 2 else 1
  superRank _ := 0
  unused _ := false

-- [utest->req~behavioral-lassos~1]
def cycle (loop : Fin 4 := 0) : Lasso (Fin 4) 8 3 where
  identities := pool
  loop := loop
  live k x := x == 0 || x == 5 || x == 6 || (x == 1 && k != 2) || (x == 2 && k == 2) ||
    ((x == 3 || x == 4) && (k == 0 || k == 3))
  deref k d x y := d == 2 && (x == 3 || x == 4) && (k == 0 || k == 3) &&
    y == (if k == 0 then 5 else 6)

-- [proof->req~behavioral-lassos~1]
theorem cycle_valid (loop : Fin 4) : (cycle loop).unfold.Valid model :=
  (Lasso.valid_iff_unfold _ _).mp ((Lasso.checks_iff _ _).mp (by decide +revert))

abbrev A := SetAtom (Fin 4)
abbrev D := SetExpr (Fin 4)
abbrev K := Core A D 0

def evaluate (L : Lasso (Fin 4) 8 3) (a : K) (context : Fin 8 := 3) (t : Nat := 0) : Bool :=
  a.finite L (FiniteObservation.sets model L) (.closed context) (L.clock t)

def fNever : K := .eventually (.or (.not (.atom .parentPresent)) (.not .truth))
def gTrue : K := .weakUntil (.and (.atom .parentPresent) .truth) (.not (.atom .parentPresent))
def liveThis : K := .atom (.source (.inhabited .this))

-- [utest->req~behavioral-finite-checker~1]
/-- F false and its source-negated form G true both discharge at parent death. -/
example : evaluate (cycle 0) fNever = true ∧ evaluate (cycle 0) gTrue = true := by
  simp [evaluate, fNever, gTrue, FiniteObservation.sets, SetAtom.finite]
  decide
/-- Root and top-level parents persist, so F false cannot discharge there. -/
example : evaluate (cycle 0) fNever 0 = false ∧ evaluate (cycle 0) fNever 1 = false := by
  simp [evaluate, fNever, FiniteObservation.sets, SetAtom.finite]
  decide
/-- Context death alone does not cancel X; its parent is still live at state 1. -/
example : evaluate (cycle 0) (.next (.or (.not (.atom .parentPresent)) liveThis)) = false := by
  simp [evaluate, liveThis, FiniteObservation.sets, SetAtom.finite]
  decide
/-- U cannot excuse a false left side before the later cancellation. -/
example : evaluate (cycle 0) (.strongUntil (.not .truth) (.not (.atom .parentPresent))) = false := by
  simp [evaluate, FiniteObservation.sets, SetAtom.finite]
  decide

-- [utest->req~behavioral-lassos~1]
/-- Root starts exactly once, even with a loop to state zero. -/
example : evaluate (cycle 0) (.atom .starts) 0 0 = true ∧
    evaluate (cycle 0) (.atom .starts) 0 4 = false := by
  simp [evaluate, FiniteObservation.sets, SetAtom.finite]
  decide
/-- With loop entry 3 the first arrival is a birth; later self-loop visits are not. -/
example : evaluate (cycle 3) (.atom .starts) 3 3 = true ∧
    evaluate (cycle 3) (.atom .starts) 3 4 = false := by
  simp [evaluate, FiniteObservation.sets, SetAtom.finite]
  decide
/-- With loop entry 2, state 3 is the last live state; the next traversal births it again. -/
example : evaluate (cycle 2) (.atom .ends) 3 3 = true ∧
    evaluate (cycle 2) (.atom .starts) 3 5 = true := by
  simp [evaluate, FiniteObservation.sets, SetAtom.finite]
  decide
/-- Initial history cannot be replaced by a loop predecessor. -/
example : evaluate (cycle 0) (.always (.atom .starts)) 0 = false := by
  simp [evaluate, FiniteObservation.sets, SetAtom.finite]
  decide

-- [utest->req~behavioral-finite-checker~1]
/-- An obligation begun at phase 1 ends at 2. The later reappearance at 3 does
not revive its requirement that the context remain absent. -/
example : evaluate (cycle 0)
    (.weakUntil (.and (.atom .parentPresent) (.not liveThis)) (.not (.atom .parentPresent))) 3 1 = true := by
  simp [evaluate, liveThis, FiniteObservation.sets, SetAtom.finite]
  decide
/-- The same requirement newly begun at phase 3 fails there. -/
example : evaluate (cycle 0)
    (.weakUntil (.and (.atom .parentPresent) (.not liveThis)) (.not (.atom .parentPresent))) 3 3 = false := by
  simp [evaluate, liveThis, FiniteObservation.sets, SetAtom.finite]
  decide

/-- Capture the head identity at phase 3. Its current target changes at phase 0.
Capturing the target set instead retains target 6. -/
def capturedHead : K := .letSet .this
  (.next (.atom (.source (.equal (.step (.deref 2) (.var 0)) (.step (.deref 2) .this)))))
def capturedTarget : K := .letSet (.step (.deref 2) .this)
  (.next (.atom (.source (.equal (.var 0) (.step (.deref 2) .this)))))
example : evaluate (cycle 0) capturedHead 3 3 = true ∧
    evaluate (cycle 0) capturedTarget 3 3 = false := by
  simp [evaluate, capturedHead, capturedTarget, FiniteObservation.sets, SetAtom.finite]
  decide
/-- Captured identities survive absence, while standalone this becomes empty. -/
example : evaluate (cycle 0) (.letSet .this (.next (.atom (.source (.inhabited (.var 0)))))) = true ∧
    evaluate (cycle 0) (.next liveThis) = false := by
  simp [evaluate, liveThis, FiniteObservation.sets, SetAtom.finite]
  decide
/-- Parent navigation can still succeed from the absent context identity. -/
example : evaluate (cycle 0) (.next (.atom (.source (.inhabited (.thisStep .parent))))) = true := by
  simp [evaluate, FiniteObservation.sets, SetAtom.finite]
  decide

-- [utest->req~behavioral-finite-checker~1]
example : evaluate (cycle 0) (.quant .one .this (.next (.atom (.source (.inhabited (.var 0)))))) = true := by
  simp [evaluate, FiniteObservation.sets, SetAtom.finite]
  decide
example : evaluate (cycle 0) (.quant .lone (.extent 2) .truth) = false := by
  simp [evaluate, FiniteObservation.sets, SetAtom.finite]
  decide
example : evaluate (cycle 0) (.quant .all .empty (.not .truth)) = true ∧
    evaluate (cycle 0) (.quant .some .empty .truth) = false ∧
    evaluate (cycle 0) (.quant .no .empty .truth) = true := by
  simp [evaluate, FiniteObservation.sets, SetAtom.finite]
  decide

-- [utest->req~behavioral-lassos~1]
def raw : RawLasso 4 8 3 where
  identities := pool
  loop := 0
  directType _ := pool.directType
  parent _ := pool.parent
  live := (cycle 0).live
  deref := (cycle 0).deref

example : ({raw with loop := 4}).admit = none := by decide
example : Lasso.loopIndex 0 0 = none := by decide
example : ({raw with parent := fun i x => if i = 3 ∧ x = 3 then some 2 else pool.parent x}).admit = none := by decide
example : ({raw with directType := fun i x => if i = 3 ∧ x = 3 then 1 else pool.directType x}).admit = none := by decide

/-- A second target for the same reference occurrence violates functionality. -/
def duplicateTarget : Lasso (Fin 4) 8 3 :=
  {cycle 0 with deref := fun i d x y => (cycle 0).deref i d x y ||
    (i == 0 && d == 2 && x == 3 && y == 6)}
/-- Two distinct bag heads sharing one target remain legal in `cycle`. -/
example : decide (duplicateTarget.checks model) = false := by decide

-- [utest->req~behavioral-finite-checker~1]
example : Verification.checkAt model cert (cycle 0) (some (FiniteAdapter.sets model (cycle 0)))
    (.truth : K) (.closed 3) 0 = .satisfied := by
  simp [Verification.checkAt, FiniteAdapter.sets, FiniteObservation.sets, SetAtom.finite]
  decide
example : Verification.checkAt model cert (cycle 0) (some (FiniteAdapter.sets model (cycle 0)))
    (.not .truth : K) (.closed 3) 0 = .violated := by
  simp [Verification.checkAt, FiniteAdapter.sets, FiniteObservation.sets, SetAtom.finite]
  decide
example : Verification.checkAt model cert duplicateTarget (some (FiniteAdapter.sets model duplicateTarget))
    (.truth : K) (.closed 3) 0 = .violated := by decide
example : Verification.checkAt model cert (cycle 0) (O := Observation.sets model (cycle 0).unfold)
    none (.truth : K) (.closed 3) 0 = .unsupported := by decide
example : Verification.checkRaw model cert (some {raw with loop := 4})
    (fun L => some (FiniteAdapter.sets model L)) (.truth : K) (.closed 3) 0 = .malformed := by decide
-- [utest->req~behavioral-finite-checker~1]
example : (liveThis.attachedFinite (cycle 0) (FiniteObservation.sets model (cycle 0))
    (fun _ => {3})) = true := by
  simp [liveThis, Core.attachedFinite, FiniteObservation.sets, SetAtom.finite]
  decide
example : ((.next liveThis : K).attachedFinite (cycle 0) (FiniteObservation.sets model (cycle 0))
    (fun _ => {3})) = false := by
  simp [liveThis, Core.attachedFinite, FiniteObservation.sets, SetAtom.finite]
  decide
example : Verification.checkAt model cert
    {cycle 0 with identities := {pool with root := 1}}
    (some (FiniteAdapter.sets model {cycle 0 with identities := {pool with root := 1}}))
    (.truth : K) (.closed 3) 0 = .malformed := by decide

-- [utest->req~behavioral-lassos~1]
def selfLoop : Lasso (Fin 4) 8 0 where
  identities := pool
  loop := 0
  live _ := (cycle 0).live 0
  deref _ := (cycle 0).deref 0

example : selfLoop.unfold.Valid model :=
  (Lasso.valid_iff_unfold _ _).mp ((Lasso.checks_iff _ _).mp (by decide))
example : selfLoop.starts (selfLoop.clock 0) 3 = true ∧
    selfLoop.starts (selfLoop.clock 1) 3 = false ∧
    selfLoop.ends (selfLoop.clock 0) 3 = false := by decide

end Clafer.Behavioral.LassoExamples
