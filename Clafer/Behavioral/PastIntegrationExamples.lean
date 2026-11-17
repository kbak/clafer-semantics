module

public import Clafer.Behavioral.PastExamples
public import Clafer.Behavioral.LassoExamples
public import Clafer.Behavioral.FinitePartial
public import Clafer.Behavioral.InitializerLowering
public import Clafer.Behavioral.InitializerProductionExamples

/-! # Integrated past and initializer regression witnesses

History is observed at absolute times. These kernel-checked examples exercise
mixed future/past, captured bindings, strict partial domains and the guarded
initializer lowering. Structural admission is asserted only by the reused
initializer fixture and the lasso fixture's existing validity theorem.
-/

@[expose] public section
namespace Clafer.Behavioral.PastIntegrationExamples
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

abbrev A := fun (_ : Nat) => Unit
abbrev D := fun (_ : Nat) => Empty
abbrev K := Core A D 0

def total : FiniteObservation A D 1 0 where
  atom _ _ _ := true
  domain d := nomatch d

def run (a : K) (t : Nat := 0) : Bool :=
  a.finite PastExamples.singleState total (.closed 0) t

-- [utest->req~behavioral-past-verification~1]
/-- The same base clock cannot replace the machine's history state. -/
example : run (.previous (.previous .truth)) 1 = false ∧
    run (.previous (.previous .truth)) 2 = true := by
  simp [run, total]

example : run (.eventually (.previous (.previous .truth))) = true ∧
    run (.always (.not (.previous (.previous .truth)))) = false := by
  simp [run, total]
  decide

example : run (.previous (.eventually .truth)) 1 = true ∧
    run (.since (.not .truth) .truth) = true ∧
    run (.since .truth (.previous .truth)) 1 = true := by
  simp [run, total]
  decide

/-- Parent history survives a late child's birth, but not a parent gap. -/
def history : Lasso Unit 3 2 where
  identities := ⟨0, fun _ => (), fun x => if x = 0 then none else if x = 1 then some 0 else some 1⟩
  loop := 2
  live k x := x == 0 || (x == 1 && k != 1) || (x == 2 && k == 2)
  deref _ _ _ _ := false

def mark : FiniteObservation A D 3 2 where
  atom _ _ s := s.1 == 0
  domain d := nomatch d

def parentOnce : K := .since (.atom .parentPresent)
  (.and (.atom .parentPresent) (.atom (.source ())))

-- [utest->req~behavioral-past-formulas~1]
theorem parentOnce_lower : parentOnce = (Formula.once (.atom ()) : Formula A D 0).lower := rfl

example : parentOnce.finite history mark (.closed 2) 2 = false ∧
    parentOnce.finite {history with live := fun k x => x != 2 || k == 2}
      mark (.closed 2) 2 = true := by
  simp [parentOnce, mark]
  decide

/-- A binder keeps the captured head while history changes. Capturing its target
instead retains that target, rather than reevaluating the dereference. -/
example : LassoExamples.evaluate (LassoExamples.cycle 0)
      (.letSet .this (.previous (.atom (.source (.equal (.var 0) .this)))) ) 3 3 = false ∧
    LassoExamples.evaluate (LassoExamples.cycle 0)
      (.quant .one .this (.previous (.atom (.source (.inhabited (.var 0)))))) 3 3 = true := by
  simp [LassoExamples.evaluate, FiniteObservation.sets, SetAtom.finite]
  decide

def partialTrace : Lasso Unit 1 1 where
  identities := ⟨0, fun _ => (), fun _ => none⟩
  loop := 1
  live _ _ := true
  deref _ _ _ _ := false

def missingAtZero : FinitePartialObservation A D 1 1 where
  atom _ _ s := if s.1 == 0 then none else some true
  domain d := nomatch d

def previousProgram : (Formula.previous (.atom ()) : Formula A D 0).Program true where
  domain := .not (.previous (.and (.atom .parentPresent)
    (.not (.atom (.source (.atomDefined ()))))))
  value := .previous (.and (.atom .parentPresent) (.atom (.source (.value ()))))
  domain_eq := rfl
  value_eq := rfl

def negativePreviousProgram : (Formula.previous (.atom ()) : Formula A D 0).Program false where
  domain := previousProgram.domain
  value := .not (.previous (.and (.atom .parentPresent)
    (.not (.not (.atom (.source (.value ())))))))
  domain_eq := rfl
  value_eq := rfl

def onceProgram : (Formula.once (.atom ()) : Formula A D 0).Program true where
  domain := .not (.since (.atom .parentPresent) (.and (.atom .parentPresent)
    (.not (.atom (.source (.atomDefined ()))))))
  value := .since (.atom .parentPresent)
    (.and (.atom .parentPresent) (.atom (.source (.value ()))))
  domain_eq := rfl
  value_eq := rfl

-- [utest->req~behavioral-past-formulas~1]
-- [utest->req~behavioral-past-verification~1]
/-- No preceding state demands no atom, but a missing observed predecessor is
undefined. Once demands the whole active history, even with a true witness now. -/
example : previousProgram.check partialTrace missingAtZero (.closed 0) 0 = .violated ∧
    negativePreviousProgram.check partialTrace missingAtZero (.closed 0) 0 = .satisfied ∧
    previousProgram.check partialTrace missingAtZero (.closed 0) 1 = .undefined ∧
    previousProgram.check partialTrace missingAtZero (.closed 0) 2 = .satisfied ∧
    onceProgram.check partialTrace missingAtZero (.closed 0) 2 = .undefined := by
  simp [Formula.Program.check, previousProgram, negativePreviousProgram, onceProgram,
    FinitePartialObservation.checked]
  decide

-- [utest->req~behavioral-past-formulas~1]
/-- The complete core lowering accepts an undefined RHS after the birth, in the
same admitted inherited model as the independent initializer equation. -/
theorem lowered_initializer_keeps_inactive_guard :
    let o := Initializers.ProductionExamples.initial .undefinedLater
    let τ := Initializers.ProductionExamples.fixed
    let v := Initializers.ProductionExamples.fixedView
    ∀ t x, x ∈ Initializers.attachments τ v o t → x ∈ τ.live t →
      (Initializers.lowerCore o).eval τ
        (Initializers.observation τ v Initializers.ProductionExamples.source).checked (.closed x) t := by
  apply (Initializers.lowerCore_agrees _ _ _ _
    (fun t => Initializers.ProductionExamples.fixed_valid.root_live t)).mpr
  exact Initializers.ProductionExamples.undefined_later_initializes

end Clafer.Behavioral.PastIntegrationExamples
