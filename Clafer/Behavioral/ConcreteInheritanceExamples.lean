module

public import Clafer.Behavioral.Structural
public import Mathlib.Tactic.FinCases

/-! S10 is a compiler limitation. SoSyM §5.5 and behavioral Definition 1.5
allow inheritance from concrete clafers; source admission retains that case. -/

@[expose] public section
namespace Clafer.Behavioral.ConcreteInheritanceExamples
open Semantics MCS DPGraph.Predicates

def model : Structural.Core 3 where
  family := {
    root := 0
    parent := fun d => if d = 0 then none else some 0
    reference := fun _ => .basic
    super := fun d => if d = 2 then some 1 else none
    origin := fun d => if d = 0 then .syntheticRoot else .user
    isAbstract := fun _ => false
    name := fun _ => ""
    multiplicity := fun _ => unrestricted }
  id d := ⟨d.val⟩
  group _ := unrestricted
  authoredAbstract _ := false

def trace : Trace (Fin 3) (Fin 2) where
  identities := {
    root := 0
    directType := fun x => if x = 0 then 0 else 2
    parent := fun x => if x = 0 then none else some 0 }
  live _ := Set.univ
  deref _ _ _ _ := False

private theorem unrestricted_range (A : Type) : InRange unrestricted A :=
  ⟨⟨{ toFun := Fin.elim0, inj' := fun i => Fin.elim0 i }⟩, trivial⟩

-- [utest->req~behavioral-structural-compatibility~1]
theorem wellFormed : model.WellFormed := by
  constructor
  · decide
  · simp [model]
  · intro d p h; fin_cases d <;> simp [model] at h
  · intro d e p h; fin_cases d <;> simp [model] at h
  · decide
  · decide
  · decide
  · intro d s o a b hs ho ha; cases ha
  · exact ⟨Fin.val, by decide⟩
  · exact ⟨Fin.val, by decide⟩
  · intro a b he; exact Fin.ext (congrArg DeclId.value he)
  · intro d; trivial
  · intro d; trivial
  · intro d; rfl

theorem admitted : Structural.Admissible model trace := by
  refine ⟨wellFormed, ?_⟩
  constructor
  · constructor <;> decide
  · intro t; trivial
  · intro t x p hx hp; trivial
  · intro t
    constructor
    · dsimp only [Configuration.Typed, Trace.raw, Trace.ParentAt, trace]
      simp only [Set.mem_univ, true_and]
      decide
    · dsimp only [Trace.raw, trace]; decide
    · dsimp only [Trace.raw, trace]; decide
    · dsimp only [Configuration.Inherits, Trace.raw, trace]; decide
    · intro d hd; cases hd
    · dsimp only [Configuration.Parents, ExistsUnique, Trace.raw, Trace.ParentAt, trace]
      simp only [Set.mem_univ, true_and]
      decide
    · intro d c hd; cases hd
    · intro d e x y z hy; cases hy
    · intro d o ho hk; cases hk
    · intro d c hc p hp; exact unrestricted_range _
    · intro d hd p; exact unrestricted_range _
    · dsimp only [Configuration.DeclarationDisjoint, Trace.raw, trace]; decide
    · intro x hx
      fin_cases x
      · exact .refl
      · exact Relation.ReflTransGen.single ⟨2, ⟨trivial, trivial, rfl⟩, .refl, by decide⟩

theorem outside_static_guard : ¬ model.toEffectiveCore.Supported := by
  intro h
  have bad := (h.2.2.1 2 1 (by decide)).1
  contradiction

end Clafer.Behavioral.ConcreteInheritanceExamples
