module

public import Clafer.Behavioral.InitializerTransportExamples

/-! # Resolved Box/flag/x source witness

The distinct resolved declarations in #171's temporal-condition example.
Box and x are optional and vanish after time zero; flag is optional and absent.
Target identities 5/6 stand for distinct values 1/2. The value condition itself
returns mathematical integers, without requiring a finite integer universe.
-/

@[expose] public section
namespace Clafer.Behavioral.Initializers.SourceExamples
open Semantics DPGraph.Predicates Transport

/-- Root 0, Box 1, x 2, value 3, flag 4. -/
def model : EffectiveCore 5 where
  family := {
    root := 0
    parent d := if d = 0 then none else if d = 2 ∨ d = 4 then some 1 else some 0
    reference d := if d = 2 then .set 3 else .basic
    super _ := none
    origin d := if d = 0 then .syntheticRoot else .user
    isAbstract _ := false
    name d := if d = 1 then "Box" else if d = 2 then "x" else if d = 4 then "flag" else ""
    multiplicity d := if d = 1 ∨ d = 2 ∨ d = 4 then optional else unrestricted }
  id d := ⟨d.val⟩
  group _ := unrestricted

def pool : Identities (Fin 5) (Fin 8) where
  root := 0
  directType x := if x = 0 then 0 else if x = 3 then 2 else if x = 4 then 4
    else if x = 5 ∨ x = 6 then 3 else 1
  parent x := if x = 0 then none else if x = 3 ∨ x = 4 then some 1 else some 0

def present (first : Bool) (x : Fin 8) : Prop :=
  x = 0 ∨ x = 5 ∨ x = 6 ∨ ((x = 1 ∨ x = 3) ∧ first = true)

instance (b : Bool) : DecidablePred (present b) := fun _ => by unfold present; infer_instance

def state (first : Bool) : Trace (Fin 5) (Fin 8) where
  identities := pool
  live _ := {x | present first x}
  deref _ d x y := d = 2 ∧ x = 3 ∧ first = true ∧ y = 6

private def certificate : Verification.CoreCertificate 5 where
  parentRank d := if d = 0 then 0 else if d = 2 ∨ d = 4 then 2 else 1
  superRank _ := 0
  unused _ := false

theorem wellFormed : model.WellFormed :=
  Verification.admitted_wellFormed _ certificate (by decide) (by decide)

theorem supported : model.Supported :=
  Verification.admitted_supported _ certificate (by decide)

private theorem unrestricted_range (A : Type) : InRange unrestricted A :=
  ⟨⟨{ toFun := Fin.elim0, inj' := fun i => Fin.elim0 i }⟩, trivial⟩

private theorem optional_range (S : Set (Fin 8)) (one : S.Subsingleton) :
    InRange optional {x // x ∈ S} :=
  ⟨⟨{ toFun := Fin.elim0, inj' := fun i => Fin.elim0 i }⟩,
    ⟨{ toFun := fun _ => 0, inj' := fun x y _ => Subtype.ext (one x.property y.property) }⟩⟩

set_option synthInstance.maxSize 4096 in
private theorem state_valid (b : Bool) : (state b).StateValid model 0 := by
  constructor
  · dsimp only [Configuration.Typed, Trace.raw, Trace.ParentAt, state]
    simp only [Set.mem_ofPred_eq]
    decide +revert
  · dsimp only [Trace.raw, state]; simp only [Set.mem_ofPred_eq]; decide +revert
  · dsimp only [Trace.raw, state]; simp only [Set.mem_ofPred_eq]; decide +revert
  · dsimp only [Configuration.Inherits, Trace.raw, state]; simp only [Set.mem_ofPred_eq]; decide +revert
  · dsimp only [Configuration.Abstracts, Trace.raw, state]; simp only [Set.mem_ofPred_eq]; decide +revert
  · dsimp only [Configuration.Parents, ExistsUnique, Trace.raw, Trace.ParentAt, state]; simp only [Set.mem_ofPred_eq]; decide +revert
  · dsimp only [Configuration.References, ExistsUnique, Trace.raw, state]; simp only [Set.mem_ofPred_eq]; decide +revert
  · dsimp only [Configuration.Keys, Trace.raw, Trace.ParentAt, state]; simp only [Set.mem_ofPred_eq]; decide +revert
  · intro d c hd p hp
    by_cases small : d = 1 ∨ d = 2 ∨ d = 4
    · change InRange (if d = 1 ∨ d = 2 ∨ d = 4 then optional else unrestricted) _
      rw [ite_eq_left small]
      apply optional_range {x | (state b).ParentAt 0 p x ∧
        model.Ancestor (pool.directType x) d ∧ model.family.parent d ≠ none}
      dsimp only [Set.Subsingleton, Set.mem_ofPred_eq, Trace.ParentAt, state]
      clear hd hp c
      decide +revert
    · change InRange (if d = 1 ∨ d = 2 ∨ d = 4 then optional else unrestricted) _
      rw [ite_eq_right small]
      exact unrestricted_range _
  · intro d hd p hp; exact unrestricted_range _
  · dsimp only [Configuration.DeclarationDisjoint, Trace.raw, state]; simp only [Set.mem_ofPred_eq]; decide +revert

def trace : Trace (Fin 5) (Fin 8) where
  identities := pool
  live t := (state (t == 0)).live 0
  deref t := (state (t == 0)).deref 0

theorem valid : trace.Valid model := by
  constructor
  · constructor <;> decide
  · intro t; exact Or.inl rfl
  · intro t
    exact (by decide : ∀ b x p, present b x → pool.parent x = some p → present b p) (t == 0)
  · intro t
    rcases state_valid (t == 0) with ⟨a, b, c, d, e, f, g, h, i, j, l⟩
    exact ⟨a, b, c, d, e, f, g, h, i, j, l⟩

/-- Both source declarations resolve under Box; the naive move rewrites flag
through parent but incorrectly reattaches X to Box's own lifetime. -/
def conditionFormula : Formula (SetAtom (Fin 5)) (SetExpr (Fin 5)) 0 :=
  .next (.atom (.inhabited (.thisStep (.child 4))))
def naiveFormula : Formula (SetAtom (Fin 5)) (SetExpr (Fin 5)) 0 :=
  .next (.atom (.inhabited (.step (.child 4) (.thisStep .parent))))

noncomputable def rhs : Value (Fin 8) Int 0 :=
  conditional trace (.ofTotal (.sets model trace)) conditionFormula
    (fun _ _ => some 1) (fun _ _ => some 2)

-- [utest->req~behavioral-formula-denotation~1]
-- [utest->req~behavioral-environments~1]
theorem temporal_condition_counterexample :
    rhs (.closed 1) 0 = some 2 ∧ moved rhs (move (.closed 1) 3) 0 = some 2 ∧
    conditional trace (.ofTotal (.sets model trace)) naiveFormula
      (fun _ _ => some (1 : Int)) (fun _ _ => some 2) (.closed 3) 0 = some 1 := by
  classical
  have original : ¬ conditionFormula.raw trace (.sets model trace) (.closed 1) 0 := by
    simp [conditionFormula, Formula.raw, Lifetime.next, Trace.ParentPresent, trace, pool,
      state, Set.mem_ofPred_eq, present, Observation.sets, SetAtom.eval, SetExpr.eval, Step.image,
      Step.relation, Trace.raw, Trace.ParentAt, Environment.closed]
  have naive : naiveFormula.raw trace (.sets model trace) (.closed 3) 0 := by
    simp [naiveFormula, Formula.raw, Lifetime.next, Trace.ParentPresent, trace, pool,
      state, Set.mem_ofPred_eq, present, Environment.closed]
  have a : rhs (.closed 1) 0 = some 2 := by
    simp only [rhs, conditional, condition, Formula.total_defined, ↓reduceIte]
    change choose (some (decide (conditionFormula.raw trace (.sets model trace) (.closed 1) 0)))
      (some 1) (some 2) = some 2
    simp [original, choose]
  refine ⟨a, (observation_preserved rhs (.closed 1) 3 0).trans a, ?_⟩
  simp only [conditional, condition, Formula.total_defined, ↓reduceIte]
  change choose (some (decide (naiveFormula.raw trace (.sets model trace) (.closed 3) 0)))
    (some 1) (some 2) = some 1
  simp [naive, choose]

-- [utest->req~behavioral-initializer-contract~1]
def richModel : Structural.Core 5 := .ofEffective model

theorem rich_valid : Structural.Valid richModel trace :=
  (Structural.valid_iff_common wellFormed supported (fun _ => rfl) trace).mpr valid

theorem xOwner : InheritedReference.Owner richModel.family 2 2 := .declared (by decide)

noncomputable def source (_ : Unit) : Value (Fin 8) (Set (Fin 8)) 0 :=
  fun ρ t => (rhs ρ t).map (fun i => {if i = 1 then 5 else 6})

def xInitializer : Obligation (Fin 5) Unit := ⟨2, .parent, .instanceBirth, ()⟩

theorem source_classification :
    Structure.elaborate richModel 2 .initial (some optional) true () = .ok xInitializer := rfl

private theorem ancestry (a b : Fin 5) : model.Ancestor a b ↔ a = b := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ edge _ => cases edge
  · rintro rfl; exact .refl

private theorem x_head (t : Nat) (x : Fin 8) :
    x ∈ (trace.raw richModel.toEffectiveCore t).head 2 ↔ t = 0 ∧ x = 3 := by
  change (x ∈ trace.live t ∧ model.Ancestor (pool.directType x) 2) ↔ _
  rw [ancestry]
  fin_cases x <;> simp [trace, state, present, pool]

private theorem x_target : Structure.target richModel trace rich_valid xOwner 0 3 = 6 := by
  have member := (x_head 0 3).mpr ⟨rfl, rfl⟩
  have link := Structure.target_link richModel trace rich_valid xOwner 0 3 member
  rw [InheritedReference.deref_owner xOwner] at link
  exact link.2.2.2.2

/-- The source observation is actually used by production initialization; the
valid optional x has target 2 at its birth. The generated expansion is satisfied. -/
theorem source_elaboration :
    Meaning trace (Structure.view richModel trace rich_valid xOwner) source xInitializer ∧
    (expansion xInitializer).PartialAttached trace
      (observation trace (Structure.view richModel trace rich_valid xOwner) source)
      (attachments trace (Structure.view richModel trace rich_valid xOwner) xInitializer) := by
  have meaning : Meaning trace (Structure.view richModel trace rich_valid xOwner) source xInitializer := by
    intro t x hx _
    obtain ⟨rfl, rfl⟩ := (x_head t x).mp hx
    change (Transport.original trace.identities .parent 3).bind
      (fun p => source () (.closed p) 0) = some {Structure.target richModel trace rich_valid xOwner 0 3}
    rw [x_target]
    change source () (.closed 1) 0 = some {6}
    simp [source, temporal_condition_counterexample.1]
  exact ⟨meaning, (expansion_agrees trace _ source xInitializer valid.root_live).mpr meaning⟩

end Clafer.Behavioral.Initializers.SourceExamples
