module

public import Clafer.Behavioral.InitializerTransportExamples

/-! # Resolved simultaneous reference initialization

Two optional reference declarations x/y are born together, both at target 6,
then both change to target 5 while their identities remain live. Initializers
observe the same source state; neither one executes an assignment.
-/

@[expose] public section
namespace Clafer.Behavioral.Initializers.SimultaneousExamples
open Semantics DPGraph.Predicates Transport

/-- Root 0, Box 1, x 2, value 3, y 4. -/
def model : EffectiveCore 5 where
  family := {
    root := 0
    parent d := if d = 0 then none else if d = 2 ∨ d = 4 then some 1 else some 0
    reference d := if d = 2 ∨ d = 4 then .set 3 else .basic
    super _ := none
    origin d := if d = 0 then .syntheticRoot else .user
    isAbstract _ := false
    name d := if d = 1 then "Box" else if d = 2 then "x" else if d = 4 then "y" else ""
    multiplicity d := if d = 1 ∨ d = 2 ∨ d = 4 then optional else unrestricted }
  id d := ⟨d.val⟩
  group _ := unrestricted

def pool : Identities (Fin 5) (Fin 8) where
  root := 0
  directType x := if x = 0 then 0 else if x = 3 then 2 else if x = 4 then 4
    else if x = 5 ∨ x = 6 then 3 else 1
  parent x := if x = 0 then none else if x = 3 ∨ x = 4 then some 1 else some 0

def present (_first : Bool) (x : Fin 8) : Prop :=
  x = 0 ∨ x = 5 ∨ x = 6 ∨ x = 1 ∨ x = 3 ∨ x = 4

instance (b : Bool) : DecidablePred (present b) := fun _ => by unfold present; infer_instance

def state (first : Bool) : Trace (Fin 5) (Fin 8) where
  identities := pool
  live _ := {x | present first x}
  deref _ d x y := ((d = 2 ∧ x = 3) ∨ (d = 4 ∧ x = 4)) ∧ y = if first then 6 else 5

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


def richModel : Structural.Core 5 := .ofEffective model

theorem rich_valid : Structural.Valid richModel trace :=
  (Structural.valid_iff_common wellFormed supported (fun _ => rfl) trace).mpr valid

theorem owner (d : Fin 5) (hd : d = 2 ∨ d = 4) : InheritedReference.Owner richModel.family d d :=
  .declared (by rcases hd with rfl | rfl <;> decide)

/-- true is the resolved y path; false is the resolved x path. -/
noncomputable def source (other : Bool) : Value (Fin 8) (Set (Fin 8)) 0 :=
  fun ρ t => some (SetExpr.eval model trace ρ t
    (.step (.deref (if other then 4 else 2)) (.thisStep (.child (if other then 4 else 2)))))

def initial (d : Fin 5) (other : Bool) : Obligation (Fin 5) Bool :=
  ⟨d, .parent, .instanceBirth, other⟩

private theorem ancestry (a b : Fin 5) : model.Ancestor a b ↔ a = b := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ edge _ => cases edge
  · rintro rfl; exact .refl

private theorem heads_at (t : Nat) (d : Fin 5) (hd : d = 2 ∨ d = 4) (x : Fin 8) :
    x ∈ (trace.raw richModel.toEffectiveCore t).head d ↔ x = if d = 2 then 3 else 4 := by
  change (x ∈ trace.live t ∧ model.Ancestor (pool.directType x) d) ↔ _
  rw [ancestry]
  rcases hd with rfl | rfl <;> fin_cases x <;> simp [trace, state, present, pool]

private theorem source_value (b : Bool) (t : Nat) :
    source b (.closed 1) t = some {if t = 0 then 6 else 5} := by
  unfold source
  congr 1
  ext y
  simp only [SetExpr.eval, Step.image, Step.relation, Environment.closed, trace, state,
    Trace.raw, Trace.ParentAt, Set.mem_ofPred_eq]
  simp only [ancestry]
  cases b <;> by_cases ht : t = 0 <;> fin_cases y <;> simp [pool, present, model, ht]

private theorem target_value (d : Fin 5) (hd : d = 2 ∨ d = 4) (t : Nat)
    (x : Fin 8) (hx : x ∈ (trace.raw richModel.toEffectiveCore t).head d) :
    Structure.target richModel trace rich_valid (owner d hd) t x = if t = 0 then 6 else 5 := by
  have link := Structure.target_link richModel trace rich_valid (owner d hd) t x hx
  rw [InheritedReference.deref_owner (owner d hd)] at link
  simpa only [beq_iff_eq] using link.2.2

-- [utest->req~behavioral-initializer-contract~1]
theorem mutual_initialization (d : Fin 5) (hd : d = 2 ∨ d = 4) (other : Bool) :
    Meaning trace (Structure.view richModel trace rich_valid (owner d hd)) source (initial d other) := by
  intro t x hx birth
  have liveStable : ∀ t, trace.live t = trace.live 0 := fun _ => rfl
  have zero := ((Candidate.starts_constant_live trace liveStable t x).mp birth).2
  subst t
  have who := (heads_at 0 d hd x).mp hx
  have parent : trace.identities.parent x = some 1 := by
    rw [who]; rcases hd with rfl | rfl <;> decide
  change (Transport.original trace.identities .parent x).bind _ = _
  rw [show Transport.original trace.identities .parent x = some 1 from parent, Option.bind_some]
  change source other (.closed 1) 0 = some {Structure.target richModel trace rich_valid (owner d hd) 0 x}
  rw [target_value d hd 0 x hx, source_value]

theorem both_birth_equations :
    Meaning trace (Structure.view richModel trace rich_valid (owner 2 (Or.inl rfl))) source (initial 2 true) ∧
    Meaning trace (Structure.view richModel trace rich_valid (owner 4 (Or.inr rfl))) source (initial 4 false) :=
  ⟨mutual_initialization 2 (Or.inl rfl) true, mutual_initialization 4 (Or.inr rfl) false⟩

theorem classification :
    Structure.elaborate richModel 2 .initial (some optional) true true = .ok (initial 2 true) ∧
    Structure.elaborate richModel 4 .initial (some optional) true false = .ok (initial 4 false) := ⟨rfl, rfl⟩

theorem later_change : trace.deref 0 2 3 6 ∧ trace.deref 1 2 3 5 ∧
    trace.deref 0 4 4 6 ∧ trace.deref 1 4 4 5 := by
  simp [trace, state]

end Clafer.Behavioral.Initializers.SimultaneousExamples
