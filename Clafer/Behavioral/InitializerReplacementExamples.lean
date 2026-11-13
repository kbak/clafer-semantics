module

public import Clafer.Behavioral.InitializerSourceExamples

/-! # Parent replacement through production elaboration

Behavioral §5 Definitions 3–5 / §6.1 and #171. Box identity 1 with child 3
is replaced by Box identity 2 with child 4. Each child starts with the value
observed in its own fixed original parent context; target identities 6/5 are
distinct values. This is a resolved semantic witness, not a parser theorem.
-/

@[expose] public section
namespace Clafer.Behavioral.Initializers.ReplacementExamples
open Semantics DPGraph.Predicates Transport

abbrev model := SourceExamples.model

def pool : Identities (Fin 5) (Fin 8) where
  root := 0
  directType x := if x = 0 then 0 else if x = 3 ∨ x = 4 then 2
    else if x = 5 ∨ x = 6 then 3 else 1
  parent x := if x = 0 then none else if x = 3 then some 1 else if x = 4 then some 2 else some 0

def present (first : Bool) (x : Fin 8) : Prop :=
  x = 0 ∨ x = 5 ∨ x = 6 ∨ ((x = 1 ∨ x = 3) ∧ first = true) ∨ ((x = 2 ∨ x = 4) ∧ first = false)

instance (b : Bool) : DecidablePred (present b) := fun _ => by unfold present; infer_instance

def state (first : Bool) : Trace (Fin 5) (Fin 8) where
  identities := pool
  live _ := {x | present first x}
  deref _ d x y := d = 2 ∧ ((x = 3 ∧ first = true) ∨ (x = 4 ∧ first = false)) ∧ y = if first then 6 else 5

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
  (Structural.valid_iff_common SourceExamples.wellFormed SourceExamples.supported
    (fun _ => rfl) trace).mpr valid

theorem owner : InheritedReference.Owner richModel.family 2 2 := .declared (by decide)

/-- Two independently resolved parent observations; their transport must not
reuse the old parent when the new child is attached. -/
noncomputable def source (_ : Unit) : Value (Fin 8) (Set (Fin 8)) 0 :=
  fun ρ _ => some {if ρ.this = 1 then 6 else 5}

def initializer : Obligation (Fin 5) Unit := ⟨2, .parent, .instanceBirth, ()⟩

theorem source_classification :
    Structure.elaborate richModel 2 .initial (some optional) false () = .ok initializer := rfl

private theorem ancestry (a b : Fin 5) : model.Ancestor a b ↔ a = b := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ edge _ => cases edge
  · rintro rfl; exact .refl

private theorem head_at (t : Nat) (x : Fin 8) :
    x ∈ (trace.raw richModel.toEffectiveCore t).head 2 ↔
      (t = 0 ∧ x = 3) ∨ (t ≠ 0 ∧ x = 4) := by
  change (x ∈ trace.live t ∧ model.Ancestor (pool.directType x) 2) ↔ _
  rw [ancestry]
  fin_cases x <;> simp [trace, state, present, pool]

private theorem target_at (t : Nat) (x : Fin 8)
    (hx : x ∈ (trace.raw richModel.toEffectiveCore t).head 2) :
    Structure.target richModel trace rich_valid owner t x = if t = 0 then 6 else 5 := by
  have link := Structure.target_link richModel trace rich_valid owner t x hx
  rw [InheritedReference.deref_owner owner] at link
  simpa only [beq_iff_eq] using link.2.2.2

-- [utest->req~behavioral-initializer-contract~1]
-- [utest->req~behavioral-environments~1]
theorem replacement_elaboration :
    Meaning trace (Structure.view richModel trace rich_valid owner) source initializer ∧
    (expansion initializer).PartialAttached trace
      (observation trace (Structure.view richModel trace rich_valid owner) source)
      (attachments trace (Structure.view richModel trace rich_valid owner) initializer) := by
  have meaning : Meaning trace (Structure.view richModel trace rich_valid owner) source initializer := by
    intro t x hx _
    have target := target_at t x hx
    change (Transport.original trace.identities .parent x).bind
      (fun p => source () (.closed p) t) = some {Structure.target richModel trace rich_valid owner t x}
    rw [target]
    rcases (head_at t x).mp hx with ⟨rfl, rfl⟩ | ⟨ht, rfl⟩
    · rfl
    · simp [Transport.original, trace, pool, source, Environment.closed, ht]
  exact ⟨meaning, (expansion_agrees trace _ source initializer valid.root_live).mpr meaning⟩

/-- A fresh parent and fresh child coexist at the replacement; the old child
cannot migrate. Both actual reference equations use their respective contexts. -/
theorem fresh_parent_child :
    trace.ParentAt 0 1 3 ∧ trace.ParentAt 1 2 4 ∧
    trace.Starts 1 2 ∧ trace.Starts 1 4 ∧
    trace.deref 0 2 3 6 ∧ trace.deref 1 2 4 5 := by
  simp [Trace.ParentAt, Trace.starts_succ, trace, state, present, pool]

end Clafer.Behavioral.Initializers.ReplacementExamples
