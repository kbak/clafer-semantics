module

public import Clafer.Behavioral.InitializerFinality
public import Clafer.Behavioral.InitializerCompatibility
public import Clafer.Behavioral.InitializerLifecycleExamples

/-! # Production initializer boundaries

Behavioral §5 Definitions 3–5 / §6.1, #170/#171. The fixed trace reuses a
structurally admitted inherited-reference state. Distinct finite target identities
stand for distinct values; these clock/constraint witnesses do not assert a
frontend parsing or backend translation theorem.
-/

@[expose] public section
namespace Clafer.Behavioral.Initializers.ProductionExamples
open LifecycleExamples

def fixed : Trace (Fin 5) (Fin 9) where
  identities := (fixture .replace).unfold.identities
  live _ := (fixture .replace).unfold.live 0
  deref _ := (fixture .replace).unfold.deref 0

theorem fixed_valid : Structural.Valid (model false false) fixed := by
  have h := (admitted false false .replace (Or.inl rfl)).2
  constructor
  · rcases h.identities with ⟨a, b, c, d, e, f⟩
    exact ⟨a, b, c, d, e, f⟩
  · exact fun _ => h.root_live 0
  · exact fun _ => h.parent_live 0
  · intro t
    rcases h.states 0 with ⟨a, b, c, d, e, f, g, h, i, j, l, q, r⟩
    exact ⟨a, b, c, d, e, f, g, h, i, j, l, q, r⟩


/-- The parentless abstract view has one live instance (3) targeting 6. -/
def fixedView : View (Fin 9) where
  contexts _ := {0}
  heads _ _ := {3}
  instances _ := {3}
  target _ _ := 6

theorem fixed_observations (t : Nat) :
    (fixed.raw (model false false).toEffectiveCore t).head 4 = {3} ∧
    {y | (Structural.current (model false false) fixed t).deref 4 3 y} = {6} := by
  constructor
  · ext x
    change (live .replace ((fixture .replace).clock 0).1 x = true ∧
      (model false false).toEffectiveCore.Ancestor (pool.directType x) 4) ↔ x = 3
    fin_cases x <;> decide
  · ext y
    change (Structural.current (model false false) fixed t).deref 4 3 y ↔ y = 6
    rw [show (Structural.current (model false false) fixed t).deref 4 3 y ↔
      3 ∈ (fixed.raw (model false false).toEffectiveCore t).head 4 ∧ fixed.deref t 4 3 y from
        InheritedReference.own_reference (by decide) 3 y]
    change (3 ∈ ((fixture .replace).unfold.raw (model false false).toEffectiveCore 0).head 4 ∧
      (fixture .replace).unfold.deref 0 4 3 y) ↔ y = 6
    have member : 3 ∈ ((fixture .replace).unfold.raw (model false false).toEffectiveCore 0).head 4 :=
      ⟨by change live .replace ((fixture .replace).clock 0).1 3 = true; decide,
        Relation.ReflTransGen.single (by decide)⟩
    rw [and_iff_right member]
    change ((y == (6 : Fin 9)) = true) ↔ y = 6
    simp

private theorem fixed_birth (t : Nat) (x : Fin 9) : fixed.Starts t x ↔
    x ∈ fixed.live 0 ∧ t = 0 := Candidate.starts_constant_live fixed (fun _ => rfl) t x

inductive Value where
  | six | seven | changing | undefinedLater
  deriving DecidableEq

def source : Value → Transport.Value (Fin 9) (Set (Fin 9)) 0
  | .six => fun _ _ => some {6}
  | .seven => fun _ _ => some {7}
  | .changing => fun _ t => some {if t = 0 then 6 else 7}
  | .undefinedLater => fun _ t => if t = 0 then some {6} else none

def initial (v : Value) : Obligation (Fin 5) Value := ⟨4, .root, .instanceBirth, v⟩
def constant (v : Value) : Obligation (Fin 5) Value := ⟨4, .root, .everyLive, v⟩

-- [utest->req~behavioral-initializer-contract~1]
theorem admitted_abstract (v : Value) :
    elaborate (4 : Fin 5) .initial ⟨true, false, none, .bounds unrestricted⟩ true v = .ok (initial v) := rfl

theorem six_initializes : Meaning fixed fixedView source (initial .six) := by
  intro t x hx birth
  have eq : x = 3 := hx
  subst x
  rfl

theorem changing_initializes : Meaning fixed fixedView source (initial .changing) := by
  intro t x hx birth
  have zero := (fixed_birth t x).mp birth |>.2
  subst t
  rfl

theorem undefined_later_initializes : Meaning fixed fixedView source (initial .undefinedLater) := by
  intro t x hx birth
  have zero := (fixed_birth t x).mp birth |>.2
  subst t
  rfl

-- [utest->req~behavioral-modifiers~1]
theorem changing_rejects_equality : ¬ Meaning fixed fixedView source (constant .changing) := by
  intro eq
  have bad := eq 1 0 rfl (fixed_valid.root_live 1) (Set.singleton_nonempty 3)
  simp [constant, source, fixedView, View.targets] at bad

theorem undefined_later_rejects_equality :
    ¬ Meaning fixed fixedView source (constant .undefinedLater) := by
  intro eq
  have bad := eq 1 0 rfl (fixed_valid.root_live 1) (Set.singleton_nonempty 3)
  simp [constant, source] at bad

theorem fixed_reference : Modifiers.FinalRef (model false false) fixed 4 := by
  intro x _ i j _ _
  rfl

theorem fixed_heads : Modifiers.FinalHeads (model false false) fixed 4 := by
  intro p i j _ _
  rfl

/-- Both distinctions survive adding final: fixed heads do not evaluate a
later RHS, and fixed references do not force that RHS to remain defined. -/
theorem final_does_not_remove_rhs_distinction :
    Modifiers.Final (model false false) fixed 4 ∧
    Meaning fixed fixedView source (initial .changing) ∧
    ¬ Meaning fixed fixedView source (constant .changing) ∧
    Meaning fixed fixedView source (initial .undefinedLater) ∧
    ¬ Meaning fixed fixedView source (constant .undefinedLater) :=
  ⟨⟨fixed_heads, fixed_reference⟩, changing_initializes, changing_rejects_equality,
    undefined_later_initializes, undefined_later_rejects_equality⟩

-- [utest->req~behavioral-initializer-contract~1]
theorem conflicting_inherited_initializers :
    ¬ Bundle fixed (fun _ => fixedView) source [initial .six, initial .seven] := by
  intro all
  have h := all (initial .seven) (by simp)
  have bad := h 0 3 rfl ((fixed.starts_zero 3).mpr (by change live .replace ((fixture .replace).clock 0).1 3 = true; decide))
  simp [initial, source, fixedView, Transport.original] at bad

theorem inherited_birth_and_own_equality_conflict :
    ¬ Bundle fixed (fun _ => fixedView) source [initial .six, constant .seven] := by
  intro all
  have h := all (constant .seven) (by simp)
  have bad := h 0 0 rfl (fixed_valid.root_live 0) (Set.singleton_nonempty 3)
  simp [constant, source, fixedView, View.targets] at bad

theorem production_expansion :
    (expansion (initial .undefinedLater)).PartialAttached fixed (observation fixed fixedView source)
      (attachments fixed fixedView (initial .undefinedLater)) :=
  (expansion_agrees fixed fixedView source _ fixed_valid.root_live).mpr undefined_later_initializes


/-- The inherited abstract's root context and the own declaration's parent
context remain distinct, despite their shared live head and reference target. -/
noncomputable def contextSource (_ : Unit) : Transport.Value (Fin 9) (Set (Fin 9)) 0 :=
  fun ρ _ => some {if ρ.this = 0 then 6 else 7}

theorem abstractOwner : InheritedReference.Owner (model false false).family 4 4 :=
  .declared (by decide)

theorem concreteOwner : InheritedReference.Owner (model false false).family 2 4 :=
  .inherited (by decide) (by decide) abstractOwner

def inheritedContext : Obligation (Fin 5) Unit := ⟨4, .root, .instanceBirth, ()⟩
def ownContext (clock : Clock) : Obligation (Fin 5) Unit := ⟨2, .parent, clock, ()⟩

private theorem concrete_head (t : Nat) :
    (fixed.raw (model false false).toEffectiveCore t).head 2 = {3} := by
  ext x
  change (live .replace ((fixture .replace).clock 0).1 x = true ∧
    (model false false).toEffectiveCore.Ancestor (pool.directType x) 2) ↔ x = 3
  fin_cases x <;> decide

private theorem concrete_target (t : Nat) :
    Structure.target (model false false) fixed fixed_valid concreteOwner t 3 = 6 := by
  have member : 3 ∈ (fixed.raw (model false false).toEffectiveCore t).head 2 := by
    rw [concrete_head]; exact rfl
  have link := Structure.target_link _ _ fixed_valid concreteOwner t 3 member
  rw [InheritedReference.deref_owner concreteOwner] at link
  have eq := link.2
  change (true && true && true &&
    (Structure.target (model false false) fixed fixed_valid concreteOwner t 3 == (6 : Fin 9))) = true at eq
  simpa only [Bool.true_and, beq_iff_eq] using eq


-- [utest->req~behavioral-environments~1]
-- [utest->req~behavioral-initializer-contract~1]
theorem inherited_context_initializes :
    Meaning fixed (Structure.view (model false false) fixed fixed_valid abstractOwner)
      contextSource inheritedContext := by
  intro t x hx _
  have eq : x = 3 := by simpa only [Structure.view, (fixed_observations t).1, Set.mem_singleton_iff] using hx
  subst x
  have target := Structure.shared_target (model false false) fixed fixed_valid
    abstractOwner concreteOwner t 3 (by rw [(fixed_observations t).1]; exact rfl)
    (by rw [concrete_head]; exact rfl)
  rw [concrete_target] at target
  change some ({6} : Set (Fin 9)) = some {Structure.target _ _ fixed_valid abstractOwner t 3}
  rw [target]

theorem own_context_conflicts (clock : Clock)
    (kind : clock = .instanceBirth ∨ clock = .everyLive) :
    ¬ Meaning fixed (Structure.view (model false false) fixed fixed_valid concreteOwner)
      contextSource (ownContext clock) := by
  have member : 3 ∈ (fixed.raw (model false false).toEffectiveCore 0).head 2 := by
    rw [concrete_head]; exact rfl
  rcases kind with rfl | rfl
  · intro h
    have bad := h 0 3 member ((fixed.starts_zero 3).mpr member.1)
    change some ({7} : Set (Fin 9)) = some {Structure.target _ _ fixed_valid concreteOwner 0 3} at bad
    rw [concrete_target] at bad
    have impossible : (7 : Fin 9) = 6 := Set.singleton_injective (Option.some.inj bad)
    cases impossible
  · intro h
    have perHead := (Structure.every_fibers (model false false) fixed fixed_valid concreteOwner
      contextSource () (fun _ _ _ => Or.inr (by intro S eq; cases eq; exact Set.subsingleton_singleton))).mp h
    have bad := perHead 0 3 member
    change some ({7} : Set (Fin 9)) = some {Structure.target _ _ fixed_valid concreteOwner 0 3} at bad
    rw [concrete_target] at bad
    have impossible : (7 : Fin 9) = 6 := Set.singleton_injective (Option.some.inj bad)
    cases impossible

/-- The resolved super edge carries the original record, including root
attachment; an own equation neither overwrites it nor changes its clock. -/
theorem inherited_record_preserved :
    Structure.Effective (model false false)
      (fun d => if d = 4 then {inheritedContext} else ∅) 2 inheritedContext :=
  Structure.effective_inherited _ _ (by decide : (model false false).family.super 2 = some 4)
    (Structure.effective_own _ _ _ _ (by simp))

end Clafer.Behavioral.Initializers.ProductionExamples
