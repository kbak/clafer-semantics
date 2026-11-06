module

public import Clafer.Behavioral.StructuralCompatibility
public import DPGraph.Predicates.Finite
public import Mathlib.Tactic.FinCases

/-!
# Admitted richer structural witnesses

S6: System has a nested abstract Port; SubSystem inherits System; p realizes
Port, and two ordinary speed fields inherit a reference annotation. `nested`
selects Port under concrete SubSystem or under abstract System (parent refinement).
`redeclared` also refines the reference at speed. Both bag heads share a target
that changes with time. These prove full admission, not isolated observations.
-/

@[expose] public section
namespace Clafer.Behavioral.StructuralExamples
open Structural Semantics MCS DPGraph.Predicates

set_option synthInstance.maxSize 4096

def model (nested redeclared : Bool) : Structural.Core 8 where
  family := {
    root := 0
    parent := fun d => if d = 0 ∨ d = 1 ∨ d = 7 then none else
      if d = 3 then some (if nested then 2 else 1) else
      if d = 4 then some 2 else if d = 5 then some 3 else some 0
    reference := fun d => if d = 7 ∨ (d = 5 ∧ redeclared) then .bag 6 else .basic
    super := fun d => if d = 2 then some 1 else if d = 4 then some 3 else
      if d = 5 then some 7 else none
    origin := fun d => if d = 0 then .syntheticRoot else .user
    isAbstract := fun d => d == 1 || d == 3 || d == 5 || d == 7
    name := fun _ => ""
    multiplicity := fun _ => unrestricted
    group := fun d => if d = 1 ∨ d = 2 then ⟨none, .bounds one⟩ else
      if d = 3 ∨ d = 4 then ⟨none, .bounds ⟨2, .finite 2⟩⟩ else {} }
  id d := ⟨d.val⟩
  group d := if d = 1 ∨ d = 2 then one else
    if d = 3 ∨ d = 4 then ⟨2, .finite 2⟩ else unrestricted
  authoredAbstract d := d == 1 || d == 3 || d == 7

private def parentRank (nested : Bool) (d : Fin 8) : Nat :=
  if d = 0 ∨ d = 1 ∨ d = 7 then 0 else if d = 2 ∨ d = 6 then 1 else
    if d = 3 then (if nested then 2 else 1) else if d = 4 then 2 else 3

-- [utest->req~behavioral-structural-compatibility~1]
theorem model_wellFormed (nested redeclared : Bool) : (model nested redeclared).WellFormed := by
  constructor
  · decide +revert
  · simp [model]
  · intro d p h; cases nested <;> cases redeclared <;> fin_cases d <;> simp [model] at h
  · intro d e p h; cases nested <;> cases redeclared <;> fin_cases d <;> simp [model] at h
  · decide +revert
  · decide +revert
  · exact (by decide : ∀ b r d s p, (model b r).family.super d = some s →
      (model b r).family.parent s = some p → ∃ q, (model b r).family.parent d = some q ∧
        (model b r).toEffectiveCore.Ancestor q p) nested redeclared
  · intro d s o a b _ _ ha hb
    exact (by clear * - nested; unfold Kind.CanExtend; decide +revert : ∀ r d o a b,
      ((model nested r).family.reference d).target = some a →
      ((model nested r).family.reference o).target = some b →
      (model nested r).toEffectiveCore.Ancestor a b ∧
        ((model nested r).family.reference d).kind.CanExtend
          ((model nested r).family.reference o).kind) redeclared d o a b ha hb
  · exact ⟨parentRank nested, (by decide : ∀ b r d p,
      (model b r).family.parent d = some p → parentRank b p < parentRank b d) nested redeclared⟩
  · exact ⟨fun d => if d = 2 ∨ d = 4 ∨ d = 5 then 1 else 0, by decide +revert⟩
  · intro a b he; exact Fin.ext (congrArg DeclId.value he)
  · intro d; trivial
  · intro d; fin_cases d <;> simp [model, ValidRange, one, unrestricted]
  · decide +revert

def pool : Identities (Fin 8) (Fin 7) where
  root := 0
  directType x := if x = 0 then 0 else if x = 1 then 2 else if x = 2 then 4 else
    if x = 3 ∨ x = 4 then 5 else 6
  parent x := if x = 0 then none else if x = 2 then some 1 else
    if x = 3 ∨ x = 4 then some 2 else some 0

def trace (redeclared : Bool) : Trace (Fin 8) (Fin 7) where
  identities := pool
  live _ := Set.univ
  deref t d x y := (d = 7 ∨ (d = 5 ∧ redeclared)) ∧ (x = 3 ∨ x = 4) ∧
    y = if t % 2 = 0 then 5 else 6

private instance (m : EffectiveCore 8) (r : Bool) (t : Nat) (d : Fin 8) (x : Fin 7) :
    Decidable (x ∈ ((trace r).raw m t).head d) := by
  dsimp only [Trace.raw, trace]
  infer_instance

private instance (m : EffectiveCore 8) (r : Bool) (t : Nat) (d : Fin 8) (p x : Fin 7) :
    Decidable (((trace r).raw m t).contains d p x) := by
  dsimp only [Trace.raw, Trace.ParentAt, trace]
  infer_instance

private instance (m : EffectiveCore 8) (r : Bool) (t : Nat) (d : Fin 8) (x y : Fin 7) :
    Decidable (((trace r).raw m t).deref d x y) := by
  dsimp only [Trace.raw, trace]
  infer_instance

private theorem unrestricted_range (A : Type) : InRange unrestricted A :=
  ⟨⟨{ toFun := Fin.elim0, inj' := fun i => Fin.elim0 i }⟩, trivial⟩

private theorem keys (nested redeclared : Bool) (t : Nat) :
    Structural.Keys (model nested redeclared) (trace redeclared) t := by
  intro d o _ ho
  have noSet : ∀ r o, ((model nested r).family.reference o).kind ≠ .referenceSet := by
    clear * - nested
    decide +revert
  exact (noSet redeclared o ho).elim

private theorem group_children (nested redeclared : Bool) (t : Nat) (d : Fin 8) (p x : Fin 7) :
    Semantics.Groups.ChildObjects (model nested redeclared).family
      ((trace redeclared).raw (model nested redeclared).toEffectiveCore t) d p x ↔
      ∃ a, (model nested redeclared).toEffectiveCore.Ancestor d a ∧
        ∃ c, (model nested redeclared).family.parent c = some a ∧
          ((trace redeclared).raw (model nested redeclared).toEffectiveCore t).contains c p x := Iff.rfl

set_option synthInstance.maxSize 4096 in
private theorem state_valid (nested redeclared : Bool) (t : Nat) :
    Structural.StateValid (model nested redeclared) (trace redeclared) t := by
  constructor
  · dsimp only [Configuration.Typed, Trace.raw, Trace.ParentAt, trace]
    simp only [Set.mem_univ, true_and]
    split_ifs <;> clear * - nested redeclared <;> decide +revert
  · dsimp only [Trace.raw, trace]
    simp only [Set.mem_univ, true_and]
    clear * - nested redeclared
    decide +revert
  · dsimp only [Trace.raw, trace]
    simp only [Set.mem_univ, true_and]
    clear * - nested redeclared
    decide +revert
  · dsimp only [Configuration.Inherits, Trace.raw, trace]
    simp only [Set.mem_univ, true_and]
    clear * - nested redeclared
    decide +revert
  · dsimp only [Structural.Abstracts, Trace.raw, trace]
    simp only [Set.mem_univ, true_and]
    clear * - nested redeclared
    decide +revert
  · dsimp only [Configuration.Parents, ExistsUnique, Trace.raw, Trace.ParentAt, trace]
    simp only [Set.mem_univ, true_and]
    clear * - nested redeclared
    decide +revert
  · dsimp only [Configuration.References, ExistsUnique, Trace.raw, trace]
    simp only [Set.mem_univ, true_and]
    split_ifs <;> clear * - nested redeclared <;> decide +revert
  · intro d e x y z hy hz
    exact hy.2.2.trans hz.2.2.symm
  · exact keys nested redeclared t
  · intro d c hc p hp; exact unrestricted_range _
  · intro d hd p
    by_cases h1 : d = 1 ∨ d = 2
    · have hd2 : d = 2 := by
        rcases h1 with rfl | he
        · simp [model] at hd
        · exact he
      subst d
      have hp : p.val = 1 := by
        have h := p.property
        have h := h.2
        exact (by clear * - nested redeclared; decide +revert : ∀ x, (model nested redeclared).toEffectiveCore.Ancestor
          (pool.directType x) 2 → x = 1) _ h
      have eq : Semantics.Groups.ChildObjects (model nested redeclared).family
          ((trace redeclared).raw (model nested redeclared).toEffectiveCore t) 2 p.val = (fun x => x = 2) := by
        funext x; apply propext
        rw [group_children, hp]
        dsimp only [Trace.raw, Trace.ParentAt, trace]
        simp only [Set.mem_univ, true_and]
        exact (by decide : ∀ b r x,
          (∃ a, (model b r).toEffectiveCore.Ancestor 2 a ∧ ∃ c,
            (model b r).family.parent c = some a ∧
            pool.parent x = some 1 ∧ (model b r).toEffectiveCore.Ancestor (pool.directType x) c ∧
              (model b r).family.parent c ≠ none) ↔ x ∈ ({2} : Set (Fin 7))) nested redeclared x
      rw [eq]
      exact (inRange_card _ _).mpr (by change CountInRange one (Fintype.card {x : Fin 7 // x = 2}); decide)
    · by_cases h2 : d = 3 ∨ d = 4
      · have hd4 : d = 4 := by
          rcases h2 with rfl | he
          · simp [model] at hd
          · exact he
        subst d
        have hp : p.val = 2 := by
          have h := p.property
          have h := h.2
          exact (by clear * - nested redeclared; decide +revert : ∀ x, (model nested redeclared).toEffectiveCore.Ancestor
            (pool.directType x) 4 → x = 2) _ h
        have eq : Semantics.Groups.ChildObjects (model nested redeclared).family
            ((trace redeclared).raw (model nested redeclared).toEffectiveCore t) 4 p.val = (fun x => x = 3 ∨ x = 4) := by
          funext x; apply propext
          rw [group_children, hp]
          dsimp only [Trace.raw, Trace.ParentAt, trace]
          simp only [Set.mem_univ, true_and]
          exact (by decide : ∀ b r x,
            (∃ a, (model b r).toEffectiveCore.Ancestor 4 a ∧ ∃ c,
              (model b r).family.parent c = some a ∧
              pool.parent x = some 2 ∧ (model b r).toEffectiveCore.Ancestor (pool.directType x) c ∧
                (model b r).family.parent c ≠ none) ↔ x ∈ ({3, 4} : Set (Fin 7))) nested redeclared x
        rw [eq]
        exact (inRange_card _ _).mpr (by change CountInRange ⟨2, .finite 2⟩ (Fintype.card {x : Fin 7 // x = 3 ∨ x = 4}); decide)
      · simpa only [model, ite_eq_right h1, ite_eq_right h2, GroupCard.range] using unrestricted_range
          {x // Semantics.Groups.ChildObjects (model nested redeclared).family
            ((trace redeclared).raw (model nested redeclared).toEffectiveCore t) d p.val x}
  · dsimp only [Configuration.DeclarationDisjoint, Trace.raw, trace]
    simp only [Set.mem_univ, true_and]
    clear * - nested redeclared
    decide +revert
  · intro x _
    have edge : ∀ p x, pool.parent x = some p → ∃ d,
        ((trace redeclared).raw (model nested redeclared).toEffectiveCore t).contains d p x := by
      dsimp only [Trace.raw, Trace.ParentAt, trace]
      simp only [Set.mem_univ, true_and]
      exact (by decide : ∀ b r p x, pool.parent x = some p → ∃ d,
        pool.parent x = some p ∧ (model b r).toEffectiveCore.Ancestor (pool.directType x) d ∧
          (model b r).family.parent d ≠ none) nested redeclared
    have r0 : ((trace redeclared).raw (model nested redeclared).toEffectiveCore t).Reaches 0 := .refl
    have r1 := r0.tail (edge 0 1 rfl)
    have r2 := r1.tail (edge 1 2 rfl)
    fin_cases x
    · exact r0
    · exact r1
    · exact r2
    · exact r2.tail (edge 2 3 rfl)
    · exact r2.tail (edge 2 4 rfl)
    · exact r0.tail (edge 0 5 rfl)
    · exact r0.tail (edge 0 6 rfl)

-- [utest->req~behavioral-structural-compatibility~1]
-- [utest->req~behavioral-reference-atoms~1]
theorem admitted (nested redeclared : Bool) :
    Structural.Admissible (model nested redeclared) (trace redeclared) := by
  refine ⟨model_wellFormed nested redeclared, ?_⟩
  constructor
  · constructor
    · rfl
    · decide +revert
    · decide +revert
    · rfl
    · decide +revert
    · decide +revert
  · intro t; trivial
  · intro t x p hx hp; trivial
  · exact state_valid nested redeclared

-- [utest->req~behavioral-structural-compatibility~1]
theorem nested_abstract_outside_old_domain : ¬ (model true false).family.WellFormed := by
  intro h
  have bad := h.nested_abstract 3 2 (by decide) (by decide)
  contradiction

theorem refined_parent_outside_old_domain : ¬ (model false false).family.WellFormed := by
  intro h
  have bad := h.inheritance_parent 4 3 (by decide) (by decide)
  contradiction

theorem ordinary_inherited_field_has_instances :
    (model false false).family.isAbstract 5 = true ∧
    (model false false).authoredAbstract 5 = false ∧
    3 ∈ ((trace false).raw (model false false).toEffectiveCore 0).head 5 := by
  refine ⟨rfl, rfl, trivial, ?_⟩
  exact .refl

theorem inherited_owner : InheritedReference.Owner (model false false).family 5 7 :=
  .inherited (by simp [model]) (by simp [model]) (.declared (by simp [model]))

-- [utest->req~behavioral-reference-atoms~1]
theorem inherited_bag_changes_target :
    InheritedReference.deref (model false false).family
      ((trace false).raw (model false false).toEffectiveCore 0) 5 3 5 ∧
    InheritedReference.deref (model false false).family
      ((trace false).raw (model false false).toEffectiveCore 0) 5 4 5 ∧
    InheritedReference.deref (model false false).family
      ((trace false).raw (model false false).toEffectiveCore 1) 5 3 6 ∧
    (3 : Fin 7) ≠ 4 := by
  simp only [InheritedReference.deref_owner inherited_owner]
  decide

def setModel : Structural.Core 8 :=
  { model false false with family := { (model false false).family with
      reference := fun d => if d = 7 then .set 6 else .basic } }

theorem set_duplicates_rejected : ¬ Structural.Valid setModel (trace false) := by
  intro h
  have owner : InheritedReference.Owner setModel.family 5 7 :=
    .inherited (by simp [setModel]) (by simp [setModel, model]) (.declared (by simp [setModel]))
  have bad := (h.states 0).keys 5 7 owner (by decide) 2 5 3 4
    (by decide) ((InheritedReference.deref_owner owner 3 5).mpr (by decide))
    (by decide) ((InheritedReference.deref_owner owner 4 5).mpr (by decide))
  contradiction

/-- Invalid raw data is not repaired by hiding the endpoint during navigation. -/
def missing (x : Fin 7) : Trace (Fin 8) (Fin 7) :=
  { trace false with live := fun _ => {y | y ≠ x} }

theorem dead_target_rejected : ¬ Structural.Valid (model false false) (missing 5) := by
  intro h
  have typed := (h.states 0).typed.2 7 3 5 (by change (trace false).deref 0 7 3 5; unfold trace; decide)
  obtain ⟨_, c, _, hc⟩ := typed
  exact hc.1 rfl

theorem dead_head_rejected : ¬ Structural.Valid (model false false) (missing 3) := by
  intro h
  exact ((h.states 0).typed.2 7 3 5 (by change (trace false).deref 0 7 3 5; unfold trace; decide)).1.1 rfl

def conflicting : Trace (Fin 8) (Fin 7) :=
  { trace true with deref := fun _ d x y =>
      (d = 5 ∧ x = 3 ∧ y = 6) ∨ (d = 7 ∧ x = 3 ∧ y = 5) }

theorem conflicting_refinement_rejected : ¬ Structural.Valid (model false true) conflicting := by
  intro h
  have bad := (h.states 0).coherent 5 7 3 6 5 (Or.inl ⟨rfl, rfl, rfl⟩) (Or.inr ⟨rfl, rfl, rfl⟩)
  contradiction

/-- A group inherited by p counts two distinct speed heads even at one target. -/
theorem inherited_group_counts_occurrences :
    InRange ⟨2, .finite 2⟩ {x : Fin 7 // Semantics.Groups.ChildObjects
      (model false false).family ((trace false).raw (model false false).toEffectiveCore 0) 4 2 x} :=
  ((admitted false false).2.states 0).groups 4 (by decide) ⟨2, trivial, .refl⟩

def tooSmallGroup : Structural.Core 8 :=
  { model false false with
    family := { (model false false).family with group := fun d =>
      if d = 4 then ⟨none, .bounds one⟩ else (model false false).family.group d }
    group := fun d => if d = 4 then one else (model false false).group d }

-- [utest->req~behavioral-structural-compatibility~1]
theorem inherited_group_overflow_rejected : ¬ Structural.Valid tooSmallGroup (trace false) := by
  intro h
  have small := (h.states 0).groups 4 (by decide) ⟨2, trivial, .refl⟩
  have big := inherited_group_counts_occurrences
  obtain ⟨down⟩ := small.2
  obtain ⟨up⟩ := big.1
  have impossible := Fintype.card_le_of_embedding (up.trans down)
  contradiction

theorem direct_authored_abstract_rejected :
    ¬ Structural.IdentitiesValid (model false false)
      { trace false with identities := { pool with directType := fun _ => 3 } } := by
  intro h
  have bad := h.concrete 1
  contradiction

end Clafer.Behavioral.StructuralExamples
