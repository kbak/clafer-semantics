module

public import Clafer.Behavioral.AbstractMultiplicity
public import Clafer.Behavioral.StructuralExamples
public import Mathlib.Tactic.FinCases

/-!
# Aggregate multiplicity witnesses

Tools (1) is a parentless abstract bag reference to the root. Left (3) extends
an intermediate abstract (2), and Right (4) extends Tools directly. They have
four heads each, under distinct concrete parent declarations (5 and 6).
The right parent and its children may be absent. Every reference has target 0.
This makes both cross-parent counting and the optional-ancestor trap explicit.
-/

@[expose] public section
namespace Clafer.Behavioral.AbstractMultiplicityExamples
open Semantics DPGraph.Predicates AbstractMultiplicity

set_option synthInstance.maxSize 4096

def core (bound : Option Range) : AbstractMultiplicity.Core 7 where
  family := {
    root := 0
    parent d := if d = 0 ∨ d = 1 ∨ d = 2 then none else
      if d = 3 then some 5 else if d = 4 then some 6 else some 0
    reference d := if d = 1 then .bag 0 else .basic
    super d := if d = 2 ∨ d = 4 then some 1 else if d = 3 then some 2 else none
    origin d := if d = 0 then .syntheticRoot else .user
    isAbstract d := d == 1 || d == 2
    name _ := ""
    -- Deliberately retained optimizer zeroing. Source counts must ignore it.
    multiplicity d := if d = 1 then ⟨0, .finite 0⟩ else
      if d = 3 ∨ d = 4 then ⟨4, .finite 4⟩ else unrestricted }
  id d := ⟨d.val⟩
  group _ := unrestricted
  authoredAbstract d := d == 1 || d == 2
  authoredMultiplicity d := if d = 1 then bound else none

def pool : Identities (Fin 7) (Fin 11) where
  root := 0
  directType x := if x = 0 then 0 else if x = 1 then 5 else if x = 2 then 6 else
    if x.val < 7 then 3 else 4
  parent x := if x = 0 then none else if x = 1 ∨ x = 2 then some 0 else
    if x.val < 7 then some 1 else some 2

def present (b : Bool) (x : Fin 11) : Prop :=
  x = 0 ∨ x = 1 ∨ (3 ≤ x.val ∧ x.val < 7) ∨ b = true

instance (b : Bool) (x : Fin 11) : Decidable (present b x) := by
  unfold present
  infer_instance

def trace (expanded : Nat → Bool) : Trace (Fin 7) (Fin 11) where
  identities := pool
  live t := {x | present (expanded t) x}
  deref t d x y := d = 1 ∧ 3 ≤ x.val ∧ present (expanded t) x ∧ y = 0

def state (b : Bool) : Configuration (Fin 7) (Fin 11) :=
  (trace (fun _ => b)).raw (core none).source.toEffectiveCore 0

instance (b : Bool) (d : Fin 7) (x : Fin 11) : Decidable (x ∈ (state b).head d) := by
  dsimp only [state, Trace.raw, trace]
  infer_instance

instance (b : Bool) (d : Fin 7) (p x : Fin 11) :
    Decidable ((state b).contains d p x) := by
  dsimp only [state, Trace.raw, Trace.ParentAt, trace]
  infer_instance

private theorem ancestor_eq (r : Option Range) :
    (core r).source.toEffectiveCore.Ancestor = (core none).source.toEffectiveCore.Ancestor := rfl

macro "fixture_decide" : tactic => `(tactic| (
  try simp only [ancestor_eq]
  try dsimp only [core, Core.source, trace]
  all_goals (clear * -; decide +revert)))

-- [utest->req~abstract-multiplicity~1]
theorem wellFormed (r : Option Range) (hr : ValidRange (Semantics.AbstractMultiplicity.range r)) :
    (core r).source.WellFormed := by
  constructor
  · fixture_decide
  · simp [core, Core.source]
  · intro d p h; fin_cases d <;> simp [core, Core.source] at h
  · intro d e p h; fin_cases d <;> simp [core, Core.source] at h
  · fixture_decide
  · fixture_decide
  · fixture_decide
  · intro d s o a b edge _ ha _
    have eq : d = 1 := (by decide : ∀ d a,
      ((core none).source.family.reference d).target = some a → d = 1) d a ha
    subst d
    simp [core, Core.source] at edge
  · exact ⟨fun d => if d = 3 ∨ d = 4 then 2 else if d = 5 ∨ d = 6 then 1 else 0,
      by fixture_decide⟩
  · exact ⟨fun d => if d = 3 then 2 else if d = 2 ∨ d = 4 then 1 else 0,
      by fixture_decide⟩
  · intro d e h; exact Fin.ext (congrArg DeclId.value h)
  · intro d; fin_cases d <;> simp_all [core, Core.source, Semantics.AbstractMultiplicity.range,
      ValidRange, unrestricted]
  · intro d; trivial
  · fixture_decide

private theorem state_valid (r : Option Range) (b : Bool) :
    Structural.StateValid (core r).source (trace (fun _ => b)) 0 := by
  constructor
  · dsimp only [Configuration.Typed, Trace.raw, Trace.ParentAt, trace]
    fixture_decide
  · dsimp only [Trace.raw, trace]
    fixture_decide
  · dsimp only [Trace.raw, trace]
    fixture_decide
  · dsimp only [Configuration.Inherits, Trace.raw, trace]
    fixture_decide
  · dsimp only [Structural.Abstracts, Trace.raw, trace]
    fixture_decide
  · dsimp only [Configuration.Parents, ExistsUnique, Trace.raw, Trace.ParentAt, trace]
    fixture_decide
  · dsimp only [Configuration.References, ExistsUnique, Trace.raw, trace]
    fixture_decide
  · intro d e x y z hy hz
    exact hy.2.2.2.trans hz.2.2.2.symm
  · intro d o _ hk
    have noSet : ∀ o, ((core r).source.family.reference o).kind ≠ .referenceSet := by fixture_decide
    exact (noSet o hk).elim
  · intro d c hc p hp
    fin_cases d <;> simp only [core, Core.source] at hc ⊢
    all_goals try contradiction
    all_goals try exact Semantics.AbstractMultiplicity.unrestricted_holds _
    all_goals
      change InRange ⟨4, .finite 4⟩ {x // (state b).contains _ p x}
      apply (inRange_card _ _).mpr
      have hp' : p ∈ (state b).head c := hp
      revert hp'
      revert hc
      clear hp
      fixture_decide
  · intro d _ p
    exact Semantics.AbstractMultiplicity.unrestricted_holds _
  · dsimp only [Configuration.DeclarationDisjoint, Trace.raw, trace]
    fixture_decide
  · intro x hx
    have edge : ∀ p x, present b p → present b x → pool.parent x = some p →
        ∃ d, ((trace (fun _ => b)).raw (core r).source.toEffectiveCore 0).contains d p x := by
      dsimp only [Trace.raw, Trace.ParentAt, trace]
      fixture_decide
    have r0 : ((trace (fun _ => b)).raw (core r).source.toEffectiveCore 0).Reaches 0 := .refl
    have r1 := r0.tail (edge 0 1 (by exact Or.inl rfl) (by exact Or.inr (Or.inl rfl)) rfl)
    have right : present b 2 →
        ((trace (fun _ => b)).raw (core r).source.toEffectiveCore 0).Reaches 2 :=
      fun hp => r0.tail (edge 0 2 (Or.inl rfl) hp rfl)
    have rightPresent : ∀ (x : Fin 11), 7 ≤ x.val → present b x → present b 2 :=
      (by decide : ∀ b (x : Fin 11), 7 ≤ x.val → present b x → present b 2) b
    fin_cases x
    · exact r0
    · exact r1
    · exact right hx
    all_goals first
      | exact r1.tail (edge 1 _ (Or.inr (Or.inl rfl)) hx rfl)
      | exact (right (rightPresent _ (by decide) hx)).tail
          (edge 2 _ (rightPresent _ (by decide) hx) hx rfl)

/-- These are full structural traces for every right-parent presence pattern;
only the additional global abstract bound can reject them. -/
theorem structural_valid (r : Option Range) (expanded : Nat → Bool) :
    Structural.Valid (core r).source (trace expanded) where
  identities := by
    constructor
    · rfl
    · fixture_decide
    · fixture_decide
    · rfl
    · fixture_decide
    · fixture_decide
  root_live _ := by exact Or.inl rfl
  parent_live t := (by decide : ∀ b x p, present b x → pool.parent x = some p → present b p)
    (expanded t)
  states t := by
    obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, q⟩ := state_valid r (expanded t)
    exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, q⟩

-- [utest->req~abstract-multiplicity~1]
theorem count (b : Bool) (r : Range) :
    Semantics.AbstractMultiplicity.Global (state b) 1 r ↔
      CountInRange r (if b then 8 else 4) := by
  rw [Semantics.AbstractMultiplicity.global_card]
  cases b <;> rfl

theorem at_iff (r : Option Range) (expanded : Nat → Bool) (t : Nat) :
    At (core r) (trace expanded) t ↔
      CountInRange (Semantics.AbstractMultiplicity.range r) (if expanded t then 8 else 4) := by
  constructor
  · intro h
    exact (count (expanded t) _).mp (h 1 rfl)
  · intro h d hd
    have cases_d : d = 1 ∨ d = 2 := by
      fin_cases d <;> simp_all [core]
    rcases cases_d with rfl | rfl
    · exact (count (expanded t) _).mpr h
    · exact Semantics.AbstractMultiplicity.unrestricted_holds _

/-- Optional ancestor absence is permitted by local exact-four child bounds.
The remaining four heads satisfy 3..6 globally. -/
theorem optional_admitted : Admissible (core (some ⟨3, .finite 6⟩)) (trace (fun _ => false)) := by
  refine ⟨wellFormed _ (by simp [Semantics.AbstractMultiplicity.range, ValidRange, unrestricted]), structural_valid _ _, fun t => ?_⟩
  exact (at_iff _ _ t).mpr (by decide)

/-- Four heads from each parent violate the global upper bound of six. -/
theorem two_parents_rejected : ¬ Valid (core (some ⟨3, .finite 6⟩)) (trace (fun _ => true)) := by
  intro h
  have bad := (at_iff _ _ 0).mp (h.2 0)
  contradiction

/-- Summing the local exact-four minima predicts eight, but an optional parent
may be absent: a global lower bound of five then fails. -/
theorem absent_parent_lower_failure :
    ¬ Valid (core (some ⟨5, .unbounded⟩)) (trace (fun _ => false)) := by
  intro h
  have bad := (at_iff _ _ 0).mp (h.2 0)
  contradiction

/-- Every-state enforcement: time zero succeeds and time one fails. -/
theorem later_violation :
    At (core (some ⟨3, .finite 6⟩)) (trace (fun t => t != 0)) 0 ∧
    ¬ Valid (core (some ⟨3, .finite 6⟩)) (trace (fun t => t != 0)) := by
  refine ⟨(at_iff _ _ 0).mpr (by decide), fun h => ?_⟩
  have bad := (at_iff _ _ 1).mp (h.2 1)
  contradiction

example : Admissible (core (some ⟨4, .finite 4⟩)) (trace (fun _ => false)) :=
  ⟨wellFormed _ (by simp [Semantics.AbstractMultiplicity.range, ValidRange, unrestricted]), structural_valid _ _, fun t => (at_iff _ _ t).mpr (by decide)⟩

example : Admissible (core (some ⟨8, .finite 8⟩)) (trace (fun _ => true)) :=
  ⟨wellFormed _ (by simp [Semantics.AbstractMultiplicity.range, ValidRange, unrestricted]), structural_valid _ _, fun t => (at_iff _ _ t).mpr (by decide)⟩

/-- Omission ignores optimizer zeroing, even with eight actual heads. -/
example : Admissible (core none) (trace (fun _ => true)) :=
  ⟨wellFormed _ (by simp [Semantics.AbstractMultiplicity.range, ValidRange, unrestricted]), structural_valid _ _, fun t => (at_iff _ _ t).mpr (by decide)⟩

/-- One identity lies in three inherited views but contributes once. Distinct
heads across parents have the same reference target and remain separate. -/
example : 3 ∈ (state true).head 1 ∧ 3 ∈ (state true).head 2 ∧ 3 ∈ (state true).head 3 ∧
    (trace (fun _ => true)).deref 0 1 3 0 ∧ (trace (fun _ => true)).deref 0 1 7 0 ∧
    (state true).contains 3 1 3 ∧ (state true).contains 4 2 7 := by
  dsimp only [trace]
  decide

example : (state true).head 3 ∪ (state true).head 2 = (state true).head 2 :=
  Semantics.AbstractMultiplicity.inherited_union _ _ ((structural_valid none _).states 0).inherits
    (Relation.ReflTransGen.single (by decide))

-- [utest->req~abstract-multiplicity~1]
/-- Parentless heads have a global count without any containment relation. -/
example : ∀ p x, ¬ (state true).contains 1 p x := by decide

/-- Small independent extents exercise both ends, including an empty extent. -/
def small (k : Nat) : Configuration Unit (Fin 8) where
  root := 0
  head _ := {x | x.val < k}
  contains _ _ _ := False
  deref _ _ _ := False

instance (k : Nat) (x : Fin 8) : Decidable (x ∈ (small k).head ()) :=
  inferInstanceAs (Decidable (x.val < k))

theorem endpoints (k : Fin 9) :
    Semantics.AbstractMultiplicity.Global (small k.val) () ⟨3, .finite 6⟩ ↔
      3 ≤ k.val ∧ k.val ≤ 6 := by
  rw [Semantics.AbstractMultiplicity.global_card]
  fin_cases k <;> decide

example : Semantics.AbstractMultiplicity.Global (small 0) () ⟨0, .finite 0⟩ ∧
    ¬ Semantics.AbstractMultiplicity.Global (small 0) () ⟨1, .unbounded⟩ ∧
    Semantics.AbstractMultiplicity.Global (small 1) () ⟨0, .finite 1⟩ ∧
    ¬ Semantics.AbstractMultiplicity.Global (small 2) () ⟨0, .finite 1⟩ := by
  simp only [Semantics.AbstractMultiplicity.global_card]
  decide

/-- Unbounded source multiplicity admits an infinite head without assigning
it cardinality zero or assuming a finite ambient universe. -/
example : Semantics.AbstractMultiplicity.Global
    (⟨0, fun _ => Set.univ, fun _ _ _ => False, fun _ _ _ => False⟩ :
      Configuration Unit Nat) () ⟨3, .unbounded⟩ := by
  refine ⟨⟨⟨fun i => ⟨i.val, trivial⟩, ?_⟩⟩, trivial⟩
  intro a b h
  exact Fin.ext (congrArg Subtype.val h)

/-- An aggregate lower bound is not required independently of both subtypes. -/
def splitHeads : Configuration (Fin 3) (Fin 3) where
  root := 0
  head d := {x | if d = 0 then True else if d = 1 then x = 0 else x ≠ 0}
  contains _ _ _ := False
  deref _ _ _ := False

instance (d x : Fin 3) : Decidable (x ∈ splitHeads.head d) := by
  dsimp [splitHeads]
  infer_instance

example : Semantics.AbstractMultiplicity.Global splitHeads 0 ⟨3, .finite 6⟩ ∧
    ¬ Semantics.AbstractMultiplicity.Global splitHeads 1 ⟨3, .finite 6⟩ ∧
    ¬ Semantics.AbstractMultiplicity.Global splitHeads 2 ⟨3, .finite 6⟩ := by
  simp only [Semantics.AbstractMultiplicity.global_card]
  decide

/-- No live declared parents means no nested lower-bound obligation. -/
example : Semantics.AbstractMultiplicity.PerParent (small 0) () () ⟨4, .finite 4⟩ := by
  intro p hp
  exact (Nat.not_lt_zero p.val hp).elim

-- [utest->req~abstract-multiplicity~1]
-- [utest->req~behavioral-snapshot-bridge~1]
example (t : Nat) : Semantics.AbstractMultiplicity.Holds
    (core (some ⟨3, .finite 6⟩)).family.parent
    (core (some ⟨3, .finite 6⟩)).authoredAbstract
    (core (some ⟨3, .finite 6⟩)).authoredMultiplicity
    (Structural.snapshot _ _ optional_admitted.2.1 t) :=
  (snapshot_iff _ _ optional_admitted.2.1 t).mpr (optional_admitted.2.2 t)

/-- The existing admitted nested Port fixture, with an authored nested range. -/
def nestedCore (r : Range) : AbstractMultiplicity.Core 8 :=
  ⟨StructuralExamples.model true false, fun d => if d = 3 then some r else none⟩

def nestedState : Configuration (Fin 8) (Fin 7) :=
  (StructuralExamples.trace false).raw (StructuralExamples.model true false).toEffectiveCore 0

instance (d : Fin 8) (x : Fin 7) : Decidable (x ∈ nestedState.head d) := by
  dsimp only [nestedState, Trace.raw, StructuralExamples.trace]
  infer_instance

instance (d : Fin 8) (p x : Fin 7) : Decidable (nestedState.contains d p x) := by
  dsimp only [nestedState, Trace.raw, Trace.ParentAt, StructuralExamples.trace]
  infer_instance

-- [utest->req~abstract-multiplicity~1]
theorem nested_count (r : Range) :
    Semantics.AbstractMultiplicity.PerParent nestedState 3 2 r ↔ CountInRange r 1 := by
  rw [Semantics.AbstractMultiplicity.perParent_card]
  constructor
  · intro h
    exact h 1 (by decide)
  · intro h p hp
    have eq : p = 1 := (by decide : ∀ p, p ∈ nestedState.head 2 → p = 1) p hp
    subst p
    exact h

theorem nested_at (r : Range) (t : Nat) :
    At (nestedCore r) (StructuralExamples.trace false) t ↔ CountInRange r 1 := by
  constructor
  · intro h
    exact (nested_count r).mp (h 3 rfl)
  · intro h d hd
    have options : d = 1 ∨ d = 3 ∨ d = 7 :=
      (by decide : ∀ d, (StructuralExamples.model true false).authoredAbstract d = true →
        d = 1 ∨ d = 3 ∨ d = 7) d hd
    rcases options with rfl | rfl | rfl
    · exact Semantics.AbstractMultiplicity.unrestricted_holds _
    · exact (nested_count r).mpr h
    · exact Semantics.AbstractMultiplicity.unrestricted_holds _

/-- A fully admitted richer structure, now with exact-one nested abstract Port.
All ordinary bounds and groups are retained. -/
theorem nested_admitted : Admissible (nestedCore one) (StructuralExamples.trace false) := by
  have old := StructuralExamples.admitted true false
  refine ⟨?_, ?_, fun t => (nested_at one t).mpr (by decide)⟩
  · refine { old.1 with reference_refinement := ?_, multiplicity_bounds := ?_ }
    · intro d s o a b edge _ ht _
      have eq : d = 7 := (by decide : ∀ d a,
        ((StructuralExamples.model true false).family.reference d).target = some a → d = 7) d a ht
      subst d
      simp [nestedCore, Core.source, StructuralExamples.model] at edge
    · intro d
      fin_cases d <;> simp [nestedCore, Core.source, StructuralExamples.model,
        Semantics.AbstractMultiplicity.range, one, unrestricted, ValidRange]
  · have ids : Structural.IdentitiesValid (nestedCore one).source (StructuralExamples.trace false) := by
      obtain ⟨a, b, c, d, e, f⟩ := old.2.identities
      exact ⟨a, b, c, d, e, f⟩
    refine ⟨ids, old.2.root_live, old.2.parent_live, fun t => ?_⟩
    refine { old.2.states t with keys := ?_, multiplicities := ?_ }
    · intro d o _ hk
      have noSet : ∀ o, ((nestedCore one).source.family.reference o).kind ≠ .referenceSet := by decide
      exact (noSet o hk).elim
    · intro d c hc p hp
      by_cases hd : d = 3
      · subst d
        have hc' : c = 2 := Option.some.inj hc.symm
        subst c
        exact (nested_count one).mpr (by decide) p hp
      · have unbounded : (nestedCore one).source.family.multiplicity d = unrestricted := by
          simp [nestedCore, Core.source, StructuralExamples.model, hd,
            Semantics.AbstractMultiplicity.range]
        rw [unbounded]
        exact Semantics.AbstractMultiplicity.unrestricted_holds _

example : ¬ Valid (nestedCore ⟨2, .finite 2⟩) (StructuralExamples.trace false) := by
  intro h
  have bad := (nested_at _ 0).mp (h.2 0)
  contradiction

example : ¬ Valid (nestedCore ⟨0, .finite 0⟩) (StructuralExamples.trace false) := by
  intro h
  have bad := (nested_at _ 0).mp (h.2 0)
  contradiction

example : Always (core (some ⟨3, .finite 6⟩)) (trace (fun _ => false)) ↔
    Semantics.AbstractMultiplicity.Holds
      (core (some ⟨3, .finite 6⟩)).family.parent
      (core (some ⟨3, .finite 6⟩)).authoredAbstract
      (core (some ⟨3, .finite 6⟩)).authoredMultiplicity (state false) :=
  constant_iff _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)

/-- Two live instances of one declared parent each own two abstract heads.
A skewed distribution has the same total but violates the local upper bound. -/
def twoParentState (skew : Bool) : Configuration (Fin 2) (Fin 6) where
  root := 0
  head d := {x | if d = 0 then x.val < 2 else 2 ≤ x.val}
  contains d p x := d = 1 ∧ 2 ≤ x.val ∧
    if x.val < (if skew then 5 else 4) then p = 0 else p = 1
  deref _ _ _ := False

instance (b : Bool) (d : Fin 2) (x : Fin 6) :
    Decidable (x ∈ (twoParentState b).head d) := by
  dsimp [twoParentState]
  infer_instance

instance (b : Bool) (d : Fin 2) (p x : Fin 6) :
    Decidable ((twoParentState b).contains d p x) := by
  dsimp [twoParentState]
  infer_instance

-- [utest->req~abstract-multiplicity~1]
example : Semantics.AbstractMultiplicity.PerParent (twoParentState false) 1 0 ⟨2, .finite 2⟩ ∧
    ¬ Semantics.AbstractMultiplicity.Global (twoParentState false) 1 ⟨2, .finite 2⟩ ∧
    ¬ Semantics.AbstractMultiplicity.PerParent (twoParentState true) 1 0 ⟨2, .finite 2⟩ := by
  simp only [Semantics.AbstractMultiplicity.perParent_card,
    Semantics.AbstractMultiplicity.global_card]
  decide

end Clafer.Behavioral.AbstractMultiplicityExamples
