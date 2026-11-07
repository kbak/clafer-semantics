module

public import Clafer.Behavioral.ModifierExamples

/-! # Reference modifier boundary regressions

Behavioral §5 Definitions 2–3 and §§6.1–6.2, with the accepted D5 completion
of finalref/finaltarget. Each live parent-declaration instance has exactly three
bag heads. The
same witnesses use either a declared reference or an inherited owner. No
cardinality is relaxed to admit swaps, replacement, or a lifetime reset.
-/

@[expose] public section
namespace Clafer.Behavioral.ModifierBoundaryExamples
open Modifiers ReferenceObservation Semantics DPGraph.Predicates

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 4096

/-- Root, parent, concrete bag field, target, abstract reference supertype. -/
def model (inherited : Bool) : Structural.Core 5 where
  family := {
    root := 0
    parent d := if d = 0 ∨ d = 4 then none else if d = 2 then some 1 else some 0
    reference d := if d = (if inherited then 4 else 2) then .bag 3 else .basic
    super d := if d = 2 then some 4 else none
    origin d := if d = 0 then .syntheticRoot else .user
    isAbstract d := d == 4
    name _ := ""
    multiplicity d := if d = 2 then ⟨3, .finite 3⟩ else unrestricted
    group d := if d = 1 then ⟨none, .bounds ⟨3, .finite 3⟩⟩ else {} }
  id d := ⟨d.val⟩
  group d := if d = 1 then ⟨3, .finite 3⟩ else unrestricted
  authoredAbstract d := d == 4

theorem model_wellFormed (inherited : Bool) : (model inherited).WellFormed := by
  constructor
  · decide +revert
  · cases inherited <;> decide
  · intro d p h; cases inherited <;> fin_cases d <;> simp [model] at h
  · intro d e p h; cases inherited <;> fin_cases d <;> simp [model] at h
  · decide +revert
  · decide +revert
  · decide +revert
  · intro d s o a b edge owner ha hb
    cases inherited
    · have noRef : (model false).family.reference s = .basic :=
        (by decide : ∀ d s, (model false).family.super d = some s →
          (model false).family.reference s = .basic) d s edge
      have hs : s = 4 := (by decide : ∀ d s,
        (model false).family.super d = some s → s = 4) d s edge
      subst s
      have ho : o = 4 := (by decide : ∀ o,
        (model false).toEffectiveCore.Ancestor 4 o → o = 4) o owner.ancestor
      subst o
      exact (owner.has_reference noRef).elim
    · have noRef : (model true).family.reference d = .basic :=
        (by decide : ∀ d s, (model true).family.super d = some s →
          (model true).family.reference d = .basic) d s edge
      simp [noRef, MCS.ReferenceTo.target] at ha
  · exact ⟨fun d => if d = 0 ∨ d = 4 then 0 else if d = 2 then 2 else 1,
      by decide +revert⟩
  · exact ⟨fun d => if d = 2 then 1 else 0, by decide +revert⟩
  · intro a b h; exact Fin.ext (congrArg DeclId.value h)
  · intro d; fin_cases d <;> simp [model, ValidRange, unrestricted]
  · intro d; fin_cases d <;> simp [model, ValidRange, unrestricted]
  · decide +revert

/-- Four possible head identities, with exactly three live whenever parent 1 is live. -/
def pool : Identities (Fin 5) (Fin 9) where
  root := 0
  directType x := if x = 0 then 0 else if x = 1 then 1 else if x.val < 6 then 2 else 3
  parent x := if x = 0 then none else if 2 ≤ x.val ∧ x.val < 6 then some 1 else some 0

inductive Case where
  | fixed | swap | replace | loseTarget | addTarget | bag | headGap | parentGap
  deriving DecidableEq

instance : Fintype Case := ⟨{.fixed, .swap, .replace, .loseTarget, .addTarget, .bag, .headGap, .parentGap},
  by intro c; cases c <;> simp⟩

/-- The last state repeats forever. A head gap replaces 2 by 5 for one state;
a parent gap removes the whole fiber for one state. -/
def live (c : Case) (t : Fin 3) (x : Fin 9) : Bool :=
  if x = 0 ∨ 6 ≤ x.val then true
  else if c = .parentGap ∧ t = 1 then false
  else if x = 1 ∨ x = 3 ∨ x = 4 then true
  else if (c = .replace ∨ c = .loseTarget ∨ c = .addTarget) ∧ t ≠ 0 then x == 5
  else if c = .headGap ∧ t = 1 then x == 5
  else x == 2

/-- A=6, B=7, C=8. The bag case changes A,A,B to A,B,B. -/
def target (c : Case) (t : Fin 3) (x : Fin 9) : Fin 9 :=
  match c with
  | .fixed | .replace => if x = 4 then 7 else 6
  | .swap => if (x = 2) == (t == 0) then 6 else 7
  | .loseTarget => if x = 2 then 6 else 7
  | .addTarget => if x = 3 then 6 else if x = 5 then 8 else 7
  | .bag => if x = 2 ∨ (x = 3 ∧ t = 0) then 6 else 7
  | .headGap => if x = 4 ∨ (x = 2 ∧ t = 2) then 7 else 6
  | .parentGap => if t = 0 then (if x = 4 then 7 else 6)
      else (if x = 4 then 8 else 7)

def fixture (inherited : Bool) (c : Case) : Lasso (Fin 5) 9 2 where
  identities := pool
  loop := 2
  live := live c
  deref t d x y := d == (if inherited then 4 else 2) &&
    decide (2 ≤ x.val ∧ x.val < 6) && live c t x && y == target c t x

private instance (b : Bool) (c : Case) (t : Nat) (x : Fin 9) :
    Decidable (x ∈ (fixture b c).unfold.live t) := by
  dsimp only [Lasso.unfold]; infer_instance

private theorem unrestricted_range (A : Type) : InRange unrestricted A :=
  ⟨⟨{ toFun := Fin.elim0, inj' := fun i => Fin.elim0 i }⟩, trivial⟩

private instance (b : Bool) (c : Case) (t : Fin 3) (d : Fin 5) (x : Fin 9) :
    Decidable (x ∈ (((fixture b c).state t).raw (model b).toEffectiveCore 0).head d) := by
  dsimp only [Trace.raw, Lasso.state, fixture]; infer_instance

private instance (b : Bool) (c : Case) (t : Fin 3) (d : Fin 5) (p x : Fin 9) :
    Decidable (((fixture b c).state t).raw (model b).toEffectiveCore 0 |>.contains d p x) := by
  dsimp only [Trace.raw, Trace.ParentAt, Lasso.state, fixture]; infer_instance

private theorem state_valid (b : Bool) (c : Case) (t : Fin 3) :
    Structural.StateValid (model b) ((fixture b c).state t) 0 := by
  constructor
  · dsimp only [Configuration.Typed, Trace.raw, Trace.ParentAt, Lasso.state, fixture]
    decide +revert
  · dsimp only [Trace.raw, Lasso.state, fixture]; decide +revert
  · dsimp only [Trace.raw, Lasso.state, fixture]; decide +revert
  · dsimp only [Configuration.Inherits, Trace.raw, Lasso.state, fixture]; decide +revert
  · dsimp only [Structural.Abstracts, Trace.raw, Lasso.state, fixture]; decide +revert
  · dsimp only [Configuration.Parents, ExistsUnique, Trace.raw, Trace.ParentAt, Lasso.state, fixture]
    decide +revert
  · dsimp only [Configuration.References, ExistsUnique, Trace.raw, Lasso.state, fixture]
    decide +revert
  · intro d e x y z hy hz
    simp only [Lasso.state, fixture, Bool.and_eq_true, beq_iff_eq] at hy hz
    exact hy.2.trans hz.2.symm
  · intro d o _ ho
    exact ((by decide : ∀ b o, ((model b).family.reference o).kind ≠ .referenceSet) b o ho).elim
  · intro d a hd p hp
    by_cases h : d = 2
    · subst d
      have ha : a = 1 := by simpa [model] using hd.symm
      subst a
      have hparent : p = 1 := (by decide : ∀ b x,
        (model b).toEffectiveCore.Ancestor (pool.directType x) 1 → x = 1) b p hp.2
      subst p
      rw [inRange_card]
      exact (by decide : ∀ b c t,
        live c t 1 = true → CountInRange ((model b).family.multiplicity 2)
          (Fintype.card {x : Fin 9 // (((fixture b c).state t).raw
            (model b).toEffectiveCore 0).contains 2 1 x})) b c t hp.1
    · simpa only [model, ite_eq_right h] using unrestricted_range
        {x // (((fixture b c).state t).raw (model b).toEffectiveCore 0).contains d p x}
  · intro d _ p
    by_cases hd : d = 1
    · subst d
      have hp : p.val = 1 := (by decide : ∀ b x,
        (model b).toEffectiveCore.Ancestor (pool.directType x) 1 → x = 1) b p.val p.property.2
      have alive : live c t 1 = true := hp ▸ p.property.1
      change InRange _ {x // Semantics.Groups.ChildObjects _ _ _ p.val x}
      simp only [hp]
      let : DecidablePred (Semantics.Groups.ChildObjects (model b).family
          (((fixture b c).state t).raw (model b).toEffectiveCore 0) 1 1) := by
        unfold Semantics.Groups.ChildObjects
        change DecidablePred (fun x => ∃ a, (model b).toEffectiveCore.Ancestor 1 a ∧ _)
        infer_instance
      rw [inRange_card]
      have bound : ∀ b c t, live c t 1 = true → CountInRange
          ((model b).family.group 1).effective.range
          (Fintype.card {x : Fin 9 // ∃ a, (model b).toEffectiveCore.Ancestor 1 a ∧
            ∃ d, (model b).family.parent d = some a ∧
            (((fixture b c).state t).raw (model b).toEffectiveCore 0).contains d 1 x}) := by decide
      exact bound b c t alive
    · simpa only [model, ite_eq_right hd, GroupCard.range] using unrestricted_range
        {x // Semantics.Groups.ChildObjects (model b).family
          (((fixture b c).state t).raw (model b).toEffectiveCore 0) d p.val x}
  · dsimp only [Configuration.DeclarationDisjoint, Trace.raw, Lasso.state, fixture]
    decide +revert
  · intro x hx
    have root : (((fixture b c).state t).raw (model b).toEffectiveCore 0).Reaches 0 := .refl
    have edge : ∀ x, live c t x = true → x ≠ 0 → ∃ p,
        (p = 0 ∨ (p = 1 ∧ live c t 1 = true)) ∧ ∃ d,
        (((fixture b c).state t).raw (model b).toEffectiveCore 0).contains d p x := by
      dsimp only [Trace.raw, Trace.ParentAt, Lasso.state, fixture]
      clear * - b c t
      decide +revert
    by_cases h0 : x = 0
    · subst x; exact root
    obtain ⟨p, hp, he⟩ := edge x hx h0
    rcases hp with rfl | ⟨rfl, hp⟩
    · exact root.tail he
    · exact (root.tail ⟨1, by
        dsimp only [Trace.raw, Trace.ParentAt, Lasso.state, fixture]
        exact (by decide : ∀ b c t, live c t 1 = true →
          (live c t 0 = true ∧ live c t 1 = true ∧ pool.parent 1 = some 0) ∧
          (model b).toEffectiveCore.Ancestor (pool.directType 1) 1 ∧
          (model b).family.parent 1 ≠ none) b c t hp⟩).tail he

-- [utest->req~behavioral-modifiers~1]
theorem admitted (b : Bool) (c : Case) :
    Structural.Admissible (model b) (fixture b c).unfold := by
  refine ⟨model_wellFormed b, ?_⟩
  constructor
  · constructor <;> dsimp only [Lasso.unfold, fixture] <;> decide +revert
  · intro t; change live c ((fixture b c).clock t).1 0 = true; unfold live; simp
  · intro t
    exact (by decide : ∀ c t x p,
      live c t x = true → pool.parent x = some p → live c t p = true) c _
  · intro t
    have h := state_valid b c ((fixture b c).clock t).1
    exact ⟨h.typed, h.root_head, h.root_separate, h.inherits, h.abstracts,
      h.parents, h.references, h.coherent, h.keys, h.multiplicities, h.groups,
      h.disjoint, h.reachable⟩

/-- Resolved reference observation, with occurrence identity still present. -/
def refAt (c : Case) (i : Fin 3) (x y : Fin 9) : Prop :=
  2 ≤ x.val ∧ x.val < 6 ∧ live c i x = true ∧ y = target c i x

private instance (c : Case) (i : Fin 3) (x y : Fin 9) : Decidable (refAt c i x y) := by
  unfold refAt; infer_instance

theorem reference_at (b : Bool) (c : Case) (t : Nat) (x y : Fin 9) :
    (Structural.current (model b) (fixture b c).unfold t).deref 2 x y ↔
      refAt c ((fixture b c).clock t).1 x y := by
  have owner : InheritedReference.Owner (model b).family 2 (if b then 4 else 2) := by
    cases b
    · exact .declared (by decide)
    · exact .inherited (by decide) (by decide) (.declared (by decide))
  change InheritedReference.deref _ _ _ _ _ ↔ _
  rw [InheritedReference.deref_owner owner]
  dsimp only [Trace.raw, Lasso.unfold]
  generalize ((fixture b c).clock t).1 = i
  dsimp only [fixture]
  clear * - b c i x y
  decide +revert

def targetAt (c : Case) (i : Fin 3) (p y : Fin 9) : Prop :=
  p = 1 ∧ ∃ x, refAt c i x y

private instance (c : Case) (i : Fin 3) (p y : Fin 9) : Decidable (targetAt c i p y) := by
  unfold targetAt; infer_instance

theorem targets_at (b : Bool) (c : Case) (t : Nat) (p y : Fin 9) :
    y ∈ targets (Structural.current (model b) (fixture b c).unfold t) 2 p ↔
      targetAt c ((fixture b c).clock t).1 p y := by
  simp only [targets, assignments, Set.mem_ofPred_eq, reference_at]
  change (∃ x, (((fixture b c).unfold.raw (model b).toEffectiveCore t).contains 2 p x) ∧ _) ↔ _
  dsimp only [Trace.raw, Trace.ParentAt, Lasso.unfold]
  generalize ((fixture b c).clock t).1 = i
  dsimp only [fixture]
  clear * - b c i p y
  decide +revert

private theorem ref_stable (b : Bool) (c : Case)
    (hc : c = .fixed ∨ c = .replace ∨ c = .loseTarget ∨ c = .addTarget ∨ c = .headGap ∨ c = .parentGap) :
    FinalRef (model b) (fixture b c).unfold 2 := by
  intro x _
  rw [stable_iff_adjacent]
  intro t ht hn
  ext y
  simp only [Set.mem_ofPred_eq, reference_at, Lasso.clock_succ, Lasso.step]
  change live c ((fixture b c).clock t).1 x = true at ht
  change live c ((fixture b c).clock (t + 1)).1 x = true at hn
  simp only [Lasso.clock_succ, Lasso.step] at hn
  generalize ((fixture b c).clock t).1 = i at *
  clear * - b c hc x y i ht hn
  revert ht hn
  exact (by decide : ∀ b c i x y,
    (c = .fixed ∨ c = .replace ∨ c = .loseTarget ∨ c = .addTarget ∨ c = .headGap ∨ c = .parentGap) →
    live c i x = true → live c ((fixture b c).next i) x = true →
    (refAt c i x y ↔ refAt c ((fixture b c).next i) x y)) b c i x y hc

private theorem target_stable (b : Bool) (c : Case) (hc : c ≠ .loseTarget ∧ c ≠ .addTarget) :
    FinalTarget (model b) (fixture b c).unfold 2 := by
  intro p
  rw [stable_iff_adjacent]
  intro t ht hn
  ext y
  simp only [targets_at, Lasso.clock_succ, Lasso.step]
  change live c ((fixture b c).clock t).1 p = true at ht
  change live c ((fixture b c).clock (t + 1)).1 p = true at hn
  simp only [Lasso.clock_succ, Lasso.step] at hn
  generalize ((fixture b c).clock t).1 = i at *
  clear * - b c hc p y i ht hn
  revert ht hn
  exact (by decide : ∀ b c i p y, (c ≠ .loseTarget ∧ c ≠ .addTarget) →
    live c i p = true → live c ((fixture b c).next i) p = true →
    (targetAt c i p y ↔ targetAt c ((fixture b c).next i) p y)) b c i p y hc

-- [utest->req~behavioral-modifiers~1]
theorem replacement_both (b : Bool) :
    FinalRef (model b) (fixture b .replace).unfold 2 ∧
    FinalTarget (model b) (fixture b .replace).unfold 2 :=
  ⟨ref_stable b .replace (by simp), target_stable b .replace (by decide)⟩

-- [utest->req~behavioral-modifiers~1]
theorem replacement_not_final (b : Bool) : ¬ Final (model b) (fixture b .replace).unfold 2 := by
  intro h
  have eq := (stable_iff_adjacent _ _).mp (h.1 1) 0 (by cases b <;> decide)
    (by cases b <;> decide)
  have old : 2 ∈ heads (Structural.current (model b) (fixture b .replace).unfold 0) 2 1 := by
    change (((fixture b .replace).unfold.raw (model b).toEffectiveCore 0).contains 2 1 2)
    dsimp only [Trace.raw, Trace.ParentAt, Lasso.unfold]; cases b <;> decide
  have gone := Set.ext_iff.mp eq 2 |>.mp old
  change (((fixture b .replace).unfold.raw (model b).toEffectiveCore 1).contains 2 1 2) at gone
  have absent : ¬ (((fixture b .replace).unfold.raw (model b).toEffectiveCore 1).contains 2 1 2) := by
    dsimp only [Trace.raw, Trace.ParentAt, Lasso.unfold]; cases b <;> decide
  exact absent gone

-- [utest->req~behavioral-modifiers~1]
theorem loses_target_only (b : Bool) :
    FinalRef (model b) (fixture b .loseTarget).unfold 2 ∧
    ¬ FinalTarget (model b) (fixture b .loseTarget).unfold 2 := by
  refine ⟨ref_stable b .loseTarget (by simp), ?_⟩
  intro h
  have eq := (stable_iff_adjacent _ _).mp (h 1) 0 (by cases b <;> decide) (by cases b <;> decide)
  have old : 6 ∈ targets (Structural.current (model b) (fixture b .loseTarget).unfold 0) 2 1 :=
    (targets_at b .loseTarget 0 1 6).mpr (by cases b <;> decide)
  have bad := (targets_at b .loseTarget 1 1 6).mp (Set.ext_iff.mp eq 6 |>.mp old)
  exact (by cases b <;> decide : ¬ targetAt .loseTarget ((fixture b .loseTarget).clock 1).1 1 6) bad

-- [utest->req~behavioral-modifiers~1]
theorem swap_target_only (b : Bool) :
    FinalTarget (model b) (fixture b .swap).unfold 2 ∧
    ¬ FinalRef (model b) (fixture b .swap).unfold 2 := by
  refine ⟨target_stable b .swap (by decide), ?_⟩
  intro h
  have eq := (stable_iff_adjacent _ _).mp (h 2 .refl) 0 (by cases b <;> decide) (by cases b <;> decide)
  have old := (reference_at b .swap 0 2 6).mpr (by cases b <;> decide)
  have bad := (reference_at b .swap 1 2 6).mp (Set.ext_iff.mp eq 6 |>.mp old)
  exact (by cases b <;> decide : ¬ refAt .swap ((fixture b .swap).clock 1).1 2 6) bad

/-- Each supplied annotation remains a separate effective obligation. -/
def annotations (inherited : Bool) (d : Fin 5) : Set Modifier :=
  {modifier | d = (if inherited then 4 else 2) ∧
    (modifier = .finalref ∨ modifier = .finaltarget)}

theorem effective_both (b : Bool) (d : Fin 5) (modifier : Modifier) :
    Effective (model b).family (annotations b) d modifier ↔
      (d = 2 ∨ (b = true ∧ d = 4)) ∧
        (modifier = .finalref ∨ modifier = .finaltarget) := by
  change (∃ a, (model b).toEffectiveCore.Ancestor d a ∧
    a = (if b then 4 else 2) ∧ (modifier = .finalref ∨ modifier = .finaltarget)) ↔ _
  cases modifier <;> decide +revert

private theorem inherited_super_reference (c : Case) (t : Nat) (x y : Fin 9) :
    (Structural.current (model true) (fixture true c).unfold t).deref 4 x y ↔
      (Structural.current (model true) (fixture true c).unfold t).deref 2 x y := by
  rw [reference_at]
  change InheritedReference.deref _ _ _ _ _ ↔ _
  rw [InheritedReference.deref_owner (show InheritedReference.Owner (model true).family 4 4
    from .declared (by decide))]
  dsimp only [Trace.raw, Lasso.unfold]
  generalize ((fixture true c).clock t).1 = i
  dsimp only [fixture]
  clear * - c i x y
  decide +revert

private theorem combined_holds (b : Bool) (c : Case)
    (hr : FinalRef (model b) (fixture b c).unfold 2)
    (ht : FinalTarget (model b) (fixture b c).unfold 2) :
    Holds (model b) (fixture b c).unfold (annotations b) := by
  intro d
  simp only [effective_both]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨_, impossible | impossible⟩ <;> cases impossible
  · rintro ⟨_, impossible | impossible⟩ <;> cases impossible
  · rintro ⟨rfl | ⟨rfl, rfl⟩, _⟩
    · exact hr
    · intro x hx i j hij life
      have hx2 : (model true).toEffectiveCore.Ancestor (pool.directType x) 2 :=
        (by decide : ∀ x, (model true).toEffectiveCore.Ancestor (pool.directType x) 4 →
          (model true).toEffectiveCore.Ancestor (pool.directType x) 2) x hx
      ext y
      simp only [Set.mem_ofPred_eq, inherited_super_reference]
      exact Set.ext_iff.mp (hr x hx2 i j hij life) y
  · rintro ⟨rfl | ⟨rfl, rfl⟩, _⟩
    · exact ht
    · intro p i j _ _
      have empty (t : Nat) : targets (Structural.current (model true)
          (fixture true c).unfold t) 4 p = ∅ := by
        ext y
        simp only [targets, assignments, heads, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
        change (∃ x, (((fixture true c).unfold.raw (model true).toEffectiveCore t).contains 4 p x) ∧ _) ↔ False
        simp [Trace.raw, model]
      exact (empty i).trans (empty j).symm

-- [utest->req~behavioral-modifiers~1]
theorem combined_replacement (b : Bool) :
    Holds (model b) (fixture b .replace).unfold (annotations b) ∧
    ¬ Final (model b) (fixture b .replace).unfold 2 :=
  ⟨combined_holds b .replace (replacement_both b).1 (replacement_both b).2,
    replacement_not_final b⟩

-- [utest->req~behavioral-modifiers~1]
theorem neither_modifier_can_be_dropped (b : Bool) :
    ¬ Holds (model b) (fixture b .swap).unfold (annotations b) ∧
    ¬ Holds (model b) (fixture b .loseTarget).unfold (annotations b) := by
  constructor
  · intro h
    exact (swap_target_only b).2 ((h 2).2.2.1 ((effective_both b 2 .finalref).mpr (by simp)))
  · intro h
    exact (loses_target_only b).2 ((h 2).2.2.2 ((effective_both b 2 .finaltarget).mpr (by simp)))

-- [utest->req~behavioral-modifiers~1]
theorem combined_fixed (b : Bool) : Holds (model b) (fixture b .fixed).unfold (annotations b) := by
  have final : Final (model b) (fixture b .fixed).unfold 2 :=
    ⟨fun _ _ _ _ _ => rfl, ref_stable b .fixed (by simp)⟩
  exact combined_holds b .fixed final.2
    (final_implies_finalTarget (model b) (fixture b .fixed).unfold 2 final)

-- [utest->req~behavioral-modifiers~1]
theorem adds_target_only (b : Bool) :
    FinalRef (model b) (fixture b .addTarget).unfold 2 ∧
    ¬ FinalTarget (model b) (fixture b .addTarget).unfold 2 := by
  refine ⟨ref_stable b .addTarget (by simp), ?_⟩
  intro h
  have eq := (stable_iff_adjacent _ _).mp (h 1) 0 (by cases b <;> decide) (by cases b <;> decide)
  have new := (targets_at b .addTarget 1 1 8).mpr (by cases b <;> decide)
  have bad := (targets_at b .addTarget 0 1 8).mp (Set.ext_iff.mp eq 8 |>.mpr new)
  exact (by cases b <;> decide : ¬ targetAt .addTarget ((fixture b .addTarget).clock 0).1 1 8) bad

/-- Count targets by head occurrence, without quotienting repeated targets. -/
def bagTargets (c : Case) (i : Fin 3) : Multiset (Fin 9) :=
  ((Finset.univ.filter (fun x : Fin 9 => 2 ≤ x.val ∧ x.val < 6 ∧ live c i x = true)).val).map
    (target c i)

-- [utest->req~behavioral-modifiers~1]
theorem bag_multiplicity (b : Bool) :
    bagTargets .bag 0 = {6, 6, 7} ∧ bagTargets .bag 1 = {6, 7, 7} ∧
    FinalTarget (model b) (fixture b .bag).unfold 2 ∧
    heads (Structural.current (model b) (fixture b .bag).unfold 0) 2 1 =
      heads (Structural.current (model b) (fixture b .bag).unfold 1) 2 1 := by
  refine ⟨by decide, by decide, target_stable b .bag (by decide), ?_⟩
  rfl

-- [utest->req~behavioral-modifiers~1]
theorem bag_image (b : Bool) :
    targets (Structural.current (model b) (fixture b .bag).unfold 0) 2 1 = {6, 7} ∧
    targets (Structural.current (model b) (fixture b .bag).unfold 1) 2 1 = {6, 7} := by
  constructor <;> ext y <;> rw [targets_at] <;> decide +revert

-- [utest->req~behavioral-modifiers~1]
theorem head_gap_resets (b : Bool) :
    Holds (model b) (fixture b .headGap).unfold (annotations b) ∧
    (∀ t, 1 ∈ (fixture b .headGap).unfold.live t) ∧
    (fixture b .headGap).unfold.Starts 2 2 ∧
    (Structural.current (model b) (fixture b .headGap).unfold 0).deref 2 2 6 ∧
    (Structural.current (model b) (fixture b .headGap).unfold 2).deref 2 2 7 := by
  refine ⟨combined_holds b .headGap (ref_stable b .headGap (by simp))
    (target_stable b .headGap (by decide)), ?_, ?_, ?_, ?_⟩
  · intro t
    change live .headGap ((fixture b .headGap).clock t).1 1 = true
    simp [live]
  · rw [Trace.starts_succ]
    change live .headGap ((fixture b .headGap).clock 2).1 2 = true ∧
      ¬ live .headGap ((fixture b .headGap).clock 1).1 2 = true
    cases b <;> decide
  · exact (reference_at b .headGap 0 2 6).mpr (by cases b <;> decide)
  · exact (reference_at b .headGap 2 2 7).mpr (by cases b <;> decide)

-- [utest->req~behavioral-modifiers~1]
theorem parent_gap_resets (b : Bool) :
    Holds (model b) (fixture b .parentGap).unfold (annotations b) ∧
    (fixture b .parentGap).unfold.Starts 2 1 ∧
    targets (Structural.current (model b) (fixture b .parentGap).unfold 0) 2 1 ≠
      targets (Structural.current (model b) (fixture b .parentGap).unfold 2) 2 1 := by
  refine ⟨combined_holds b .parentGap (ref_stable b .parentGap (by simp))
    (target_stable b .parentGap (by decide)), ?_, ?_⟩
  · rw [Trace.starts_succ]
    change live .parentGap ((fixture b .parentGap).clock 2).1 1 = true ∧
      ¬ live .parentGap ((fixture b .parentGap).clock 1).1 1 = true
    cases b <;> decide
  · intro eq
    have old := (targets_at b .parentGap 0 1 6).mpr (by cases b <;> decide)
    have bad := (targets_at b .parentGap 2 1 6).mp (Set.ext_iff.mp eq 6 |>.mp old)
    exact (by cases b <;> decide : ¬ targetAt .parentGap ((fixture b .parentGap).clock 2).1 1 6) bad

end Clafer.Behavioral.ModifierBoundaryExamples
