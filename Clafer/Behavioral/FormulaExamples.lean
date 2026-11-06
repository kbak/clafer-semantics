module

public import Clafer.Behavioral.Lowering
public import Clafer.Behavioral.Examples

/-!
# Temporal polarity and environment witnesses

T2/T3/T7 and D1. All trace examples use the independently checked, structurally
valid cycling fixture from #124, with parent absence at 2 and reappearance at 3.
No finite checker, native-decide proof or compiler outcome defines satisfaction.
-/

@[expose] public section
namespace Clafer.Behavioral.FormulaExamples
open Examples

abbrev A (_ : Nat) := Unit
abbrev D (_ : Nat) := Unit
abbrev F (n : Nat) := Formula A D n

def noError : Observation A D (Fin 8) where
  atom _ _ _ := False
  domain _ _ _ := {5}

def error {n} : F n := .atom ()
def source : Environment (Fin 8) 0 := .closed 3
def machine : Environment (Fin 8) 0 := .closed 1

private theorem parent_gone : ¬ cycling.ParentPresent 3 2 := by
  simp [Trace.ParentPresent, cycling, pool, phaseLive]

private theorem parent_survives (t : Nat) : cycling.ParentPresent 1 t := by
  exact Or.inr ⟨0, rfl, cycling_valid.root_live t⟩

-- [utest->req~behavioral-formula-denotation~1]
-- [utest->req~behavioral-signed-normalization~1]
theorem both_polarities :
    (error.eventually : F 0).denote cycling noError true source 0 ∧
    error.eventually.not.denote cycling noError true source 0 := by
  constructor
  · exact Lifetime.eventually_cancel (by decide : 0 ≤ 2) parent_gone
  · intro j _ _
    exact id

theorem nested_negation :
    (error.eventually.not.not.not : F 0).denote cycling noError true source 0 :=
  (Formula.double_negation cycling noError error.eventually.not true source 0).mpr both_polarities.2

/-- This is a concrete failure of negating *after* lifetime lowering. -/
theorem late_negation_rejected :
    ¬ ((error.eventually : F 0).lower.not).eval cycling noError source 0 := by
  intro h
  exact h ((Formula.lower_agrees cycling noError error.eventually source 0).mpr both_polarities.1)

theorem persistent_no_both (a : A 0) (t : Nat) :
    ¬ ((Formula.eventually (.atom a) : F 0).denote cycling noError true machine t ∧
       (Formula.eventually (.atom a) : F 0).not.denote cycling noError true machine t) := by
  rintro ⟨hp, hn⟩
  exact Formula.persistent_eventually_consistent cycling noError a machine t
    (fun j _ => parent_survives j) hp hn

-- [utest->req~behavioral-formula-denotation~1]
/-- Moving the same body up one level changes its owner to the permanent root. -/
theorem attachment_matters :
    (error.eventually : F 0).denote cycling noError true source 0 ∧
    ¬ (error.eventually : F 0).denote cycling noError true machine 0 := by
  refine ⟨both_polarities.1, ?_⟩
  rintro (⟨j, _, hn⟩ | ⟨_, _, _, ha⟩)
  · exact hn (parent_survives j)
  · exact ha

/-- Source 3 disappears at 1, but its parent 1 remains; false next is rejected. -/
theorem source_death_does_not_cancel :
    ¬ (error.next : F 0).denote cycling noError true source 0 := by
  intro h
  exact h (by simp [Trace.ParentPresent, source, Environment.closed, cycling, pool, phaseLive])

/-- The root's own context has plain persistent obligations. -/
theorem root_eventually_false :
    ¬ (error.eventually : F 0).denote cycling noError true (.closed 0) 0 := by
  rintro (⟨j, _, hn⟩ | ⟨_, _, _, ha⟩)
  · exact hn (cycling.parentPresent_root j)
  · exact ha

def beforeGap : Observation A D (Fin 8) := { noError with atom := fun _ _ t => t < 2 }

def eventAtOne : Observation A D (Fin 8) := { noError with atom := fun _ _ t => t = 1 }

-- [utest->req~behavioral-formula-denotation~1]
/-- Fulfillment under a permanent parent, independent of cancellation. -/
theorem persistent_fulfillment :
    (error.eventually : F 0).denote cycling eventAtOne true machine 0 ∧
    error.next.denote cycling eventAtOne true machine 0 ∧
    ¬ error.eventually.not.denote cycling eventAtOne true machine 0 := by
  have hf : (error.eventually : F 0).denote cycling eventAtOne true machine 0 :=
    Or.inr ⟨1, by decide, fun j _ _ => parent_survives j, rfl⟩
  exact ⟨hf, fun _ => rfl, Formula.persistent_eventually_consistent cycling eventAtOne () machine 0
    (fun j _ => parent_survives j) hf⟩

-- [utest->req~behavioral-formula-denotation~1]
/-- The old G obligation ends at the gap; the new lifetime starts a fresh one. -/
theorem no_resumption :
    (error.always : F 0).denote cycling beforeGap true source 0 ∧
    ¬ (error.always : F 0).denote cycling beforeGap true source 3 := by
  constructor
  · change Lifetime.always (cycling.ParentPresent 3) (fun t => t < 2) 0
    exact (Lifetime.always_before_end (a := fun t => t < 2)
      (by decide : 0 ≤ 2) parent_gone).mpr (fun _ _ hj _ => hj)
  · intro h
    have hp : cycling.ParentPresent 3 3 := by simp [Trace.ParentPresent, cycling, pool, phaseLive]
    have bad := h 3 (by decide) (by
      intro k hk hk'
      have : k = 3 := by omega
      subst k
      exact hp)
    exact (by decide : ¬ (3 < 2)) bad

-- [utest->req~behavioral-signed-normalization~1]
/-- all/some/no distribute signs; binding target 5 does not change parent 1. -/
theorem quantified_cancellation :
    (Formula.quant .all () error.eventually.not : F 0).denote cycling noError true source 0 ∧
    (Formula.quant .some () error.eventually : F 0).not.denote cycling noError true source 0 ∧
    (Formula.quant .no () error.eventually : F 0).denote cycling noError true source 0 := by
  have hn : ∀ x : Fin 8, (error.eventually.not : F 1).denote cycling noError true
      (source.push {x}) 0 := by intro _ j _ _; exact id
  exact ⟨fun x _ => hn x, fun x _ => hn x, fun x _ => hn x⟩

def emptyDomain : Observation A D (Fin 8) := { noError with domain := fun _ _ _ => ∅ }

-- [utest->req~behavioral-signed-normalization~1]
theorem empty_quantifiers :
    (Formula.quant .all () error.eventually : F 0).denote cycling emptyDomain true source 0 ∧
    ¬ (Formula.quant .some () error.eventually : F 0).denote cycling emptyDomain true source 0 ∧
    (Formula.quant .no () error.eventually : F 0).denote cycling emptyDomain true source 0 ∧
    ¬ (Formula.quant .one () error.eventually : F 0).denote cycling emptyDomain true source 0 ∧
    (Formula.quant .lone () error.eventually : F 0).denote cycling emptyDomain true source 0 := by
  simp [Formula.denote, polarity, emptyDomain, Quantifier.eval, ExistsUnique]

-- [utest->req~behavioral-signed-normalization~1]
theorem signed_until_duals {n} (a b : F n) :
    (a.strongUntil b).not.normalize true =
      .weakUntil (b.normalize false) (.and (a.normalize false) (b.normalize false)) ∧
    (a.weakUntil b).not.normalize true =
      .strongUntil (b.normalize false) (.and (a.normalize false) (b.normalize false)) := ⟨rfl, rfl⟩

theorem one_barrier :
    (Formula.quant .one () error.eventually : F 0).denote cycling noError true source 0 ∧
    ¬ (Formula.quant .one () error.eventually : F 0).not.denote cycling noError true source 0 ∧
    ¬ (Formula.quant .one () error.eventually.not : F 0).denote cycling noError true source 0 := by
  have hf : ∀ x : Fin 8, (error.eventually : F 1).raw cycling noError (source.push {x}) 0 := by
    intro x
    exact Lifetime.eventually_cancel (by decide : 0 ≤ 2) parent_gone
  have hone : (Formula.quant .one () error.eventually : F 0).denote cycling noError true source 0 := by
    exact ⟨5, ⟨rfl, hf 5⟩, fun _ h => h.1⟩
  refine ⟨hone, fun h => h hone, ?_⟩
  rintro ⟨x, hx, _⟩
  exact hx.2 (hf x)

def twoChoices : Observation A D (Fin 8) := { noError with domain := fun _ _ _ => {5, 6} }

theorem lone_barrier :
    (Formula.quant .lone () error.eventually : F 0).not.denote cycling twoChoices true source 0 := by
  intro h
  have hf : ∀ x : Fin 8, (error.eventually : F 1).raw cycling twoChoices (source.push {x}) 0 := by
    intro x
    exact Lifetime.eventually_cancel (by decide : 0 ≤ 2) parent_gone
  have bad : (5 : Fin 8) = 6 := h 5 (by simp [twoChoices]) 6 (by simp [twoChoices]) (hf 5) (hf 6)
  exact (by decide : (5 : Fin 8) ≠ 6) bad

-- [utest->req~behavioral-signed-normalization~1]
/-- These Boolean forms are interpreted through source signs, not tests of the
already bounded truth value. In particular the temporal guard is not an if-test. -/
theorem boolean_expansions :
    (Formula.implies error.eventually (.not .truth) : F 0).denote cycling noError true source 0 ∧
    (Formula.iff error.eventually error.eventually.not : F 0).denote cycling noError true source 0 ∧
    (Formula.xor error.eventually error.eventually : F 0).denote cycling noError true source 0 ∧
    (Formula.ite error.eventually (.not .truth) .truth : F 0).denote cycling noError true source 0 := by
  have hp := both_polarities.1
  have hn := both_polarities.2
  exact ⟨Or.inl hn, ⟨Or.inl hn, Or.inr hp⟩,
    Or.inl ⟨hp, hn⟩, ⟨Or.inl hn, Or.inr trivial⟩⟩

-- [utest->req~behavioral-formula-denotation~1]
/-- U requires the left operand before cancellation; W can persist forever. -/
theorem until_and_weak_boundaries :
    (Formula.strongUntil .truth error : F 0).denote cycling noError true source 0 ∧
    ¬ (Formula.strongUntil error error : F 0).denote cycling noError true source 0 ∧
    (Formula.weakUntil .truth error : F 0).denote cycling noError true machine 0 := by
  constructor
  · refine ⟨2, by decide, Or.inl parent_gone, ?_⟩
    intro k hk hlt
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl <;>
      simp [Trace.ParentPresent, source, Environment.closed, cycling, pool, phaseLive, Formula.denote, polarity]
  · constructor
    · rintro ⟨j, hj, hn | ha, hleft⟩
      · by_cases hz : j = 0
        · subst j
          exact hn (by simp [Trace.ParentPresent, source, Environment.closed, cycling, pool, phaseLive])
        · exact (hleft 0 (by decide) (by omega)).2
      · exact ha
    · exact Or.inl (fun _ _ _ => trivial)

-- [utest->req~behavioral-formula-denotation~1]
/-- Initial and final anchors inspect the context, not its parent; signs stay
inside the anchor. The root has one initial state and no final state. -/
theorem anchor_boundaries :
    ¬ (error.initially : F 0).denote cycling noError true source 0 ∧
    ¬ (error.initially : F 0).denote cycling noError true source 3 ∧
    (error.initially.not : F 0).denote cycling noError true source 3 ∧
    ¬ (error.finally : F 0).denote cycling noError true source 0 ∧
    (error.finally : F 0).denote cycling noError true (.closed 0) 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact h (by simp [Trace.Starts, source, Environment.closed, cycling, phaseLive])
  · intro h
    apply h
    exact ⟨by simp [source, Environment.closed, cycling, phaseLive],
      Or.inr ⟨2, rfl, by simp [source, Environment.closed, cycling, phaseLive]⟩⟩
  · intro _; exact id
  · intro h; exact h (by simp [Trace.Ends, source, Environment.closed, cycling, phaseLive])
  · intro h; exact cycling.root_never_ends model cycling_valid 0 h

abbrev SF (n : Nat) := Formula (SetAtom (Fin 4)) (SetExpr (Fin 4)) n
def sets := Observation.sets model cycling

-- [utest->req~behavioral-environments~1]
theorem absent_this_and_parent :
    (SetExpr.this : SetExpr (Fin 4) 0).eval model cycling source 1 = ∅ ∧
    1 ∈ (SetExpr.thisStep .parent).eval model cycling source 1 ∧
    (SetExpr.step .parent .this : SetExpr (Fin 4) 0).eval model cycling source 1 = ∅ := by
  have hthis := SetExpr.this_absent model cycling source 1 (by simp [source, Environment.closed, cycling, phaseLive])
  refine ⟨hthis, ?_, ?_⟩
  · exact (SetExpr.direct_parent model cycling source 1 1).mpr
      ⟨rfl, by simp [cycling, phaseLive]⟩
  · simp [SetExpr.eval, Step.image, source, Environment.closed, cycling, phaseLive]

theorem capture_survives_absence :
    (Formula.letSet .this (.next (.atom (.inhabited (.var 0)))) : SF 0).denote cycling sets true source 0 ∧
    ¬ (Formula.letSet .this (.next (.atom (.equal (.var 0) .this))) : SF 0).denote cycling sets true source 0 := by
  have live0 : (SetExpr.this : SetExpr (Fin 4) 0).eval model cycling source 0 = {3} :=
    SetExpr.this_live model cycling source 0 (by simp [source, Environment.closed, cycling, phaseLive])
  constructor
  · intro _
    change ((SetExpr.this : SetExpr (Fin 4) 0).eval model cycling source 0).Nonempty
    rw [live0]; exact ⟨3, rfl⟩
  · intro h
    have hp : cycling.ParentPresent 3 1 := by simp [Trace.ParentPresent, cycling, pool, phaseLive]
    have bad := h hp
    change (SetExpr.this : SetExpr (Fin 4) 0).eval model cycling source 0 =
      {x | x = (3 : Fin 8) ∧ x ∈ cycling.live 1} at bad
    rw [live0] at bad
    have hm : (3 : Fin 8) ∈ ({x | x = (3 : Fin 8) ∧ x ∈ cycling.live 1} : Set (Fin 8)) :=
      bad ▸ (show (3 : Fin 8) ∈ ({3} : Set (Fin 8)) from rfl)
    simpa [cycling, phaseLive] using hm.2

/-- Capture at 3; the same head points to 6 at 3 and 5 at 4, without a birth.
Capturing the old target set differs from navigating the captured head later. -/
theorem current_reference_not_snapshot :
    6 ∈ (SetExpr.step (.deref 2) (.var 0)).eval model cycling (source.push {3}) 3 ∧
    5 ∈ (SetExpr.step (.deref 2) (.var 0)).eval model cycling (source.push {3}) 4 ∧
    6 ∉ (SetExpr.step (.deref 2) (.var 0)).eval model cycling (source.push {3}) 4 ∧
    (SetExpr.var 0 : SetExpr (Fin 4) 1).eval model cycling (source.push {6}) 4 = {6} := by
  simp [SetExpr.captured_deref, SetExpr.captured_set, cycling, phaseLive, phaseDeref]

/-- Captured bag heads remain two identities, even at an equal target. -/
theorem captured_bag_heads :
    (SetExpr.var 0 : SetExpr (Fin 4) 1).eval model cycling (source.push {3, 4}) 1 = {3, 4} ∧
    (3 : Fin 8) ≠ 4 := ⟨rfl, by decide⟩

-- [utest->req~behavioral-environments~1]
theorem nested_capture :
    ((source.push {3}).push {5}).lookup 0 = {5} ∧
    ((source.push {3}).push {5}).lookup 1 = {3} ∧
    ((source.push {3}).push {5}).this = 3 := ⟨rfl, rfl, rfl⟩
end Clafer.Behavioral.FormulaExamples
