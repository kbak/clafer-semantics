module

public import Clafer.Behavioral.AbsentReference
public import Clafer.Behavioral.LassoExamples
public import Clafer.Behavioral.PrimitiveExpressionExamples

/-!
# Accepted absent-reference cases on admitted traces

Issue #168 A–F, behavioral §5 Definitions 2–5 and §6.1 with T2/T7/T11.
The finite fixture uses distinct target identities 5/6; singleton-set reasoning
is independent of their labels. `AbsentReference` separately instantiates the
same laws at literal mathematical integers, including 3/4, using the primitive
adapter. No Haskell or solver result supplies these proofs.
-/

@[expose] public section
namespace Clafer.Behavioral.AbsentReferenceExamples
open Examples

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Outcome 0: same head/value; 1: child gap; 2: replacement; 3: parent gap;
4: same head/different value. Slot 2 restores the original head and value.
Looping to slot 1 exercises exactly the same cases on the last-to-loop edge. -/
def fixture (outcome : Fin 5) (loop : Fin 3 := 1) : Lasso (Fin 4) 8 2 where
  identities := pool
  loop := loop
  live s x := x == 0 || x == 5 || x == 6 || (x == 1 && !(s == 1 && outcome == 3)) ||
    (x == 3 && (s != 1 || outcome == 0 || outcome == 4)) ||
    (x == 4 && s == 1 && outcome == 2)
  deref s d x y := d == 2 &&
    ((x == 3 && (s != 1 || outcome == 0 || outcome == 4)) ||
      (x == 4 && s == 1 && outcome == 2)) &&
    y == (if s == 1 && outcome == 4 then 6 else 5)

-- [utest->req~behavioral-reference-atoms~1]
theorem fixture_valid (outcome : Fin 5) (loop : Fin 3) :
    (fixture outcome loop).unfold.Valid model :=
  (Lasso.valid_iff_unfold _ _).mp ((Lasso.checks_iff _ _).mp (by decide +revert))

abbrev F := Formula (SetAtom (Fin 4)) (SetExpr (Fin 4)) 1

/-- Capture the expected target set, retaining attachment to head 3. -/
def env : FiniteEnvironment 8 1 := (FiniteEnvironment.closed 3).push {5}
def value : F := .atom (.equal (.thisStep (.deref 2)) (.var 0))
def present : F := .atom (.inhabited .this)

noncomputable def check (L : Lasso (Fin 4) 8 2) (f : F) (t : Nat) : Bool :=
  (f.normalize true).lower.finite L (FiniteObservation.sets model L) env (L.clock t)

theorem check_agrees (L : Lasso (Fin 4) 8 2) (f : F) (t : Nat) :
    check L f t = true ↔ f.denote L.unfold (.sets model L.unfold) true env.realize t :=
  Core.normalized_finite_agrees L _ _ (FiniteObservation.sets_agrees model L) f true env t

-- [utest->req~behavioral-formula-denotation~1]
-- [utest->req~behavioral-environments~1]
/-- A–E, at the ordinary edge 0→1 and the loop edge 2→1. F is checked below
as an entire model without future constraints. Outcome 4 rejects a wrong value. -/
theorem accepted_outcomes :
    ∀ t ∈ ([0, 2] : List Nat),
      check (fixture 0) value.next t = true ∧
      check (fixture 1) value.next t = false ∧
      check (fixture 2) value.next t = false ∧
      check (fixture 3) value.next t = true ∧
      check (fixture 1) value.not.next t = true ∧
      check (fixture 4) value.next t = false := by
  simp [check, value, Formula.normalize, Formula.lower, FiniteObservation.sets, SetAtom.finite]
  decide

/-- These are source judgments on the infinite unfolding, not just finite
Boolean answers. All five fixtures have independent structural validity. -/
theorem source_outcomes (t : Nat) (ht : t ∈ ([0, 2] : List Nat)) :
    value.next.denote (fixture 0).unfold (.sets model (fixture 0).unfold) true env.realize t ∧
    ¬ value.next.denote (fixture 1).unfold (.sets model (fixture 1).unfold) true env.realize t ∧
    ¬ value.next.denote (fixture 2).unfold (.sets model (fixture 2).unfold) true env.realize t ∧
    value.next.denote (fixture 3).unfold (.sets model (fixture 3).unfold) true env.realize t ∧
    value.not.next.denote (fixture 1).unfold (.sets model (fixture 1).unfold) true env.realize t := by
  obtain ⟨ha, hb, hc, hd, he, _⟩ := accepted_outcomes t ht
  refine ⟨(check_agrees _ _ _).mp ha, ?_, ?_,
    (check_agrees _ _ _).mp hd, (check_agrees _ _ _).mp he⟩
  · intro h; have := (check_agrees _ _ _).mpr h; simp [hb] at this
  · intro h; have := (check_agrees _ _ _).mpr h; simp [hc] at this

-- [utest->req~behavioral-reference-atoms~1]
/-- Child loss, replacement, parent loss and same-identity rebirth are explicit
states. Neither future rebirth nor a replacement target repairs the failed X. -/
theorem identities_and_gaps :
    (3 : Fin 8) ∉ (fixture 1).unfold.live 1 ∧
    (fixture 1).unfold.Starts 2 3 ∧
    (3 : Fin 8) ∉ (fixture 2).unfold.live 1 ∧
    (4 : Fin 8) ∈ (fixture 2).unfold.live 1 ∧
    (fixture 2).unfold.deref 1 2 4 5 ∧
    ¬ (fixture 3).unfold.ParentPresent 3 1 ∧
    (fixture 3).unfold.Starts 2 1 := by
  simp only [Trace.starts_succ, Trace.ParentPresent, Lasso.unfold, Set.mem_ofPred_eq]
  decide

-- [utest->req~behavioral-environments~1]
theorem capture_observes_absence :
    (SetExpr.var 0).eval model (fixture 1).unfold
      ((Environment.closed 3).push {3}) 1 = {3} ∧
    (SetExpr.step (.deref 2) (.var 0)).eval model (fixture 1).unfold
      ((Environment.closed 3).push {3}) 1 = ∅ :=
  AbsentReference.captured_empty model _ _ (by
    change (fixture 1).live ((fixture 1).clock 1).1 3 ≠ true
    decide) 2

/-- After the parent gap, the original head returns with a different value. -/
def afterParentGap : Lasso (Fin 4) 8 2 :=
  {fixture 3 with deref := fun s d x y =>
    if s == 2 then d == 2 && x == 3 && y == 6 else (fixture 3).deref s d x y}

-- [utest->req~behavioral-formula-denotation~1]
/-- Both contradictory next requirements cancel at the parent gap; a fresh
requirement at rebirth is new. The old G stops before that rebirth permanently. -/
theorem cancelled_does_not_resume :
    check (fixture 3) (.and value.next value.not.next) 0 = true ∧
    check afterParentGap value.always 0 = true ∧
    check afterParentGap value.always 2 = false := by
  simp [check, value, Formula.normalize, Formula.lower, FiniteObservation.sets, SetAtom.finite]
  decide

theorem afterParentGap_valid : afterParentGap.unfold.Valid model :=
  (Lasso.valid_iff_unfold _ _).mp ((Lasso.checks_iff _ _).mp (by decide))

-- [utest->req~behavioral-transition-sugar~1]
def transition : F :=
  (Transitions.Chain.link value none .immediate (.stop value)).expand present

/-- An enabled immediate value transition retains the same head; a disabled
transition permits disappearance. Test both ordinary and last-to-loop edges. -/
theorem transition_boundaries :
    ∀ t ∈ ([0, 2] : List Nat),
      check (fixture 0) transition t = true ∧
      check (fixture 1) transition t = false ∧
      check (fixture 2) transition t = false ∧
      check (fixture 3) transition t = true ∧
      check (fixture 1)
        ((Transitions.Chain.link value.not none .immediate (.stop value)).expand present) t = true := by
  simp [check, transition, Transitions.Chain.expand, Transitions.precondition,
    Transitions.step, value, present, Formula.normalize, Formula.lower,
    FiniteObservation.sets, SetAtom.finite]
  decide

def otherValue : F := .atom (.equal (.thisStep (.deref 2)) (.diff (.extent 3) (.var 0)))

/-- A two-value increment/reset counter over the two distinct target objects. -/
def counter : F := .and
  ((Transitions.Chain.link value none .immediate (.stop otherValue)).expand present)
  ((Transitions.Chain.link otherValue none .immediate (.stop value)).expand present)

-- [utest->req~behavioral-transition-sugar~1]
theorem counter_boundaries :
    check (fixture 4) counter.always 0 = true ∧
    check (fixture 4) counter 2 = true ∧
    check (fixture 1) counter 0 = false ∧
    check (fixture 2) counter 2 = false ∧
    check (fixture 3) counter 2 = true := by
  simp [check, counter, otherValue, Transitions.Chain.expand, Transitions.precondition,
    Transitions.step, value, present, Formula.normalize, Formula.lower,
    FiniteObservation.sets, SetAtom.finite]
  decide

-- [utest->req~behavioral-formula-denotation~1]
/-- F: optional heads disappear in a whole structural model with no pending
constraint. Structural admission alone does not create a value obligation. -/
theorem permitted_disappearance :
    ∃ τ : Trace (Fin 4) (Fin 8),
      (Properties.Model.structural (Structural.Core.ofEffective model)
        (fun τ => PartialObservation.ofTotal (Observation.sets model τ)) ∅).Satisfies τ ∧
      (3 : Fin 8) ∈ τ.live 0 ∧ (3 : Fin 8) ∉ τ.live 1 := by
  refine ⟨(fixture 1).unfold, ⟨?_, ?_⟩, by trivial, by
    change (fixture 1).live ((fixture 1).clock 1).1 3 ≠ true
    decide⟩
  · exact ⟨Structural.Core.ofEffective_wellFormed model_wellFormed model_supported (by decide),
      (Structural.valid_iff_common model_wellFormed model_supported (by decide) _).mpr
        (fixture_valid 1 1)⟩
  · intro c hc; exact hc.elim

-- [utest->req~behavioral-reference-atoms~1]
/-- Adding hidden tuples to either an absent or never-live head invalidates the
candidate even if the displayed live reference image would be unchanged. -/
def hidden (x : Fin 8) : Lasso (Fin 4) 8 2 :=
  {fixture 1 with deref := fun s d a y => (fixture 1).deref s d a y ||
    (s == 1 && d == 2 && a == x && y == 5)}

theorem hidden_rejected :
    decide ((hidden 3).checks model) = false ∧
    decide ((hidden 4).checks model) = false := by decide

section IntegerConsequences
open AbsentReference
variable {k n : Nat} {U : Type} (m : Structural.Core k) (τ : Trace (Fin k) U)
    (R : Constraints.IntegerRealization U) (ρ : Environment U n) (t : Nat) (d : Fin k)

-- [utest->req~behavioral-formula-denotation~1]
/-- Literal 3/4 contradiction in the actual strict primitive observation API,
regardless of whether the child survives, disappears, or is replaced. -/
theorem three_four_contradiction (parent : τ.ParentPresent ρ.this (t + 1)) :
    ¬ ((equalValue d 3).next.Satisfies τ (.primitives m τ R) true ρ t ∧
       (equalValue d 4).next.Satisfies τ (.primitives m τ R) true ρ t) :=
  next_distinct_values m τ R ρ t d 3 4 (by decide) parent

-- [utest->req~behavioral-reference-atoms~1]
/-- Strict extraction from an absent head is undefined in both source signs;
the numeric zero comparison after coercion is instead defined and true. -/
theorem strict_vs_coercion (absent : ρ.this ∉ τ.live t) :
    ¬ (Formula.atom (.integerEqual (.extract (.set (.thisStep (.deref d)))) (.literal 0)) :
      Formula (PrimitiveExpression.Atom (Fin k)) (CollectionExpr (Fin k)) n).Satisfies
        τ (.primitives m τ R) true ρ t ∧
    ¬ (Formula.atom (.integerEqual (.extract (.set (.thisStep (.deref d)))) (.literal 0)) :
      Formula (PrimitiveExpression.Atom (Fin k)) (CollectionExpr (Fin k)) n).Satisfies
        τ (.primitives m τ R) false ρ t ∧
    (PrimitiveExpression.Atom.integerEqual (.coerce (.set (.thisStep (.deref d))))
      (.literal 0)).eval m.toEffectiveCore (Structural.observed m τ) R ρ t = some True := by
  have strict := (absent_arithmetic m τ R ρ t d absent).2
  refine ⟨?_, ?_, absent_zero_comparison m τ R ρ t d absent⟩ <;>
    simp [Formula.Satisfies, Formula.Defined, PartialObservation.primitives,
      PrimitiveExpression.Atom.eval, strict, Constraints.lift₂]

-- [utest->req~behavioral-reference-atoms~1]
theorem zero_divisor_neither (absent : ρ.this ∉ τ.live t) (v : Int) :
    ∀ sign, ¬ (Formula.atom (.less
      (.binary .divide (.literal v) (.coerce (.set (.thisStep (.deref d)))))
      (.literal 1)) : Formula (PrimitiveExpression.Atom (Fin k)) (CollectionExpr (Fin k)) n).Satisfies τ (.primitives m τ R) sign ρ t := by
  intro sign
  have missing := absent_divisor m τ R ρ t d absent v
  simp [Formula.Satisfies, Formula.Defined, PartialObservation.primitives,
    PrimitiveExpression.Atom.eval, missing, Constraints.lift₂]

end IntegerConsequences

namespace IntegerWitness
open PrimitiveExpressionExamples AbsentReference

/-- Freeze the admitted infinite-integer fixture at its value-3 state. -/
def stable : Trace (Fin 3) Object := {trace with deref _ := trace.deref 0}

-- [utest->req~behavioral-reference-atoms~1]
theorem stable_valid : Structural.Valid PrimitiveExpressionExamples.model stable := by
  refine ⟨?_, valid.root_live, valid.parent_live, ?_⟩
  · rcases valid.identities with ⟨a, b, c, d, e, f⟩
    exact ⟨a, b, c, d, e, f⟩
  intro _
  rcases valid.states 0 with ⟨a, b, c, d, e, f, g, h, i, j, l, p, q⟩
  exact ⟨a, b, c, d, e, f, g, h, i, j, l, p, q⟩

theorem stable_value (t : Nat) :
    Structural.eval PrimitiveExpressionExamples.model stable (.thisStep (.deref 1))
      (Environment.closed (.inl 1)) t = {integers.encode 3} :=
  current_target (Environment.closed (.inl 1)) 0 (Or.inl rfl)

-- [utest->req~behavioral-formula-denotation~1]
/-- Nonvacuous literal-3 success on an admitted trace with all mathematical
integers, for every next state; the literal-4 mutation fails on the same trace. -/
theorem literal_success_failure (t : Nat) :
    (equalValue 1 3).next.Satisfies stable
      (.primitives PrimitiveExpressionExamples.model stable integers) true
      (Environment.closed (.inl 1)) t ∧
    ¬ (equalValue 1 4).next.Satisfies stable
      (.primitives PrimitiveExpressionExamples.model stable integers) true
      (Environment.closed (.inl 1)) t := by
  have success := (next_equalValue_iff PrimitiveExpressionExamples.model stable integers
    (Environment.closed (.inl 1)) t 1 3).mpr (fun _ => stable_value (t + 1))
  refine ⟨success, fun failure => ?_⟩
  exact next_distinct_values PrimitiveExpressionExamples.model stable integers
    (Environment.closed (.inl 1)) t 1 3 4 (by decide)
    (Or.inr ⟨.inl 0, by rfl, by trivial⟩) ⟨success, failure⟩

end IntegerWitness

end Clafer.Behavioral.AbsentReferenceExamples
