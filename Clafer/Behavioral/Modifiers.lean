module

public import Clafer.Behavioral.Anchors
public import Clafer.Behavioral.StructuralSnapshot

/-! # Shallow lifetime-scoped modifiers

Behavioral §6.1–6.2 p.2:32 supplies final child-instance stability. T7/T8
adds repeated births, inherited references and reference-only modifiers.
The reviewed extension distinguishes per-head reference stability from stability
of the parent's target image. It is not a theorem about the pinned generator,
which emits per-head equality for both finalref and finaltarget.
-/

@[expose] public section
namespace Clafer.Behavioral.Modifiers
open ReferenceObservation Semantics
universe u
variable {C : Type} {U : Type u}

inductive Modifier where
  | initial | final | finalref | finaltarget
  deriving DecidableEq

-- [impl->req~behavioral-modifiers~1]
/-- Modifiers accumulate along inheritance; a refinement may add a modifier. -/
def Effective (f : MCS.Family C) (declared : C → Set Modifier) (d : C) (m : Modifier) : Prop :=
  ∃ a, Groups.Ancestor f d a ∧ m ∈ declared a

/-- Dynamic enum expansion adds finality to each literal; static enums do not
introduce a temporal modifier. Name/enum parsing remains a frontend obligation. -/
def enumLiteral (dynamic : Bool) : Set Modifier := if dynamic then {.final} else ∅

/-- Equality throughout one uninterrupted life, including its first state.
Separate lifetimes may have different observations. -/
def Stable {V : Type u} (live : Signal) (value : Nat → V) : Prop :=
  ∀ i j, i ≤ j → Lifetime.Through live i j → value i = value j

-- [proof->req~behavioral-modifiers~1]
theorem stable_iff_adjacent {V : Type u} (live : Signal) (value : Nat → V) :
    Stable live value ↔ ∀ t, live t → live (t + 1) → value t = value (t + 1) := by
  constructor
  · intro h t ht hn
    apply h t (t + 1) (by omega)
    intro k hk hkn
    have : k = t ∨ k = t + 1 := by omega
    rcases this with rfl | rfl
    · exact ht
    · exact hn
  · intro h i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; rfl
    | succ j hij ih =>
      intro life
      exact (ih (fun k hk hkj => life k hk (by omega))).trans
        (h j (life j hij (by omega)) (life (j + 1) (by omega) (by omega)))

theorem effective_own (f : MCS.Family C) (declared : C → Set Modifier) (d : C) (m : Modifier)
    (h : m ∈ declared d) : Effective f declared d m := ⟨d, .refl, h⟩

theorem effective_inherited (f : MCS.Family C) (declared : C → Set Modifier)
    {d a : C} {m : Modifier} (edge : f.super d = some a) (h : Effective f declared a m) :
    Effective f declared d m := by
  obtain ⟨b, path, hb⟩ := h
  exact ⟨b, path.head edge, hb⟩

theorem dynamic_enum_final : Modifier.final ∈ enumLiteral true := by simp [enumLiteral]
theorem static_enum_no_modifier : enumLiteral false = ∅ := rfl

variable {k : Nat} (m : Structural.Core k) (τ : Trace (Fin k) U)

def parents (d : Fin k) (t : Nat) : Set U :=
  {p | ∃ c, m.family.parent d = some c ∧ p ∈ (τ.raw m.toEffectiveCore t).head c}

-- [impl->req~behavioral-modifiers~1]
def Initial (d : Fin k) : Prop :=
  ∀ t p, p ∈ parents m τ d t → τ.Starts t p → (heads (Structural.current m τ t) d p).Nonempty

def FinalHeads (d : Fin k) : Prop :=
  ∀ p, Stable (fun t => p ∈ τ.live t) (fun t => heads (Structural.current m τ t) d p)

-- [impl->req~behavioral-modifiers~1]
def FinalRef (d : Fin k) : Prop :=
  ∀ x, m.toEffectiveCore.Ancestor (τ.identities.directType x) d →
    Stable (fun t => x ∈ τ.live t) (fun t => {y | (Structural.current m τ t).deref d x y})

def FinalTarget (d : Fin k) : Prop :=
  ∀ p, Stable (fun t => p ∈ τ.live t) (fun t => targets (Structural.current m τ t) d p)

def Final (d : Fin k) : Prop := FinalHeads m τ d ∧ FinalRef m τ d

-- [impl->req~behavioral-modifiers~1]
def Holds (declared : Fin k → Set Modifier) : Prop :=
  ∀ d, (Effective m.family declared d .initial → Initial m τ d) ∧
    (Effective m.family declared d .final → Final m τ d) ∧
    (Effective m.family declared d .finalref → FinalRef m τ d) ∧
    (Effective m.family declared d .finaltarget → FinalTarget m τ d)

/-- Resolved current views, with no free captured variable. The reference view
is attached to a head; heads/targets are attached to its actual parent. -/
inductive View (C : Type) where
  | heads (d : C) | reference (d : C) | targets (d : C)

def View.expression {n : Nat} : View C → SetExpr C n
  | .heads d => .thisStep (.child d)
  | .reference d => .thisStep (.deref d)
  | .targets d => .step (.deref d) (.thisStep (.child d))

def View.value (v : View (Fin k)) (p : U) (t : Nat) : Set U :=
  (v.expression : SetExpr (Fin k) 0).eval m.toEffectiveCore (Structural.observed m τ) (.closed p) t

def initialExpansion (d : C) : Formula (SetAtom C) (SetExpr C) 0 :=
  .initially (.atom (.inhabited (.thisStep (.child d))))

/-- Capture the complete current set, compare it at the next state only if
the attachment survives. This explicit guard uses the attachment's own life,
even though ordinary source X is bounded by its actual parent's life. -/
def stabilityExpansion (v : View C) : Formula (SetAtom C) (SetExpr C) 0 :=
  .letSet v.expression (.next (.implies (.atom (.inhabited .this))
    (.atom (.equal (.var 0) v.expression))))

-- [proof->req~behavioral-modifiers~1]
theorem View.expression_capture {n : Nat} (ρ : Environment U n) (S : Set U)
    {j : Nat} (core : EffectiveCore j) (tr : Trace (Fin j) U)
    (v' : View (Fin j)) (t : Nat) :
    v'.expression.eval core tr (ρ.push S) t = v'.expression.eval core tr ρ t := by
  cases v' <;> rfl

theorem heads_value (d : Fin k) (p : U) (t : Nat) :
    (View.heads d).value m τ p t = heads (Structural.current m τ t) d p := by
  ext x
  simp [View.value, View.expression, SetExpr.eval, Step.image, Step.relation,
    Environment.closed, heads, Structural.current]

theorem reference_value (h : Structural.Valid m τ) (d : Fin k) (x : U) (t : Nat) :
    (View.reference d).value m τ x t = {y | (Structural.current m τ t).deref d x y} := by
  ext y
  simp only [View.value, View.expression, SetExpr.eval, Step.image,
    Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_eq_left, Environment.closed]
  exact Structural.observed_deref m τ h t d x y

theorem targets_value (h : Structural.Valid m τ) (d : Fin k) (p : U) (t : Nat) :
    (View.targets d).value m τ p t = targets (Structural.current m τ t) d p := by
  ext y
  change (∃ x ∈ (View.heads d).value m τ p t,
    (Step.deref d).relation m.toEffectiveCore (Structural.observed m τ) t x y) ↔ _
  simp only [heads_value, Structural.observed_deref m τ h]
  rfl

theorem initial_agrees (d : Fin k) :
    (initialExpansion d).Attached τ (.sets m.toEffectiveCore (Structural.observed m τ))
      (parents m τ d) ↔ Initial m τ d := by
  have eq : ∀ p t, (SetExpr.thisStep (.child d) : SetExpr (Fin k) 0).eval
      m.toEffectiveCore (Structural.observed m τ) (.closed p) t =
      heads (Structural.current m τ t) d p := heads_value m τ d
  simp only [Formula.Attached, initialExpansion, Formula.denote, polarity, ↓reduceIte,
    Observation.sets, SetAtom.eval, eq, Initial]
  exact ⟨fun h t p hp birth => h t p hp birth.1 birth,
    fun h t p hp _ birth => h t p hp birth⟩

theorem stability_step_agrees (h : Structural.Valid m τ) (v : View (Fin k)) (p : U) (t : Nat) :
    (stabilityExpansion v).denote τ (.sets m.toEffectiveCore (Structural.observed m τ)) true (.closed p) t ↔
      (p ∈ τ.live (t + 1) → v.value m τ p t = v.value m τ p (t + 1)) := by
  have cap := View.expression_capture (.closed p) (v.value m τ p t)
    m.toEffectiveCore (Structural.observed m τ) v (t + 1)
  simp only [stabilityExpansion, Formula.denote, ↓reduceIte, Observation.sets,
    SetAtom.eval, Lifetime.next, polarity, SetExpr.eval, Environment.push_this,
    Environment.push_zero, Environment.closed]
  change (τ.ParentPresent p (t + 1) →
    ¬ ({x | x = p ∧ x ∈ τ.live (t + 1)} : Set U).Nonempty ∨
    v.value m τ p t = v.expression.eval m.toEffectiveCore (Structural.observed m τ)
      ((Environment.closed p).push (v.value m τ p t)) (t + 1)) ↔ _
  rw [cap]
  have present : ({x | x = p ∧ x ∈ τ.live (t + 1)} : Set U).Nonempty ↔ p ∈ τ.live (t + 1) :=
    ⟨fun ⟨_, hx, hl⟩ => hx ▸ hl, fun hp => ⟨p, rfl, hp⟩⟩
  rw [present]
  classical
  constructor
  · intro hh hp
    exact (hh (Structural.Valid.context_parent_present m τ h hp)).resolve_left (not_not_intro hp)
  · intro hh _
    by_cases hp : p ∈ τ.live (t + 1)
    · exact Or.inr (hh hp)
    · exact Or.inl hp

theorem stability_attached (h : Structural.Valid m τ) (v : View (Fin k)) :
    (stabilityExpansion v).Attached τ (.sets m.toEffectiveCore (Structural.observed m τ))
      (fun _ => Set.univ) ↔ ∀ p, Stable (fun t => p ∈ τ.live t) (v.value m τ p) := by
  simp only [Formula.Attached, Set.mem_univ, true_implies, stability_step_agrees m τ h,
    stable_iff_adjacent]
  exact ⟨fun hh p t hp hn => hh t p hp hn, fun hh t p hp hn => hh p t hp hn⟩

theorem finalHeads_agrees (h : Structural.Valid m τ) (d : Fin k) :
    (stabilityExpansion (.heads d)).Attached τ (.sets m.toEffectiveCore (Structural.observed m τ))
      (fun _ => Set.univ) ↔ FinalHeads m τ d := by
  rw [stability_attached m τ h]
  simp only [FinalHeads, Stable, heads_value]

-- [proof->req~behavioral-modifiers~1]
theorem finalTarget_agrees (h : Structural.Valid m τ) (d : Fin k) :
    (stabilityExpansion (.targets d)).Attached τ (.sets m.toEffectiveCore (Structural.observed m τ))
      (fun _ => Set.univ) ↔ FinalTarget m τ d := by
  rw [stability_attached m τ h]
  simp only [FinalTarget, Stable, targets_value m τ h]

-- [proof->req~behavioral-modifiers~1]
theorem finalRef_agrees (h : Structural.Valid m τ) (d : Fin k) :
    (stabilityExpansion (.reference d)).Attached τ (.sets m.toEffectiveCore (Structural.observed m τ))
      (fun t => (τ.raw m.toEffectiveCore t).head d) ↔ FinalRef m τ d := by
  simp only [Formula.Attached, stability_step_agrees m τ h, reference_value m τ h,
    FinalRef, stable_iff_adjacent]
  constructor
  · intro hh x ancestor t ht hn
    exact hh t x ⟨ht, ancestor⟩ ht hn
  · intro hh t x hx ht hn
    exact hh x hx.2 t ht hn

/-- Complete resolved constraint bundles, including the two parts of final.
The effective inherited annotation remains separate from source name resolution. -/
inductive Placement (C : Type) where
  | all | parents (d : C) | heads (d : C)

def Placement.contexts : Placement (Fin k) → Nat → Set U
  | .all => fun _ => Set.univ
  | .parents d => Modifiers.parents m τ d
  | .heads d => fun t => (τ.raw m.toEffectiveCore t).head d

def expand (d : C) : Modifier → List (Placement C × Formula (SetAtom C) (SetExpr C) 0)
  | .initial => [(.parents d, initialExpansion d)]
  | .final => [(.all, stabilityExpansion (.heads d)), (.heads d, stabilityExpansion (.reference d))]
  | .finalref => [(.heads d, stabilityExpansion (.reference d))]
  | .finaltarget => [(.all, stabilityExpansion (.targets d))]

def meaning (d : Fin k) : Modifier → Prop
  | .initial => Initial m τ d
  | .final => Final m τ d
  | .finalref => FinalRef m τ d
  | .finaltarget => FinalTarget m τ d

-- [proof->req~behavioral-modifiers~1]
theorem expand_agrees (h : Structural.Valid m τ) (d : Fin k) (modifier : Modifier) :
    (∀ item ∈ expand d modifier, item.2.Attached τ
      (.sets m.toEffectiveCore (Structural.observed m τ)) (item.1.contexts m τ)) ↔
      meaning m τ d modifier := by
  cases modifier <;> simp [expand, meaning, Placement.contexts, initial_agrees m τ,
    finalHeads_agrees m τ h, finalRef_agrees m τ h, finalTarget_agrees m τ h, Final]

/-- Modifier reduction to ordinary temporal core, with the S3 signed pass
before lifetime lowering. The total set adapter discharges partial definedness. -/
-- [proof->req~behavioral-modifiers~1]
theorem lower_agrees (h : Structural.Valid m τ) (d : Fin k) (modifier : Modifier) :
    meaning m τ d modifier ↔ ∀ item ∈ expand d modifier, ∀ t x,
      x ∈ item.1.contexts m τ t → x ∈ τ.live t →
      (item.2.normalize true).lower.eval τ (.sets m.toEffectiveCore (Structural.observed m τ)) (.closed x) t := by
  rw [← expand_agrees m τ h]
  simp only [Formula.attached_lower_agrees]

theorem final_assignments_adjacent (d : Fin k) (final : Final m τ d)
    (p : U) (t : Nat) (hp : p ∈ τ.live t) (hn : p ∈ τ.live (t + 1)) :
    assignments (Structural.current m τ t) d p = assignments (Structural.current m τ (t + 1)) d p := by
  have headsEq := (stable_iff_adjacent _ _).mp (final.1 p) t hp hn
  have refsEq (x : U) (hx : x ∈ heads (Structural.current m τ t) d p) :
      {y | (Structural.current m τ t).deref d x y} =
        {y | (Structural.current m τ (t + 1)).deref d x y} := by
    have hx' : x ∈ heads (Structural.current m τ (t + 1)) d p := headsEq ▸ hx
    exact (stable_iff_adjacent _ _).mp (final.2 x hx.2.1) t hx.1.2.1 hx'.1.2.1
  ext xy
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨headsEq ▸ hx, (Set.ext_iff.mp (refsEq xy.1 hx) xy.2).mp hy⟩
  · rintro ⟨hx, hy⟩
    have hx' := headsEq.symm ▸ hx
    exact ⟨hx', (Set.ext_iff.mp (refsEq xy.1 hx') xy.2).mpr hy⟩

/-- Finality fixes the target image as a consequence, not as a replacement
for the stronger head-and-reference requirements. -/
theorem final_implies_finalTarget (d : Fin k) (final : Final m τ d) : FinalTarget m τ d := by
  intro p
  rw [stable_iff_adjacent]
  intro t hp hn
  ext y
  change (∃ x, (x, y) ∈ assignments (Structural.current m τ t) d p) ↔
    ∃ x, (x, y) ∈ assignments (Structural.current m τ (t + 1)) d p
  rw [final_assignments_adjacent m τ d final p t hp hn]

end Clafer.Behavioral.Modifiers
