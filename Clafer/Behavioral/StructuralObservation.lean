module

public import Clafer.Behavioral.StructuralCompatibility
public import Clafer.Behavioral.Environment

/-! # Current observations of richer structural states

S6/S7/S9 and T8, with adopted D1. Resolve an inherited reference once, then
use the existing identity-capturing set evaluator on its current relation.
Raw state admission precedes observation; filtering cannot repair an invalid state.
-/

@[expose] public section
namespace Clafer.Behavioral
open Semantics
universe u

namespace InheritedReference

-- [proof->req~behavioral-reference-atoms~1]
theorem owner_exists_iff {C : Type} (f : MCS.Family C) (d : C) :
    (∃ o, Owner f d o) ↔ ∃ a, Groups.Ancestor f d a ∧ f.reference a ≠ .basic := by
  constructor
  · rintro ⟨o, h⟩; exact ⟨o, h.ancestor, h.has_reference⟩
  · rintro ⟨a, path, ref⟩
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨a, .declared ref⟩
    | @head d s edge _ ih =>
      by_cases basic : f.reference d = .basic
      · obtain ⟨o, ho⟩ := ih
        exact ⟨o, .inherited basic edge ho⟩
      · exact ⟨d, .declared basic⟩

end InheritedReference

namespace Structural
variable {n : Nat} {U : Type u} (m : Core n) (τ : Trace (Fin n) U)

-- [impl->req~behavioral-reference-atoms~1]
/-- An observation adapter, not a replacement validity predicate. It preserves
the identity pool, live sets and actual parents exactly. -/
def observed : Trace (Fin n) U where
  identities := τ.identities
  live := τ.live
  deref t := InheritedReference.deref m.family (τ.raw m.toEffectiveCore t)

@[simp] theorem observed_head (t : Nat) (d : Fin n) :
    ((observed m τ).raw m.toEffectiveCore t).head d = (τ.raw m.toEffectiveCore t).head d := rfl

@[simp] theorem observed_contains (t : Nat) (d : Fin n) :
    ((observed m τ).raw m.toEffectiveCore t).contains d =
      (τ.raw m.toEffectiveCore t).contains d := rfl

-- [proof->req~behavioral-reference-atoms~1]
theorem observed_deref (h : Valid m τ) (t : Nat) (d : Fin n) (x y : U) :
    (Step.deref d).relation m.toEffectiveCore (observed m τ) t x y ↔
      InheritedReference.deref m.family (τ.raw m.toEffectiveCore t) d x y := by
  constructor
  · exact fun h => h.2.2
  · intro link
    exact ⟨link.choose_spec.2.1.1, h.target_live link, link⟩

noncomputable def eval {k : Nat} (e : SetExpr (Fin n) k) (ρ : Environment U k) (t : Nat) : Set U :=
  e.eval m.toEffectiveCore (observed m τ) ρ t

theorem captured_deref (h : Valid m τ) {k : Nat} (ρ : Environment U k)
    (x y : U) (d : Fin n) (t : Nat) :
    y ∈ eval m τ (.step (.deref d) (.var 0)) (ρ.push {x}) t ↔
      InheritedReference.deref m.family (τ.raw m.toEffectiveCore t) d x y := by
  change y ∈ (SetExpr.step (.deref d) (.var 0)).eval _ _ _ _ ↔ _
  rw [SetExpr.captured_deref]
  exact observed_deref m τ h t d x y

theorem direct_parent {k : Nat} (ρ : Environment U k) (p : U) (t : Nat) :
    p ∈ eval m τ (.thisStep .parent) ρ t ↔
      τ.identities.parent ρ.this = some p ∧ p ∈ τ.live t :=
  SetExpr.direct_parent _ _ _ _ _

theorem this_absent {k : Nat} (ρ : Environment U k) (t : Nat)
    (absent : ρ.this ∉ τ.live t) : eval m τ .this ρ t = ∅ :=
  SetExpr.this_absent _ _ _ _ absent

theorem absent_deref {t : Nat} {d : Fin n} {x y : U} (absent : x ∉ τ.live t) :
    ¬ (observed m τ).deref t d x y := by
  rintro ⟨_, _, hx, _⟩
  exact absent hx.1

-- [proof->req~behavioral-reference-atoms~1]
/-- Only the captured head collection must be finite. Neither the current
class extent nor the primitive universe is assumed finite. -/
theorem finite_captured_deref (h : Valid m τ) {k : Nat} (ρ : Environment U k)
    {S : Set U} (finite : S.Finite) (d : Fin n) (t : Nat) :
    (eval m τ (.step (.deref d) (.var 0)) (ρ.push S) t).Finite := by
  classical
  apply Set.Finite.subset (finite.biUnion (t := fun x =>
    {y | InheritedReference.deref m.family (τ.raw m.toEffectiveCore t) d x y}) (fun x _ => ?_))
  · intro y hy
    obtain ⟨x, hx, link⟩ := hy
    exact Set.mem_iUnion₂.mpr ⟨x, hx, (observed_deref m τ h t d x y).mp link⟩
  · apply Set.Subsingleton.finite
    intro y hy z hz
    exact h.refined_reference_agrees hy hz

theorem captured_target_typed (h : Valid m τ) {k : Nat} (ρ : Environment U k)
    (S : Set U) {d o c : Fin n} (owner : InheritedReference.Owner m.family d o)
    (target : (m.family.reference o).target = some c) (t : Nat) :
    eval m τ (.step (.deref d) (.var 0)) (ρ.push S) t ⊆
      (τ.raw m.toEffectiveCore t).head c := by
  rintro y ⟨x, _, link⟩
  exact h.target_typed owner target ((observed_deref m τ h t d x y).mp link)

/-- The complete observed relation, including its target view, agrees on the
common static fragment. No new relation is allocated for inherited heads. -/
theorem observed_common {m : EffectiveCore n} (support : m.Supported)
    (h : τ.Valid m) : observed (Core.ofEffective m) τ = τ := by
  have links : ∀ t d x y,
      InheritedReference.deref m.family (τ.raw m t) d x y ↔ τ.deref t d x y := by
    intro t d x y
    constructor
    · rintro ⟨o, owner, _, link⟩
      have he := Common.owner_eq support owner
      exact he ▸ link
    · intro link
      obtain ⟨hx, c, hc, _⟩ := (h.states t).typed.2 d x y link
      have ref : m.family.reference d ≠ .basic := by
        intro he; simp [he, MCS.ReferenceTo.target] at hc
      exact ⟨d, .declared ref, hx, link⟩
  cases τ with
  | mk ids live deref =>
    dsimp only [observed]
    congr 1
    funext t d x y
    exact propext (links t d x y)

theorem eval_common {m : EffectiveCore n} (support : m.Supported) (h : τ.Valid m)
    {k : Nat} (e : SetExpr (Fin n) k) (ρ : Environment U k) (t : Nat) :
    eval (Core.ofEffective m) τ e ρ t = e.eval m τ ρ t := by
  unfold eval
  rw [observed_common τ support h]
  rfl

end Structural
end Clafer.Behavioral
