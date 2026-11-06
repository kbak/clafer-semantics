module

public import Clafer.Behavioral.Trace

/-!
# Time-spanning environments and current observations

Behavioral paper §5 pp. 2:26–28, with the explicitly adopted D1 departure:
capture identities/sets, then navigate current relations. Standalone `this`
is live-filtered; direct `this` navigation starts at the retained identity.
No static `Expr.not`, primitive extraction or partial arithmetic is reused.
-/

@[expose] public section
namespace Clafer.Behavioral
universe u

-- [impl->req~behavioral-environments~1]
/-- Lexically indexed captured values. Quantifiers push singletons; let pushes
the entire evaluated set. Neither operation changes the attachment identity. -/
structure Environment (U : Type u) (n : Nat) where
  this : U
  lookup : Fin n → Set U

namespace Environment
def closed {U : Type u} (c : U) : Environment U 0 := ⟨c, Fin.elim0⟩
def push {U : Type u} {n} (ρ : Environment U n) (S : Set U) : Environment U (n + 1) :=
  ⟨ρ.this, Fin.cases S ρ.lookup⟩

-- [proof->req~behavioral-environments~1]
@[simp] theorem push_this {U : Type u} {n} (ρ : Environment U n) (S : Set U) :
    (ρ.push S).this = ρ.this := rfl
@[simp] theorem push_zero {U : Type u} {n} (ρ : Environment U n) (S : Set U) :
    (ρ.push S).lookup 0 = S := rfl
@[simp] theorem push_succ {U : Type u} {n} (ρ : Environment U n) (S : Set U) (v : Fin n) :
    (ρ.push S).lookup v.succ = ρ.lookup v := rfl
end Environment

namespace Trace
-- [impl->req~behavioral-formula-denotation~1]
/-- Fixed *actual* parent of the original context. Quantification does not
reattach the obligation. The synthetic-root context has unbounded lifetime. -/
def ParentPresent {C : Type} {U : Type u} (τ : Trace C U) (c : U) (t : Nat) : Prop :=
  c = τ.identities.root ∨ ∃ p, τ.identities.parent c = some p ∧ p ∈ τ.live t

-- [proof->req~behavioral-formula-denotation~1]
@[simp] theorem parentPresent_root {C : Type} {U : Type u} (τ : Trace C U) (t : Nat) :
    τ.ParentPresent τ.identities.root t := Or.inl rfl

theorem parentPresent_iff {C : Type} {U : Type u} (τ : Trace C U)
    {c p : U} (hc : c ≠ τ.identities.root) (hp : τ.identities.parent c = some p) (t : Nat) :
    τ.ParentPresent c t ↔ p ∈ τ.live t := by
  simp [ParentPresent, hc, hp]

theorem context_parent_present {k : Nat} {U : Type u} {m : Semantics.EffectiveCore k}
    {τ : Trace (Fin k) U} (h : τ.Valid m) {t : Nat} {c : U} (hc : c ∈ τ.live t) :
    τ.ParentPresent c t := by
  by_cases hr : c = τ.identities.root
  · exact Or.inl hr
  · obtain ⟨p, hp⟩ := h.identities.parent_exists c hr
    exact Or.inr ⟨p, hp, h.parent_live t c p hc hp⟩
end Trace

-- [impl->req~behavioral-environments~1]
inductive Step (C : Type) where
  | parent
  | child (declaration : C)
  | deref (declaration : C)

inductive SetExpr (C : Type) (n : Nat) where
  | empty
  | this
  | root
  | var (index : Fin n)
  | extent (declaration : C)
  | union (a b : SetExpr C n)
  | inter (a b : SetExpr C n)
  | diff (a b : SetExpr C n)
  | step (s : Step C) (a : SetExpr C n)
  /-- Resolved direct navigation, distinct from observing standalone `this`. -/
  | thisStep (s : Step C)

namespace Step
def relation {k : Nat} {U : Type u} (m : Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) (t : Nat) : Step (Fin k) → U → U → Prop
  | .parent, x, p => τ.identities.parent x = some p ∧ p ∈ τ.live t
  | .child d, p, x => (τ.raw m t).contains d p x
  | .deref d, x, y => x ∈ τ.live t ∧ y ∈ τ.live t ∧ τ.deref t d x y

def image {k : Nat} {U : Type u} (m : Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) (t : Nat) (s : Step (Fin k)) (S : Set U) : Set U :=
  {y | ∃ x ∈ S, s.relation m τ t x y}
end Step

namespace SetExpr
noncomputable def eval {k n : Nat} {U : Type u} (m : Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) (ρ : Environment U n) (t : Nat) : SetExpr (Fin k) n → Set U
  | .empty => ∅
  | .this => {x | x = ρ.this ∧ x ∈ τ.live t}
  | .root => {τ.identities.root}
  | .var v => ρ.lookup v
  | .extent d => (τ.raw m t).head d
  | .union a b => a.eval m τ ρ t ∪ b.eval m τ ρ t
  | .inter a b => a.eval m τ ρ t ∩ b.eval m τ ρ t
  | .diff a b => a.eval m τ ρ t \ b.eval m τ ρ t
  | .step s a => s.image m τ t (a.eval m τ ρ t)
  | .thisStep s => s.image m τ t {ρ.this}

-- [proof->req~behavioral-environments~1]
theorem this_absent {k n : Nat} {U : Type u} (m : Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) (ρ : Environment U n) (t : Nat) (h : ρ.this ∉ τ.live t) :
    (SetExpr.this : SetExpr (Fin k) n).eval m τ ρ t = ∅ := by
  ext x
  simp only [eval, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl
  exact h

theorem this_live {k n : Nat} {U : Type u} (m : Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) (ρ : Environment U n) (t : Nat) (h : ρ.this ∈ τ.live t) :
    (SetExpr.this : SetExpr (Fin k) n).eval m τ ρ t = {ρ.this} := by
  ext x
  simp only [eval, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact ⟨And.left, fun hx => ⟨hx, hx ▸ h⟩⟩

theorem captured_set {k n : Nat} {U : Type u} (m : Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) (ρ : Environment U n) (S : Set U) (t : Nat) :
    (SetExpr.var 0).eval m τ (ρ.push S) t = S := rfl

/-- Source absence is intentionally not a premise of parent navigation. -/
theorem direct_parent {k n : Nat} {U : Type u} (m : Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) (ρ : Environment U n) (t : Nat) (p : U) :
    p ∈ (SetExpr.thisStep .parent).eval m τ ρ t ↔
      τ.identities.parent ρ.this = some p ∧ p ∈ τ.live t := by
  simp [eval, Step.image, Step.relation]

theorem captured_deref {k n : Nat} {U : Type u} (m : Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) (ρ : Environment U n) (x y : U) (d : Fin k) (t : Nat) :
    y ∈ (SetExpr.step (.deref d) (.var 0)).eval m τ (ρ.push {x}) t ↔
      x ∈ τ.live t ∧ y ∈ τ.live t ∧ τ.deref t d x y := by
  simp [eval, Step.image, Step.relation]
end SetExpr

-- [impl->req~behavioral-environments~1]
/-- Total set observations only. Partial numeric/primitive atoms require their
separate S4/D3 contract; they are not mapped to false when undefined. -/
inductive SetAtom (C : Type) (n : Nat) where
  | inhabited (a : SetExpr C n)
  | equal (a b : SetExpr C n)
  | subset (a b : SetExpr C n)

def SetAtom.eval {k n : Nat} {U : Type u} (m : Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) (ρ : Environment U n) (t : Nat) : SetAtom (Fin k) n → Prop
  | .inhabited a => (a.eval m τ ρ t).Nonempty
  | .equal a b => a.eval m τ ρ t = b.eval m τ ρ t
  | .subset a b => a.eval m τ ρ t ⊆ b.eval m τ ρ t
end Clafer.Behavioral
