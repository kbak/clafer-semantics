module

public import Clafer.Semantics.Structural

/-!
# Shared identities and infinite traces

Juodisius et al., §5 Definitions 1–3 and 5 (pp. 2:23–28), with pinned
0.5.7 errata T1, T7 and T11. The synthetic root is permanent; direct types
and actual parents are static, including across absence and reappearance.
These are source data, independent of temporal formulas, compiler IR and lassos.
-/

@[expose] public section
namespace Clafer.Behavioral
open Semantics

universe u

-- [impl->req~behavioral-identities~1]
/-- Reference occurrences are objects in `U`, not their dereferenced targets. -/
structure Identities (C : Type) (U : Type u) where
  root : U
  directType : U → C
  parent : U → Option U

namespace Identities
variable {n : Nat} {U : Type u}

/-- Abstract declaration roles do not determine an object's actual parent.
A top-level concrete object's declared parent is the synthetic root class.
Unused pool identities carry the same static information as used identities. -/
structure Valid (m : EffectiveCore n) (ids : Identities (Fin n) U) : Prop where
  root_type : ids.directType ids.root = m.family.root
  root_only : ∀ x, ids.directType x = m.family.root → x = ids.root
  concrete : ∀ x, m.family.isAbstract (ids.directType x) = false
  root_parent : ids.parent ids.root = none
  parent_exists : ∀ x, x ≠ ids.root → ∃ p, ids.parent x = some p
  parent_typed : ∀ x p, ids.parent x = some p →
    ∃ c, m.family.parent (ids.directType x) = some c ∧
      m.Ancestor (ids.directType p) c

end Identities

-- [impl->req~behavioral-traces~1]
structure Trace (C : Type) (U : Type u) where
  identities : Identities C U
  live : Nat → Set U
  deref : Nat → C → U → U → Prop

namespace Trace
variable {C : Type} {U : Type u} (τ : Trace C U)

/-- Each state has its own live carrier; `Subtype.val` embeds it in the pool. -/
def Live (t : Nat) := {x : U // x ∈ τ.live t}

def embedding (t : Nat) : τ.Live t ↪ U := ⟨Subtype.val, Subtype.val_injective⟩

-- [impl->req~behavioral-identities~1]
/-- Actual ownership at a time, including parents of top-level objects. -/
def ParentAt (t : Nat) (p x : U) : Prop :=
  p ∈ τ.live t ∧ x ∈ τ.live t ∧ τ.identities.parent x = some p

-- [proof->req~behavioral-identities~1]
/-- No adjacency premise: this also covers two different lifetimes of `x`. -/
theorem parent_stable {i j : Nat} {p q x : U}
    (hi : τ.ParentAt i p x) (hj : τ.ParentAt j q x) : p = q :=
  Option.some.inj (hi.2.2.symm.trans hj.2.2)

/-- Distinct snapshot memberships of one pool identity retain its direct type. -/
theorem type_stable {i j : Nat} (x : τ.Live i) (y : τ.Live j)
    (h : τ.embedding i x = τ.embedding j y) :
    τ.identities.directType x.val = τ.identities.directType y.val :=
  congrArg τ.identities.directType h

-- [impl->req~behavioral-traces~1]
/-- T7: time zero is a birth when live; every absent-to-live edge is another. -/
def Starts (t : Nat) (x : U) : Prop :=
  x ∈ τ.live t ∧ (t = 0 ∨ ∃ k, t = k + 1 ∧ x ∉ τ.live k)

/-- The last live state, not the first absent state. Permanent lives have no end. -/
def Ends (t : Nat) (x : U) : Prop := x ∈ τ.live t ∧ x ∉ τ.live (t + 1)

-- [proof->req~behavioral-traces~1]
@[simp] theorem starts_zero (x : U) : τ.Starts 0 x ↔ x ∈ τ.live 0 := by
  simp [Starts]

@[simp] theorem starts_succ (t : Nat) (x : U) :
    τ.Starts (t + 1) x ↔ x ∈ τ.live (t + 1) ∧ x ∉ τ.live t := by
  simp [Starts]

theorem end_then_start {t : Nat} {x : U} (h : τ.Ends t x)
    (hx : x ∈ τ.live (t + 2)) : τ.Starts (t + 2) x :=
  (τ.starts_succ (t + 1) x).mpr ⟨hx, h.2⟩

variable {n : Nat} (m : EffectiveCore n) (σ : Trace (Fin n) U)

-- [impl->req~behavioral-snapshot-bridge~1]
/-- A presentation on the whole identity pool. Its `Rooted` condition generally
fails on unused/absent identities; only its live restriction is a snapshot.
Containment preserves head occurrences. Dereferences are not silently filtered:
a dangling endpoint must fail typedness in `StateValid`. -/
def raw (t : Nat) : Configuration (Fin n) U where
  root := σ.identities.root
  head d := {x | x ∈ σ.live t ∧ m.Ancestor (σ.identities.directType x) d}
  contains d p x := σ.ParentAt t p x ∧
    m.Ancestor (σ.identities.directType x) d ∧ m.family.parent d ≠ none
  deref := σ.deref t

/-- Structural clauses on the shared carrier, with root coverage restricted to
live objects. The clauses reuse the independent structural meaning, not a checker. -/
structure StateValid (t : Nat) : Prop where
  typed : (σ.raw m t).Typed m
  root_head : ∀ x, x ∈ (σ.raw m t).head m.family.root ↔ x = σ.identities.root
  root_separate : ∀ d, d ≠ m.family.root →
    σ.identities.root ∉ (σ.raw m t).head d
  inherits : (σ.raw m t).Inherits m
  abstracts : (σ.raw m t).Abstracts m
  parents : (σ.raw m t).Parents m
  references : (σ.raw m t).References m
  keys : (σ.raw m t).Keys m
  multiplicities : (σ.raw m t).Multiplicities m
  groups : (σ.raw m t).Groups m
  disjoint : (σ.raw m t).DeclarationDisjoint m

-- [impl->req~behavioral-traces~1]
/-- No no-reappearance axiom and no temporal formulas. Global parent presence
is required independently of the snapshot clauses and of declaration views. -/
structure Valid : Prop where
  identities : σ.identities.Valid m
  root_live : ∀ t, σ.identities.root ∈ σ.live t
  parent_live : ∀ t x p, x ∈ σ.live t → σ.identities.parent x = some p → p ∈ σ.live t
  states : ∀ t, σ.StateValid m t

-- [proof->req~behavioral-traces~1]
theorem root_starts (h : σ.Valid m) (t : Nat) :
    σ.Starts t σ.identities.root ↔ t = 0 := by
  constructor
  · rintro ⟨_, ht | ⟨k, _, hk⟩⟩
    · exact ht
    · exact (hk (h.root_live k)).elim
  · rintro rfl
    exact (σ.starts_zero _).mpr (h.root_live 0)

theorem root_never_ends (h : σ.Valid m) (t : Nat) : ¬ σ.Ends t σ.identities.root :=
  fun hx => hx.2 (h.root_live (t + 1))

/-- The accepted common structural fragment, without temporal modifiers. -/
def Admissible : Prop := m.WellFormed ∧ m.Supported ∧ σ.Valid m

-- [proof->req~behavioral-identities~1]
theorem top_level_parent (h : σ.Valid m) {t : Nat} {x p : U}
    (hp : σ.ParentAt t p x)
    (htop : m.family.parent (σ.identities.directType x) = some m.family.root) :
    p = σ.identities.root := by
  obtain ⟨c, hc, hpc⟩ := h.identities.parent_typed x p hp.2.2
  have he : c = m.family.root := Option.some.inj (hc.symm.trans htop)
  subst c
  exact ((h.states t).root_head p).mp ⟨hp.1, hpc⟩

end Trace
end Clafer.Behavioral
