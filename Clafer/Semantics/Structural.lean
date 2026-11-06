module

public import Clafer.Semantics.Inheritance
public import DPGraph.Predicates.Interpretation
public import DPGraph.Predicates.FunctionalKey

/-!
[impl->req~clafer-structural-satisfaction~1]
[proof->req~clafer-structural-satisfaction~1]
-/

/-!
# Whole-model structural satisfaction

SoSyM §5.3–5.5, §6.1–6.2, Table 3/A.1 and Appendix 5, with Q1/Q8.
This relation is over mathematical sets and relations, independently of the
finite checker. Objects in two classes are the same ambient object. Ordinary
maps have relation-tuple links; composite reference maps retain both links.
-/

@[expose] public section
namespace Clafer.Semantics
open DPGraph DPGraph.Predicates MCS

universe u

/-- A relational presentation; no finiteness, functionality, coverage or bounds
are built into the data. Those are independently stated semantic obligations. -/
structure Configuration (C : Type) (U : Type u) where
  root : U
  head : C → Set U
  contains : C → U → U → Prop
  deref : C → U → U → Prop

namespace Configuration
variable {n : Nat} {U : Type u} (m : EffectiveCore n) (s : Configuration (Fin n) U)

def Typed : Prop :=
  (∀ d p x, s.contains d p x →
    (x ∈ s.head d) ∧ ∃ c, m.family.parent d = some c ∧ (p ∈ s.head c)) ∧
  (∀ d x t, s.deref d x t →
    (x ∈ s.head d) ∧ ∃ c, (m.family.reference d).target = some c ∧ (t ∈ s.head c))

def Rooted : Prop :=
  (∀ x, (x ∈ s.head m.family.root) ↔ x = s.root) ∧
  (∀ d, d ≠ m.family.root → ¬ (s.root ∈ s.head d)) ∧
  (∀ x, x = s.root ∨ ∃ d, d ≠ m.family.root ∧ (x ∈ s.head d))

def Inherits : Prop :=
  ∀ d c, m.family.super d = some c → ∀ x, (x ∈ s.head d) → (x ∈ s.head c)

/-- Maintainer-adopted #87 clarification of §5.5/Appendix 5: shared head
membership requires comparability through super edges. Equality is reflexive;
containment, names and reference targets do not create ancestry. Context views
are restrictions of these declarations, not additional heads. -/
def DeclarationDisjoint : Prop :=
  ∀ d e x, x ∈ s.head d → x ∈ s.head e → m.Ancestor d e ∨ m.Ancestor e d

/-- Pairwise disjointness of inheritance-incomparable declaration extents. -/
theorem declarationDisjoint_iff : s.DeclarationDisjoint m ↔
    ∀ d e, ¬ m.Ancestor d e → ¬ m.Ancestor e d →
      ∀ x, ¬ (x ∈ s.head d ∧ x ∈ s.head e) := by
  constructor
  · intro h d e hd he x hx
    exact (h d e x hx.1 hx.2).elim hd he
  · intro h d e x hd he
    by_cases hde : m.Ancestor d e
    · exact Or.inl hde
    · apply Or.inr
      by_contra hed
      exact h d e hde hed x ⟨hd, he⟩

/-- The direct subtype family covers its abstract head, and distinct images
are disjoint in that common target (accepted Q8), including the empty family. -/
def Abstracts : Prop :=
  ∀ d, m.family.isAbstract d = true →
    (∀ x, (x ∈ s.head d) → ∃ c, m.family.super c = some d ∧ (x ∈ s.head c)) ∧
    (∀ c e, m.family.super c = some d → m.family.super e = some d → c ≠ e →
      ∀ x, ¬ ((x ∈ s.head c) ∧ (x ∈ s.head e)))

def Parents : Prop :=
  ∀ d c, m.family.parent d = some c → ∀ x, (x ∈ s.head d) →
    ∃! p, s.contains d p x

def References : Prop :=
  ∀ d c, (m.family.reference d).target = some c → ∀ x, (x ∈ s.head d) →
    ∃! t, s.deref d x t

/-- Uniqueness of the parent/target pair is imposed only on set heads. -/
def Keys : Prop :=
  ∀ d, (m.family.reference d).kind = .referenceSet →
    ∀ p t x y, s.contains d p x → s.deref d x t →
      s.contains d p y → s.deref d y t → x = y

def Multiplicities : Prop :=
  ∀ d c, m.family.parent d = some c → ∀ p, (p ∈ s.head c) →
    InRange (m.family.multiplicity d) {x : U // s.contains d p x}

/-- A union, not a sum over declarations or a set of dereferenced targets. -/
def Child (d : Fin n) (p x : U) : Prop :=
  ∃ c, m.family.parent c = some d ∧ s.contains c p x

def Groups : Prop :=
  ∀ d, m.family.isAbstract d = false → ∀ p, (p ∈ s.head d) →
    InRange (m.group d) {x : U // s.Child m d p x}

/-- Reachability follows concrete containment, never reference targets. -/
def Reaches (x : U) : Prop :=
  Relation.ReflTransGen (fun p x => ∃ d, s.contains d p x) s.root x

end Configuration

/-- Global structural meaning of the guarded fragment. `Typed` is separated
for raw-input diagnostics; this mathematical relation includes it as an
obligation. Root reachability is derived from these clauses and core validity. -/
def StructuralSatisfies {n : Nat} {U : Type u} (m : EffectiveCore n)
    (s : Configuration (Fin n) U) : Prop :=
  s.Typed m ∧ s.Rooted m ∧ s.Inherits m ∧ s.Abstracts m ∧
  s.Parents m ∧ s.References m ∧ s.Keys m ∧ s.Multiplicities m ∧ s.Groups m ∧ s.DeclarationDisjoint m

end Clafer.Semantics
