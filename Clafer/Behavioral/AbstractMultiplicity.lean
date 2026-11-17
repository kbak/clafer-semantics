module

public import Clafer.Semantics.AbstractMultiplicity
public import Clafer.Behavioral.StructuralSnapshot
public import Clafer.Behavioral.Properties

/-!
# The aggregate abstract multiplicity profile

Behavioral §5 Definitions 1, 3 and 5, extending the SoSyM §5.3.4
parentless boundary as accepted in #193. The historical `Structural.Core`
and its admission theorems retain their meaning. This profile adds authored
ranges and requires their independent static meaning at every state.
-/

@[expose] public section
namespace Clafer.Behavioral.AbstractMultiplicity
open Semantics DPGraph.Predicates

universe u

-- [impl->req~abstract-multiplicity~1]
/-- Authored intervals must be supplied by the frontend, never reconstructed
from optimizer-produced effective bounds (including unused-abstract zeroing). -/
structure Core (n : Nat) extends Structural.Core n where
  authoredMultiplicity : Fin n → Option Range

namespace Core
variable {n : Nat} (m : Core n)

/-- Abstract local bounds use authored/default values. Ordinary bounds, group
bounds, references, keys, identities and all parent/super edges are preserved. -/
def source : Structural.Core n :=
  let bounds (d : Fin n) :=
    if m.authoredAbstract d = true then
      Semantics.AbstractMultiplicity.range (m.authoredMultiplicity d)
    else m.family.multiplicity d
  { m.toCore with family := { m.family with multiplicity := bounds } }

-- [proof->req~abstract-multiplicity~1]
theorem abstract_range (d : Fin n) (h : m.authoredAbstract d = true) :
    m.source.family.multiplicity d = Semantics.AbstractMultiplicity.range (m.authoredMultiplicity d) := by
  simp [source, h]

theorem ordinary_range (d : Fin n) (h : m.authoredAbstract d = false) :
    m.source.family.multiplicity d = m.family.multiplicity d := by
  simp [source, h]

/-- Projection does not alter head closure, ownership or raw references. -/
theorem raw_eq {U : Type u} (τ : Trace (Fin n) U) (t : Nat) :
    τ.raw m.source.toEffectiveCore t = τ.raw m.toEffectiveCore t := rfl

/-- Replacing multiplicity metadata preserves nearest reference ownership. -/
theorem owner_iff (d o : Fin n) :
    InheritedReference.Owner m.source.family d o ↔ InheritedReference.Owner m.family d o := by
  constructor
  · intro h
    induction h with
    | declared ref => exact .declared ref
    | inherited basic super _ ih => exact .inherited basic super ih
  · intro h
    induction h with
    | declared ref => exact .declared ref
    | inherited basic super _ ih => exact .inherited basic super ih

theorem deref_iff {U : Type u} (s : Configuration (Fin n) U) (d : Fin n) (x y : U) :
    InheritedReference.deref m.source.family s d x y ↔
      InheritedReference.deref m.family s d x y := by
  simp only [InheritedReference.deref, owner_iff]

theorem keys_iff {U : Type u} (τ : Trace (Fin n) U) (t : Nat) :
    Structural.Keys m.source τ t ↔ Structural.Keys m.toCore τ t := by
  simp only [Structural.Keys, owner_iff, raw_eq, deref_iff]
  rfl

theorem groups_iff {U : Type u} (τ : Trace (Fin n) U) (t : Nat) :
    Structural.Groups m.source τ t ↔ Structural.Groups m.toCore τ t := Iff.rfl

end Core

variable {n : Nat} {U : Type u} (m : Core n) (τ : Trace (Fin n) U)

-- [impl->req~abstract-multiplicity~1]
def At (t : Nat) : Prop :=
  Semantics.AbstractMultiplicity.Holds m.family.parent m.authoredAbstract m.authoredMultiplicity
    (τ.raw m.source.toEffectiveCore t)

/-- Counts are state invariants, including states after time zero. -/
def Always : Prop := ∀ t, At m τ t

-- [impl->req~behavioral-structural-compatibility~1]
def Valid : Prop := Structural.Valid m.source τ ∧ Always m τ

def Admissible : Prop := m.source.WellFormed ∧ Valid m τ

-- [proof->req~abstract-multiplicity~1]
/-- The new independent clauses for nested abstracts are already precisely
those required by structural validity after source-bound projection. -/
theorem nested (valid : Structural.Valid m.source τ) (t : Nat) {d p : Fin n}
    (abstract : m.authoredAbstract d = true) (parent : m.family.parent d = some p) :
    Semantics.AbstractMultiplicity.PerParent (τ.raw m.source.toEffectiveCore t) d p
      (Semantics.AbstractMultiplicity.range (m.authoredMultiplicity d)) := by
  simpa only [Semantics.AbstractMultiplicity.PerParent, m.abstract_range d abstract] using
    (valid.states t).multiplicities d p parent

/-- The only additional structural obligation is the global count at parentless
abstracts. In particular no root containment map is needed to express it. -/
theorem valid_iff_global : Valid m τ ↔ Structural.Valid m.source τ ∧
    ∀ t d, m.authoredAbstract d = true → m.family.parent d = none →
      Semantics.AbstractMultiplicity.Global (τ.raw m.source.toEffectiveCore t) d
        (Semantics.AbstractMultiplicity.range (m.authoredMultiplicity d)) := by
  constructor
  · rintro ⟨hv, ha⟩
    refine ⟨hv, fun t d hd hp => ?_⟩
    have h := ha t d hd
    simpa only [hp] using h
  · rintro ⟨hv, hg⟩
    refine ⟨hv, fun t d hd => ?_⟩
    cases hp : m.family.parent d with
    | none => exact hg t d hd hp
    | some p => exact nested m τ hv t hd hp

-- [proof->req~behavioral-snapshot-bridge~1]
-- [proof->req~abstract-multiplicity~1]
/-- Restricting to the live carrier preserves the entire head, including all
realizations under different parents. -/
def headEquiv (h : Structural.Valid m.source τ) (t : Nat) (d : Fin n) :
    {x // x ∈ (Structural.snapshot m.source τ h t).head d} ≃
      {x // x ∈ (τ.raw m.source.toEffectiveCore t).head d} where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def fiberEquiv (h : Structural.Valid m.source τ) (t : Nat) (d : Fin n)
    (p : τ.Live t) :
    {x // (Structural.snapshot m.source τ h t).contains d p x} ≃
      {x // (τ.raw m.source.toEffectiveCore t).contains d p.val x} where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1.2.1⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem snapshot_iff (h : Structural.Valid m.source τ) (t : Nat) :
    Semantics.AbstractMultiplicity.Holds m.family.parent m.authoredAbstract m.authoredMultiplicity
      (Structural.snapshot m.source τ h t) ↔ At m τ t := by
  apply forall_congr'
  intro d
  apply imp_congr_right
  intro _
  cases hp : m.family.parent d with
  | none => exact inRange_iff _ (headEquiv m τ h t d)
  | some p =>
    constructor
    · intro hs x hx
      exact (inRange_iff _ (fiberEquiv m τ h t d ⟨x, hx.1⟩)).mp
        (hs ⟨x, hx.1⟩ hx)
    · intro hs x hx
      exact (inRange_iff _ (fiberEquiv m τ h t d x)).mpr (hs x.val hx)

/-- Static agreement requires exact head/fiber correspondence. It does not
follow from a finite solver scope or from checking only the initial state. -/
theorem constant_iff (s : Configuration (Fin n) U)
    (heads : ∀ t d, (τ.raw m.source.toEffectiveCore t).head d = s.head d)
    (parents : ∀ t d, (τ.raw m.source.toEffectiveCore t).contains d = s.contains d) :
    Always m τ ↔ Semantics.AbstractMultiplicity.Holds m.family.parent m.authoredAbstract m.authoredMultiplicity s := by
  have atTime (t : Nat) : At m τ t ↔
      Semantics.AbstractMultiplicity.Holds m.family.parent m.authoredAbstract m.authoredMultiplicity s := by
    unfold At Semantics.AbstractMultiplicity.Holds Semantics.AbstractMultiplicity.Global Semantics.AbstractMultiplicity.PerParent
    simp only [heads, parents]
  exact ⟨fun h => (atTime 0).mp (h 0), fun h t => (atTime t).mpr h⟩

-- [impl->req~abstract-multiplicity~1]
/-- Full source composition keeps all existing modifier/constraint obligations
and conjoins aggregate counts to the same source model. -/
def model {A D : Nat → Type} (modifiers : Fin n → Set Modifiers.Modifier)
    (O : Trace (Fin n) U → PartialObservation A D U)
    (constraints : Set (Properties.Constraint (Fin n) A D U)) :
    Properties.Model (Fin n) A D U :=
  { Properties.Model.behavioral m.source modifiers O constraints with
    admissible := {σ | σ ∈ (Properties.Model.behavioral m.source modifiers O constraints).admissible ∧
      Always m σ} }

-- [proof->req~abstract-multiplicity~1]
theorem model_satisfies_iff {A D : Nat → Type}
    (modifiers : Fin n → Set Modifiers.Modifier)
    (O : Trace (Fin n) U → PartialObservation A D U)
    (constraints : Set (Properties.Constraint (Fin n) A D U)) :
    (model m modifiers O constraints).Satisfies τ ↔
      (Properties.Model.behavioral m.source modifiers O constraints).Satisfies τ ∧ Always m τ := by
  simp only [model, Properties.Model.Satisfies]
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩, fun ⟨⟨a, c⟩, b⟩ => ⟨⟨a, b⟩, c⟩⟩

end Clafer.Behavioral.AbstractMultiplicity
