module

public import Clafer.Semantics.Structural
public import DPGraph.Predicates.Finite

/-!
# Authored aggregate multiplicity on abstract declarations

SoSyM §5.2, §5.3.4 and §5.5; accepted extension #193. A parentless
abstract counts its complete head, including nested realizations under different
actual parents. A parented abstract reuses the ordinary containment fiber.
No root-parent map or reference key is introduced. Bounds are source annotations,
not optimized effective bounds or finite solver scopes.
-/

@[expose] public section
namespace Clafer.Semantics.AbstractMultiplicity
open DPGraph.Predicates
universe u
variable {C : Type} {U : Type u}

-- [impl->req~abstract-multiplicity~1]
/-- Omission has the unrestricted abstract default, regardless of optimizer data. -/
def range (authored : Option Range) : Range := authored.getD unrestricted

/-- Count identities in the full inherited view, never reference targets or a
sum of subtype cardinalities. `InRange` also has meaning on infinite extents. -/
def Global (s : Configuration C U) (d : C) (r : Range) : Prop :=
  InRange r {x // x ∈ s.head d}

/-- One obligation per live member of the declared parent's head. -/
def PerParent (s : Configuration C U) (d parent : C) (r : Range) : Prop :=
  ∀ p ∈ s.head parent, InRange r {x // s.contains d p x}

/-- The independent static count obligation. Structural validity separately
establishes complete inherited heads, typed fibers and actual ownership. -/
def Holds (parent : C → Option C) (abstract : C → Bool)
    (authored : C → Option Range) (s : Configuration C U) : Prop :=
  ∀ d, abstract d = true → match parent d with
    | none => Global s d (range (authored d))
    | some p => PerParent s d p (range (authored d))

-- [proof->req~abstract-multiplicity~1]
theorem unrestricted_holds (A : Type u) : InRange unrestricted A :=
  ⟨⟨⟨Fin.elim0, fun i => Fin.elim0 i⟩⟩, trivial⟩

theorem omitted (parent : C → Option C) (abstract : C → Bool)
    (s : Configuration C U) : Holds parent abstract (fun _ => none) s := by
  intro d _
  cases parent d with
  | none => exact unrestricted_holds _
  | some p => exact fun _ _ => unrestricted_holds _

/-- A finite representation of this head alone suffices. It need not enumerate
all objects, other declarations or even all live objects. -/
theorem global_fin_iff (s : Configuration C U) (d : C) (r : Range) {k : Nat}
    (e : {x // x ∈ s.head d} ≃ Fin k) :
    Global s d r ↔ CountInRange r k := by
  rw [Global, inRange_iff r e, inRange_card]
  simp

theorem global_card (s : Configuration C U) (d : C) (r : Range)
    [Fintype {x // x ∈ s.head d}] :
    Global s d r ↔ CountInRange r (Fintype.card {x // x ∈ s.head d}) :=
  inRange_card _ _

/-- Cardinality reduction is local to each live parent's fiber. -/
theorem perParent_fin_iff (s : Configuration C U) (d parent : C) (r : Range)
    (count : U → Nat)
    (repr : ∀ p ∈ s.head parent, {x // s.contains d p x} ≃ Fin (count p)) :
    PerParent s d parent r ↔ ∀ p ∈ s.head parent, CountInRange r (count p) := by
  apply forall_congr'
  intro p
  apply imp_congr_right
  intro hp
  rw [inRange_iff r (repr p hp), inRange_card]
  simp

theorem perParent_card (s : Configuration C U) (d parent : C) (r : Range)
    [∀ p, Fintype {x // s.contains d p x}] :
    PerParent s d parent r ↔
      ∀ p ∈ s.head parent, CountInRange r (Fintype.card {x // s.contains d p x}) := by
  simp only [PerParent, inRange_card]

-- [proof->req~abstract-multiplicity~1]
/-- A subtype inherits an aggregate upper limit by inclusion. No aggregate
lower limit is imposed on each subtype, and no interval-refinement test follows. -/
theorem subview_upper (s : Configuration C U) {d a : C} {lo hi : Nat}
    (subset : s.head d ⊆ s.head a) (bound : Global s a ⟨lo, .finite hi⟩) :
    Nonempty ({x // x ∈ s.head d} ↪ Fin hi) := by
  obtain ⟨e⟩ := bound.2
  exact ⟨(⟨fun x => ⟨x.val, subset x.property⟩,
    fun _ _ h => Subtype.ext (congrArg (fun (x : {x // x ∈ s.head a}) => x.val) h)⟩ :
    {x // x ∈ s.head d} ↪ {x // x ∈ s.head a}).trans e⟩

/-- A super view already contains its subtype identities; adding that view
again does not increase the aggregate. This applies along the whole super chain. -/
theorem inherited_union {n : Nat} (m : EffectiveCore n)
    (s : Configuration (Fin n) U) (inh : s.Inherits m) {d a : Fin n}
    (path : m.Ancestor d a) : s.head d ∪ s.head a = s.head a := by
  have subset : s.head d ⊆ s.head a := by
    intro x hx
    induction path with
    | refl => exact hx
    | tail _ edge ih => exact inh _ _ edge x ih
  exact Set.union_eq_right.mpr subset

/-- Nested abstract multiplicity is exactly the existing local obligation when
its range is the authored/default range. No specialized counting rule is added. -/
theorem perParent_of_multiplicities {n : Nat} (m : EffectiveCore n)
    (s : Configuration (Fin n) U) (h : s.Multiplicities m) {d p : Fin n}
    (parent : m.family.parent d = some p) :
    PerParent s d p (m.family.multiplicity d) := h d p parent

end Clafer.Semantics.AbstractMultiplicity
