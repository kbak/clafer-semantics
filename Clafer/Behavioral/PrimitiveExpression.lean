module

public import Clafer.Behavioral.StructuralObservation
public import Clafer.Behavioral.Arithmetic
public import Clafer.Behavioral.Aggregate

/-! # Resolved partial primitive expressions

Static S8/S11 and adopted D3. Conversion, strict singleton extraction, extrema
and occurrence-indexed folds are separate constructors. The source frontend
chooses these explicitly; evaluating a missing expression never supplies zero.
-/

@[expose] public section
namespace Clafer.Behavioral
universe u

mutual
  -- [impl->req~behavioral-reference-atoms~1]
  inductive CollectionExpr (C : Type) : Nat → Type where
    | set (a : SetExpr C n) : CollectionExpr C n
    | literal (i : Int) : CollectionExpr C n
    | integer (a : IntegerExpr C n) : CollectionExpr C n
    | extreme (op : Aggregate.Extreme) (a : CollectionExpr C n) : CollectionExpr C n
    | union (a b : CollectionExpr C n) : CollectionExpr C n
    | inter (a b : CollectionExpr C n) : CollectionExpr C n
    | diff (a b : CollectionExpr C n) : CollectionExpr C n

  inductive IntegerExpr (C : Type) : Nat → Type where
    | literal (i : Int) : IntegerExpr C n
    | coerce (a : CollectionExpr C n) : IntegerExpr C n
    | extract (a : CollectionExpr C n) : IntegerExpr C n
    | cardinality (a : CollectionExpr C n) : IntegerExpr C n
    | binary (op : Arithmetic.Binary) (a b : IntegerExpr C n) : IntegerExpr C n
    | negate (a : IntegerExpr C n) : IntegerExpr C n
    /-- Each operand is a separate occurrence family. Splitting a syntactic
    union must retain its separate operands, including overlapping heads. -/
    | fold (op : Aggregate.Fold) (domains : CollectionList C n)
        (body : IntegerExpr C (n + 1)) : IntegerExpr C n

  inductive CollectionList (C : Type) : Nat → Type where
    | nil : CollectionList C n
    | cons (head : CollectionExpr C n) (tail : CollectionList C n) : CollectionList C n
end

namespace PrimitiveExpression
open Constraints

/-- Operand position plus head identity. This retains repetition across
separate operands and equal dereferenced targets within an operand. -/
def occurrences {U : Type u} (domains : List (Set U)) : Set (Fin domains.length × U) :=
  {p | p.2 ∈ domains[p.1]}

-- [proof->req~behavioral-reference-atoms~1]
theorem occurrences_finite {U : Type u} (domains : List (Set U))
    (finite : ∀ i : Fin domains.length, domains[i].Finite) : (occurrences domains).Finite := by
  have pieces : ∀ i : Fin domains.length, ({i} ×ˢ domains[i]).Finite :=
    fun i => (Set.finite_singleton i).prod (finite i)
  apply (Set.finite_iUnion pieces).subset
  intro p hp
  exact Set.mem_iUnion.mpr ⟨p.1, Set.mem_singleton p.1, hp⟩

@[simp] theorem occurrences_nil {U : Type u} : occurrences ([] : List (Set U)) = ∅ := by
  ext p
  exact Fin.elim0 p.1

mutual
  noncomputable def collection {k n : Nat} {U : Type u} (m : Semantics.EffectiveCore k)
      (τ : Trace (Fin k) U) (R : IntegerRealization U) (ρ : Environment U n) (t : Nat) :
      CollectionExpr (Fin k) n → Option (Set U)
    | .set a => some (a.eval m τ ρ t)
    | .literal i => some {R.encode i}
    | .integer a => (integerValue m τ R ρ t a).map (fun i => {R.encode i.down})
    | .extreme op a => (collection m τ R ρ t a).bind (op.select R)
    | .union a b => lift₂ (· ∪ ·) (collection m τ R ρ t a) (collection m τ R ρ t b)
    | .inter a b => lift₂ (· ∩ ·) (collection m τ R ρ t a) (collection m τ R ρ t b)
    | .diff a b => lift₂ (· \ ·) (collection m τ R ρ t a) (collection m τ R ρ t b)

  noncomputable def integerValue {k n : Nat} {U : Type u} (m : Semantics.EffectiveCore k)
      (τ : Trace (Fin k) U) (R : IntegerRealization U) (ρ : Environment U n) (t : Nat) :
      IntegerExpr (Fin k) n → Option (ULift.{u} Int)
    | .literal i => some ⟨i⟩
    | .coerce a => ((collection m τ R ρ t a).bind (IntegerObservation.coerce R)).map ULift.up
    | .extract a => ((collection m τ R ρ t a).bind R.extract).map ULift.up
    | .cardinality a => (collection m τ R ρ t a).bind finiteCard
    | .binary op a b => (op.eval ((integerValue m τ R ρ t a).map ULift.down)
        ((integerValue m τ R ρ t b).map ULift.down)).map ULift.up
    | .negate a => (integerValue m τ R ρ t a).map (fun i => ⟨-i.down⟩)
    | .fold op domains body =>
      (collections m τ R ρ t domains).bind (fun sets =>
        (op.eval (occurrences sets)
          (fun ix => (integerValue m τ R (ρ.push {ix.2}) t body).map ULift.down)).map ULift.up)

  noncomputable def collections {k n : Nat} {U : Type u} (m : Semantics.EffectiveCore k)
      (τ : Trace (Fin k) U) (R : IntegerRealization U) (ρ : Environment U n) (t : Nat) :
      CollectionList (Fin k) n → Option (List (Set U))
    | .nil => some []
    | .cons a rest => lift₂ List.cons (collection m τ R ρ t a) (collections m τ R ρ t rest)
end

noncomputable def integer {k n : Nat} {U : Type u} (m : Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) (R : IntegerRealization U) (ρ : Environment U n) (t : Nat)
    (e : IntegerExpr (Fin k) n) : Option Int := (integerValue m τ R ρ t e).map ULift.down

-- [impl->req~behavioral-reference-atoms~1]
inductive Atom (C : Type) (n : Nat) where
  | inhabited (a : CollectionExpr C n)
  | equal (a b : CollectionExpr C n)
  | subset (a b : CollectionExpr C n)
  | integerEqual (a b : IntegerExpr C n)
  | less (a b : IntegerExpr C n)

noncomputable def Atom.eval {k n : Nat} {U : Type u} (m : Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) (R : IntegerRealization U) (ρ : Environment U n) (t : Nat) :
    Atom (Fin k) n → Option Prop
  | .inhabited a => (collection m τ R ρ t a).map Set.Nonempty
  | .equal a b => (collection m τ R ρ t a).bind
      (fun x => (collection m τ R ρ t b).map (fun y => x = y))
  | .subset a b => (collection m τ R ρ t a).bind
      (fun x => (collection m τ R ρ t b).map (fun y => x ⊆ y))
  | .integerEqual a b => lift₂ (· = ·) (integer m τ R ρ t a) (integer m τ R ρ t b)
  | .less a b => lift₂ (· < ·) (integer m τ R ρ t a) (integer m τ R ρ t b)

variable {k n : Nat} {U : Type u} (m : Semantics.EffectiveCore k)
  (τ : Trace (Fin k) U) (R : IntegerRealization U) (ρ : Environment U n) (t : Nat)

theorem coerce_eval (a : CollectionExpr (Fin k) n) :
    integer m τ R ρ t (.coerce a) = (collection m τ R ρ t a).bind (IntegerObservation.coerce R) := by
  unfold integer integerValue
  cases (collection m τ R ρ t a).bind (IntegerObservation.coerce R) <;> rfl

theorem fold_eval (op : Aggregate.Fold) (domains : CollectionList (Fin k) n)
    (body : IntegerExpr (Fin k) (n + 1)) :
    integer m τ R ρ t (.fold op domains body) = (collections m τ R ρ t domains).bind
      (fun sets => op.eval (occurrences sets) (fun ix => integer m τ R (ρ.push {ix.2}) t body)) := by
  unfold integer
  conv_lhs => rw [integerValue]
  cases collections m τ R ρ t domains with
  | none => rfl
  | some sets =>
    simp only [Option.bind_some, Option.map_map]
    cases op.eval (occurrences sets)
      (fun ix => (integerValue m τ R (ρ.push {ix.2}) t body).map ULift.down) <;> rfl

-- [proof->req~behavioral-reference-atoms~1]
theorem coerce_defined_iff (a : CollectionExpr (Fin k) n) :
    (∃ i, integer m τ R ρ t (.coerce a) = some i) ↔
      ∃ S, collection m τ R ρ t a = some S ∧ S.Finite ∧ S ⊆ R.domain := by
  rw [coerce_eval]
  simp only [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨i, S, hs, hi⟩
    exact ⟨S, hs, (IntegerObservation.coerce_defined_iff R S).mp ⟨i, hi⟩⟩
  · rintro ⟨S, hs, finite, typed⟩
    obtain ⟨i, hi⟩ := (IntegerObservation.coerce_defined_iff R S).mpr ⟨finite, typed⟩
    exact ⟨i, S, hs, hi⟩

theorem division_zero (a : IntegerExpr (Fin k) n) :
    integer m τ R ρ t (.binary .divide a (.literal 0)) = none := by
  simp only [integer, integerValue, Arithmetic.Binary.eval]
  cases integerValue m τ R ρ t a <;> simp [Arithmetic.Binary.apply]

theorem empty_arithmetic : integer m τ R ρ t (.coerce (.set .empty)) = some 0 := by
  simp [integer, integerValue, collection, SetExpr.eval]

theorem empty_strict : integer m τ R ρ t (.extract (.set .empty)) = none := by
  simp [integer, integerValue, collection, SetExpr.eval]

theorem empty_extreme (op : Aggregate.Extreme) :
    collection m τ R ρ t (.extreme op (.set .empty)) = some ∅ := by
  simp [collection, SetExpr.eval, Aggregate.select_empty]

theorem empty_sum (body : IntegerExpr (Fin k) (n + 1)) :
    integer m τ R ρ t (.fold .sum .nil body) = some 0 := by
  simp [integer, integerValue, collections]

theorem empty_product (body : IntegerExpr (Fin k) (n + 1)) :
    integer m τ R ρ t (.fold .product .nil body) = some 1 := by
  simp [integer, integerValue, collections]

theorem missing_comparison (a b : IntegerExpr (Fin k) n)
    (missing : integer m τ R ρ t a = none) :
    (Atom.less a b).eval m τ R ρ t = none := by
  simp only [Atom.eval, missing, lift₂, Option.bind_none]

-- [proof->req~behavioral-reference-atoms~1]
theorem finite_reference_operand (m : Structural.Core k) (valid : Structural.Valid m τ)
    {S : Set U} (finite : S.Finite) {d o c : Fin k}
    (owner : InheritedReference.Owner m.family d o)
    (target : (m.family.reference o).target = some c)
    (primitive : (τ.raw m.toEffectiveCore t).head c ⊆ R.domain) :
    ∃ i, integer m.toEffectiveCore (Structural.observed m τ) R (ρ.push S) t
      (.coerce (.set (.step (.deref d) (.var 0)))) = some i := by
  apply (coerce_defined_iff _ _ _ _ _ _).mpr
  refine ⟨Structural.eval m τ (.step (.deref d) (.var 0)) (ρ.push S) t, rfl, ?_, ?_⟩
  · exact Structural.finite_captured_deref m τ valid ρ finite d t
  · exact (Structural.captured_target_typed m τ valid ρ S owner target t).trans primitive

end PrimitiveExpression
end Clafer.Behavioral
