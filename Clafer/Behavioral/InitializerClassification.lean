module

public import Clafer.Behavioral.InitializerBounds

/-! # Resolved initializer classification and diagnostic contract

SoSyM Appendix 3 defaulting, the adopted numeric-group evolution, behavioral
§5 Definitions 3–5 / §6.1, and accepted #170 decisions. Classification is an
independent source contract, reused by production Initializers.elaborate.
Names/types are checked by the frontend before this interface. -/

@[expose] public section
namespace Clafer.Behavioral.Initializers.Classification
open DPGraph.Predicates

inductive Clock where
  | instanceBirth | parentBirth | globalZero
  deriving DecidableEq, Repr

-- [impl->req~initializer-clock-selection~1]
/-- Authored timing, independent of multiplicity. Collection context is the
original declaration's context, never a realization's actual parent. -/
inductive Selection where
  | instance | collection
  deriving DecidableEq, Repr

def Selection.resolve (choice : Selection) (parented : Bool) : Clock :=
  match choice with
  | .instance => .instanceBirth
  | .collection => if parented then .parentBirth else .globalZero

inductive Diagnostic where
  | invalidMultiplicity | parentlessMultiplicity | scalarNotEstablished
  deriving DecidableEq, Repr

/-- Authored absence remains distinguishable from an explicit unrestricted
bound. The effective parent group includes inherited keyword provenance. -/
structure Declaration where
  abstract : Bool
  parented : Bool
  authored : Option Range
  parentGroup : GroupCard := .bounds unrestricted

def valid (r : Range) : Bool := match r.upper with
  | .finite n => decide (r.lower ≤ n)
  | .unbounded => true

def plural (r : Range) : Bool := match r.upper with
  | .finite n => decide (1 < n)
  | .unbounded => true

-- [impl->req~behavioral-initializer-contract~1]
-- [impl->req~initializer-clock-selection~1]
/-- No arbitrary constraints, RHS values or reference-kind flags participate
in classification. Scalar admission is a separate check for abstract singles. -/
def classify (d : Declaration) (scalarRhs : Bool) (choice : Option Selection := none) :
    Except Diagnostic Clock :=
  let invalid := match d.authored with | none => false | some r => !valid r
  let selected : Except Diagnostic Clock :=
    if let some explicit := choice then .ok (explicit.resolve d.parented)
    else if d.abstract && !d.parented then
      match d.authored with
      | none => .ok .instanceBirth
      | some r => if r = unrestricted then .ok .globalZero else .error .parentlessMultiplicity
    else if d.abstract && d.authored.isNone then .ok .instanceBirth
    else
      let r := d.authored.getD d.parentGroup.childDefault
      .ok (if plural r then .parentBirth else .instanceBirth)
  if invalid then .error .invalidMultiplicity else
    match selected with
    | .error e => .error e
    | .ok clock => if d.abstract && decide (clock = .instanceBirth) && !scalarRhs then
        .error .scalarNotEstablished else .ok clock

theorem valid_iff (r : Range) : valid r = true ↔ ValidRange r := by
  cases r with | mk lo hi => cases hi <;> simp [valid, ValidRange]

-- [proof->req~initializer-clock-selection~1]
/-- Valid bounds are checked independently; abstract per-instance scalar
admission still applies after explicit clock selection. -/
theorem explicit_classification (d : Declaration) (scalar : Bool) (choice : Selection)
    (ranges : ∀ r, d.authored = some r → ValidRange r) :
    classify d scalar (some choice) =
      if d.abstract && decide (choice.resolve d.parented = .instanceBirth) && !scalar then
        .error .scalarNotEstablished else .ok (choice.resolve d.parented) := by
  have ok : (match d.authored with | none => false | some r => !valid r) = false := by
    cases h : d.authored with
    | none => rfl
    | some r => simp [(valid_iff r).mpr (ranges r h)]
  simp only [classify, ok, Bool.false_eq_true, ↓reduceIte]

/-- Altering a valid multiplicity never alters an explicitly selected clock
or its abstract scalar diagnostic. Authored omission remains stored separately. -/
theorem explicit_bound_independent (d : Declaration) (a b : Option Range)
    (ha : ∀ r, a = some r → ValidRange r) (hb : ∀ r, b = some r → ValidRange r)
    (scalar : Bool) (choice : Selection) :
    classify { d with authored := a } scalar (some choice) =
      classify { d with authored := b } scalar (some choice) := by
  rw [explicit_classification _ _ _ ha, explicit_classification _ _ _ hb]

/-- Choosing collection removes only per-instance scalar admission, not
independent validity, reference, cardinality or key obligations. -/
theorem explicit_collection (d : Declaration) (scalar : Bool)
    (ranges : ∀ r, d.authored = some r → ValidRange r) :
    classify d scalar (some .collection) =
      .ok (if d.parented then .parentBirth else .globalZero) := by
  rw [explicit_classification _ _ _ ranges]
  cases d.parented <;> simp [Selection.resolve]

/-- A compiled obligation retains its origin and clock through refinement.
The refined declaration can add a separately classified own obligation. -/
structure Obligation (Origin RHS : Type) where
  origin : Origin
  clock : Clock
  rhs : RHS

def inherit {O R : Type} (obligation : Obligation O R) (_refinedMultiplicity : Range) :
    Obligation O R := obligation

-- [proof->req~behavioral-initializer-contract~1]
theorem inherit_clock {O R : Type} (o : Obligation O R) (bound : Range) :
    (inherit o bound).clock = o.clock := rfl

theorem inherit_rhs {O R : Type} (o : Obligation O R) (bound : Range) :
    (inherit o bound).rhs = o.rhs := rfl

theorem ordinary_default_single (g : GroupCard) :
    classify ⟨false, true, none, g⟩ false = .ok .instanceBirth := by
  cases g with
  | bounds r =>
    cases r with | mk lo hi =>
      cases hi <;> cases lo <;>
        simp [classify, GroupCard.childDefault, plural, one, optional]
  | xor | or | mux | opt => rfl

-- [utest->req~behavioral-initializer-contract~1]
theorem default_and_abstract_matrix :
    GroupCard.opt.childDefault = optional ∧
    (GroupCard.bounds unrestricted).childDefault = one ∧
    classify ⟨true, true, none, .opt⟩ true = .ok .instanceBirth ∧
    classify ⟨true, true, some unrestricted, .opt⟩ false = .ok .parentBirth ∧
    classify ⟨true, false, none, .opt⟩ true = .ok .instanceBirth ∧
    classify ⟨true, false, some unrestricted, .opt⟩ false = .ok .globalZero ∧
    classify ⟨true, false, some optional, .opt⟩ true = .error .parentlessMultiplicity ∧
    classify ⟨true, false, some ⟨2, .finite 2⟩, .opt⟩ false = .error .parentlessMultiplicity ∧
    classify ⟨true, false, some ⟨1, .unbounded⟩, .opt⟩ true = .error .parentlessMultiplicity ∧
    classify ⟨true, true, none, .opt⟩ false = .error .scalarNotEstablished ∧
    classify ⟨false, true, some optional, .opt⟩ false = .ok .instanceBirth ∧
    classify ⟨false, true, some ⟨2, .finite 1⟩, .opt⟩ true = .error .invalidMultiplicity := by
  simp [classify, valid, plural, GroupCard.childDefault, unrestricted, one, optional]

end Clafer.Behavioral.Initializers.Classification
