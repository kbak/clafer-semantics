module

public import Clafer.Verification.ProtocolProofs
public import Mathlib.Lean.Json

/-!
# Checked effective-IR import

SoSyM §§5.3–5.5, §6.2.2/Figure 22, under the guarded #49/#50 contract.
The external decoder supplies compiler UIDs (strings), never display-name
bindings. This module checks the finite indexing, intervals and fragment again.
No authored AST or default-elaboration evidence is constructed.
-/

@[expose] public section
namespace Clafer.Verification.Import
open Semantics MCS DPGraph.Predicates

structure Row where
  uid : String
  name : String
  parent : String
  «abstract» : Bool
  super : Option String
  mode : String
  target : Option String
  card : List Int
  group : List Int
  parentRank : Nat
  superRank : Nat
  unused : Bool
  deriving Repr, Lean.FromJson

structure Input where
  declarations : List Row
  deriving Repr, Lean.FromJson

def rootRow : Row := ⟨"root", "Sing", "", false, none, "basic", none,
  [1, 1], [0, -1], 0, 0, false⟩

def Input.rows (r : Input) : List Row := rootRow :: r.declarations
abbrev Input.Index (r : Input) := Fin r.rows.length
def Input.at (r : Input) (i : r.Index) : Row := r.rows[i]
def Input.uid (r : Input) (i : r.Index) : String := (r.at i).uid
def Input.root (r : Input) : r.Index := ⟨0, by simp [Input.rows]⟩

def Input.lookup (r : Input) (uid : String) : Option r.Index :=
  (List.finRange r.rows.length).find? (fun i => r.uid i == uid)

def range (xs : List Int) : Range :=
  ⟨xs[0]?.getD 0 |>.toNat,
   if xs[1]?.getD 0 = -1 then .unbounded else .finite (xs[1]?.getD 0).toNat⟩

def rangeData (v : Range) : List Int :=
  [Int.ofNat v.lower, match v.upper with | .unbounded => -1 | .finite n => Int.ofNat n]

def Input.parentUID (r : Input) (i : r.Index) : Option String :=
  if i = r.root then none
  else if (r.at i).parent = "clafer" ∧ (r.at i).abstract = true then none
  else some (r.at i).parent

def Input.reference (r : Input) (i : r.Index) : ReferenceTo r.Index :=
  match (r.at i).target.bind r.lookup with
  | none => .basic
  | some t => if (r.at i).mode = "set" then .set t else .bag t

def Input.normalize (r : Input) : EffectiveCore r.rows.length where
  id i := ⟨i.val⟩
  group i := range (r.at i).group
  family := {
    root := r.root
    parent i := (r.parentUID i).bind r.lookup
    super i := (r.at i).super.bind r.lookup
    reference := r.reference
    origin i := if i = r.root then .syntheticRoot else .user
    isAbstract i := (r.at i).abstract
    name i := (r.at i).name
    multiplicity i := range (r.at i).card
    group i := ⟨none, .bounds (range (r.at i).group)⟩ }

def Input.certificate (r : Input) : CoreCertificate r.rows.length :=
  ⟨fun i => (r.at i).parentRank, fun i => (r.at i).superRank, fun i => (r.at i).unused⟩

def modeName {C : Type} : ReferenceTo C → String
  | .basic => "basic" | .set _ => "set" | .bag _ => "bag"

/-- Fieldwise representation, not a serialization roundtrip or an assumed
semantic equivalence. Finite IDs are indices with an explicit UID dictionary.
All original edges must be recovered through that dictionary. -/
structure Represents (r : Input) (m : EffectiveCore r.rows.length) : Prop where
  ids : ∀ i, m.id i = ⟨i.val⟩
  root : m.family.root = r.root
  parent : ∀ i, (m.family.parent i).map r.uid = r.parentUID i
  super : ∀ i, (m.family.super i).map r.uid = (r.at i).super
  target : ∀ i, (m.family.reference i).target.map r.uid = (r.at i).target
  mode : ∀ i, modeName (m.family.reference i) = (r.at i).mode
  origin : ∀ i, m.family.origin i = if i = r.root then .syntheticRoot else .user
  abstract : ∀ i, m.family.isAbstract i = (r.at i).abstract
  name : ∀ i, m.family.name i = (r.at i).name
  card : ∀ i, rangeData (m.family.multiplicity i) = (r.at i).card
  group : ∀ i, rangeData (m.group i) = (r.at i).group
  familyGroup : ∀ i, m.family.group i = ⟨none, .bounds (m.group i)⟩

instance (r : Input) (m : EffectiveCore r.rows.length) : Decidable (Represents r m) :=
  decidable_of_iff ( _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩,
     fun h => ⟨h.ids, h.root, h.parent, h.super, h.target, h.mode,
       h.origin, h.abstract, h.name, h.card, h.group, h.familyGroup⟩⟩

def reserved : List String := ["root", "clafer", "integer", "int", "string", "double", "real", "boolean"]

/-- Checks exact preservation before core/fragment checks. Invalid endpoints,
mode/target combinations and illegal sentinel encodings cannot disappear. -/
def Input.bindingChecks (r : Input) : Prop :=
  Function.Injective r.uid ∧
  (∀ i, r.uid i ≠ "" ∧ (i ≠ r.root → r.uid i ∉ reserved)) ∧
  Represents r r.normalize

instance (r : Input) : Decidable r.bindingChecks := by
  unfold Input.bindingChecks Function.Injective
  infer_instance

inductive Error where
  | malformedBindings | malformedCore | unsupportedOrInvalidCertificate
  deriving Repr, DecidableEq

structure Accepted (r : Input) : Type where
  bindings : r.bindingChecks
  core : coreChecks r.normalize r.certificate
  support : supportChecks r.normalize r.certificate

-- [impl->req~clafer-resolved-import~1]
def admit (r : Input) : Except Error (Accepted r) :=
  if hb : r.bindingChecks then
    if hc : coreChecks r.normalize r.certificate then
      if hs : supportChecks r.normalize r.certificate then .ok ⟨hb, hc, hs⟩
      else .error .unsupportedOrInvalidCertificate
    else .error .malformedCore
  else .error .malformedBindings

theorem Accepted.wellFormed {r : Input} (a : Accepted r) : r.normalize.WellFormed :=
  admitted_wellFormed _ _ a.core a.support

theorem Accepted.supported {r : Input} (a : Accepted r) : r.normalize.Supported :=
  admitted_supported _ _ a.support

theorem Accepted.represents {r : Input} (a : Accepted r) : Represents r r.normalize :=
  a.bindings.2.2

/-- A compiler UID cannot merge with a repeated display name or another UID. -/
theorem Accepted.uid_identity {r : Input} (a : Accepted r) (i j : r.Index) :
    r.uid i = r.uid j ↔ r.normalize.id i = r.normalize.id j := by
  constructor
  · intro h; exact congrArg r.normalize.id (a.bindings.1 h)
  · intro h
    apply congrArg r.uid
    exact Fin.ext (congrArg DeclId.value h)

/-- The public raw candidate interface retains head identities and all #50
malformed/violating distinctions after import. -/
def evaluate (r : Input) (c : RawCandidate) : Except Error Result := do
  let _ ← admit r
  return verify r.normalize c

structure UidCandidate where
  objects : List Nat
  root : Nat
  members : List (String × Nat)
  containment : List (String × Nat × Nat)
  references : List (String × Nat × Nat)
  deriving Lean.FromJson

def Input.classId (r : Input) (uid : String) : Except String DeclId :=
  match r.lookup uid with
  | none => .error "unknown_class"
  | some i => .ok ⟨i.val⟩

def Input.member (r : Input) (row : String × Nat) : Except String (DeclId × Nat) := do
  return (← r.classId row.1, row.2)

def Input.link (r : Input) (row : String × Nat × Nat) : Except String (DeclId × Nat × Nat) := do
  return (← r.classId row.1, row.2)

/-- Class translation preserves list rows and original natural object labels.
It does not deduplicate references by their target. -/
def UidCandidate.translate (c : UidCandidate) (r : Input) : Except String RawCandidate := do
  let members ← c.members.mapM r.member
  let containment ← c.containment.mapM r.link
  let references ← c.references.mapM r.link
  return ⟨c.objects, c.root, members, containment, references⟩

end Clafer.Verification.Import
