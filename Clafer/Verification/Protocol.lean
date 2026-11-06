module

public import Clafer.Verification.Finite

/-!
[impl->req~clafer-finite-checker~1]
[proof->req~clafer-finite-checker~1]
-/

/-!
# Deterministic finite table protocol

This is an in-memory supplied-candidate interface, not a production parser.
Object IDs and resolved class IDs are independent of record order and names.
Ordinary link IDs are their typed relation tuples; reference occurrences are
head object IDs, so repeated parent/target pairs survive normalization.
-/

@[expose] public section
namespace Clafer.Verification
open Semantics

structure RawCandidate where
  objects : List Nat
  root : Nat
  members : List (DeclId × Nat)
  containment : List (DeclId × Nat × Nat)
  references : List (DeclId × Nat × Nat)
  deriving DecidableEq, Repr

inductive InputError where
  | duplicateObject | missingRoot | duplicateMembership | duplicateLink
  | unknownClass | danglingObject | illTyped
  deriving DecidableEq, Repr

inductive Result where
  | malformed (error : InputError)
  | satisfies
  | violates
  deriving DecidableEq, Repr

variable {n : Nat}

def RawCandidate.decode (r : RawCandidate) (m : EffectiveCore n)
    (hroot : r.root ∈ r.objects) : Candidate n where
  size := r.objects.length
  root := ⟨r.objects.idxOf r.root, List.idxOf_lt_length_of_mem hroot⟩
  head d x := decide ((m.id d, r.objects[x]) ∈ r.members)
  contains d p x := decide ((m.id d, r.objects[p], r.objects[x]) ∈ r.containment)
  deref d x t := decide ((m.id d, r.objects[x], r.objects[t]) ∈ r.references)

/-- Error priority is fixed by this order, independent of table enumeration.
The object and link checks precede membership-based normalization. -/
def verify (m : EffectiveCore n) (r : RawCandidate) : Result :=
  if ¬ r.objects.Nodup then .malformed .duplicateObject
  else if hroot : r.root ∉ r.objects then .malformed .missingRoot
  else if ¬ r.members.Nodup then .malformed .duplicateMembership
  else if ¬ r.containment.Nodup ∨ ¬ r.references.Nodup then .malformed .duplicateLink
  else if (∃ row ∈ r.members, ¬ ∃ d, m.id d = row.1) ∨
      (∃ row ∈ r.containment ++ r.references, ¬ ∃ d, m.id d = row.1) then
    .malformed .unknownClass
  else if (∃ row ∈ r.members, row.2 ∉ r.objects) ∨
      (∃ row ∈ r.containment ++ r.references,
        row.2.1 ∉ r.objects ∨ row.2.2 ∉ r.objects) then .malformed .danglingObject
  else
    let c := r.decode m (Classical.not_not.mp hroot)
    if ¬ (realize c).Typed m then .malformed .illTyped
    else if check m c then .satisfies else .violates

theorem duplicate_objects_rejected (m : EffectiveCore n) (r : RawCandidate)
    (h : ¬ r.objects.Nodup) : verify m r = .malformed .duplicateObject := by
  simp [verify, h]

theorem missing_root_rejected (m : EffectiveCore n) (r : RawCandidate)
    (hn : r.objects.Nodup) (hr : r.root ∉ r.objects) :
    verify m r = .malformed .missingRoot := by simp [verify, hn, hr]

end Clafer.Verification
