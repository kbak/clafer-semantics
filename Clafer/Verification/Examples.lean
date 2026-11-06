module

public import Clafer.Verification.Admission
public import Clafer.Semantics.Bridge
public import Clafer.Semantics.Reachability

/-!
[impl->req~clafer-checker-witnesses~1]
[proof->req~clafer-checker-witnesses~1]
[utest->req~clafer-checker-witnesses~1]
[utest->req~clafer-finite-checker~1]
-/

/-!
# Whole-model finite witnesses

Independent finite inputs for the selected 2014 semantics. Theorem witnesses
use kernel reduction, not `native_decide`. Native tests below exercise the same
algorithm without claiming per-instance proof certificates.
-/

@[expose] public section
namespace Clafer.Verification.Examples
open Semantics MCS DPGraph.Predicates

def refs (isSet : Bool) (bounds : Range := ⟨2, .finite 3⟩)
    (group : Range := unrestricted) : EffectiveCore 3 where
  family := {
    root := 0
    parent := fun d => if d = 0 then none else some 0
    reference := fun d => if d = 2 then (if isSet then .set 1 else .bag 1) else .basic
    super := fun _ => none
    origin := fun d => if d = 0 then .syntheticRoot else .user
    isAbstract := fun _ => false
    name := fun d => if d = 0 then "Sing" else "repeated-name"
    multiplicity := fun d => if d = 2 then bounds else one }
  id d := ⟨d.val⟩
  group d := if d = 0 then group else unrestricted

def refCertificate : CoreCertificate 3 where
  parentRank d := if d = 0 then 0 else 1
  superRank _ := 0
  unused _ := false

def bag : Candidate 3 where
  size := 4
  root := 0
  head d x := (d == 0 && x == 0) || (d == 1 && x == 1) ||
    (d == 2 && (x == 2 || x == 3))
  contains d p x := p == 0 &&
    ((d == 1 && x == 1) || (d == 2 && (x == 2 || x == 3)))
  deref d x t := d == 2 && (x == 2 || x == 3) && t == 1

theorem refs_valid : (refs false).WellFormed :=
  admitted_wellFormed _ refCertificate (by decide) (by decide)
theorem refs_supported : (refs false).Supported :=
  admitted_supported _ refCertificate (by decide)

theorem bag_accepts : check (refs false) bag = true := by decide
theorem bag_satisfies : StructuralSatisfies (refs false) (realize bag) :=
  (check_correct _ _ refs_valid refs_supported).mp bag_accepts

theorem set_rejects_repetition : check (refs true) bag = false := by decide
theorem exact_two_accepts : check (refs false ⟨2, .finite 2⟩) bag = true := by decide
theorem optional_rejects_two : check (refs false optional) bag = false := by decide
theorem zero_rejects_two : check (refs false ⟨0, .finite 0⟩) bag = false := by decide
theorem lower_three_rejects : check (refs false ⟨3, .unbounded⟩) bag = false := by decide
theorem unbounded_accepts : check (refs false unrestricted) bag = true := by decide
theorem group_three_accepts : check (refs false unrestricted ⟨3, .finite 3⟩) bag = true := by decide
theorem group_two_rejects : check (refs false unrestricted ⟨2, .finite 2⟩) bag = false := by decide

def missingTarget : Candidate 3 := { bag with deref := fun _ _ _ => false }
theorem missing_target_violates : check (refs false) missingTarget = false := by decide
theorem missing_target_typed : (realize missingTarget).Typed (refs false) := by decide

/-- Collapsing a duplicate occurrence loses both its object and link count. -/
def collapsed : Candidate 3 where
  size := 3
  root := 0
  head d x := d == x
  contains d p x := p == 0 && d != 0 && d == x
  deref d x t := d == 2 && x == 2 && t == 1

theorem collapse_mutation_detected :
    check (refs false) bag ≠ check (refs false) collapsed := by decide

/-- Deliberately omitting the upper bound changes the verdict on two occurrences. -/
theorem upper_bound_mutation_detected :
    check (refs false optional) bag ≠ check (refs false unrestricted) bag := by decide

/-- Overlap remains representable and typed; its group still counts the union. -/
def overlapping : Candidate 3 where
  size := 3
  root := 0
  head d x := (d == 0 && x == 0) || (d == 1 && x == 1) || (d == 2 && x != 0)
  contains d p x := p == 0 && ((d == 1 && x == 1) || (d == 2 && x != 0))
  deref d x t := d == 2 && x != 0 && t == 1

theorem unrelated_overlap_rejected :
    check (refs false ⟨2, .finite 2⟩ ⟨2, .finite 2⟩) overlapping = false := by decide

theorem unrelated_overlap_typed : (realize overlapping).Typed (refs false) := by decide

theorem overlap_group_union : (realize overlapping).Groups
    (refs false ⟨2, .finite 2⟩ ⟨2, .finite 2⟩) := by
  unfold Configuration.Groups Configuration.Child realize
  simp only [inRange_card, Set.mem_ofPred_eq]
  decide

/-- The old obligations all hold: only the independent #87 clause rejects it. -/
theorem overlap_old_checks :
    (realize overlapping).Typed (refs false) ∧
    (realize overlapping).Rooted (refs false) ∧
    (realize overlapping).Inherits (refs false) ∧
    (realize overlapping).Abstracts (refs false) ∧
    (realize overlapping).Parents (refs false) ∧
    (realize overlapping).References (refs false) ∧
    (realize overlapping).Keys (refs false) ∧
    multiplicityChecks (refs false ⟨2, .finite 2⟩) overlapping ∧
    groupChecks (refs false unrestricted ⟨2, .finite 2⟩) overlapping := by decide

def rawOverlap : RawCandidate where
  objects := [0, 1, 2]
  root := 0
  members := [(⟨0⟩, 0), (⟨1⟩, 1), (⟨2⟩, 1), (⟨2⟩, 2)]
  containment := [(⟨1⟩, 0, 1), (⟨2⟩, 0, 1), (⟨2⟩, 0, 2)]
  references := [(⟨2⟩, 1, 1), (⟨2⟩, 2, 1)]

theorem overlap_protocol_violates : run (refs false) refCertificate rawOverlap =
    .candidate .violates := by decide

def rawBag : RawCandidate where
  objects := [10, 20, 30, 40]
  root := 10
  members := [(⟨0⟩, 10), (⟨1⟩, 20), (⟨2⟩, 30), (⟨2⟩, 40)]
  containment := [(⟨1⟩, 10, 20), (⟨2⟩, 10, 30), (⟨2⟩, 10, 40)]
  references := [(⟨2⟩, 30, 20), (⟨2⟩, 40, 20)]

theorem protocol_accepts : run (refs false) refCertificate rawBag =
    .candidate .satisfies := by decide
theorem protocol_set_violates : run (refs true) refCertificate rawBag =
    .candidate .violates := by decide
theorem duplicate_identity : verify (refs false) { rawBag with objects := [10, 20, 30, 30] } =
    .malformed .duplicateObject := by decide
theorem duplicate_tuple : verify (refs false)
    { rawBag with references := (⟨2⟩, 30, 20) :: rawBag.references } =
    .malformed .duplicateLink := by decide
theorem dangling_identity : verify (refs false)
    { rawBag with references := [(⟨2⟩, 30, 99)] } = .malformed .danglingObject := by decide
theorem unknown_class : verify (refs false)
    { rawBag with members := (⟨99⟩, 10) :: rawBag.members } = .malformed .unknownClass := by decide
theorem ill_typed_endpoint : verify (refs false)
    { rawBag with references := [(⟨2⟩, 30, 10)] } = .malformed .illTyped := by decide
theorem empty_reference_table_violates : verify (refs false)
    { rawBag with references := [] } = .violates := by decide

def inheritance : EffectiveCore 6 where
  family := {
    root := 0
    parent := fun d => if d = 3 ∨ d = 4 then some 0 else if d = 5 then some 3 else none
    reference := fun _ => .basic
    super := fun d => if d = 2 then some 1 else if d = 3 ∨ d = 4 then some 2 else none
    origin := fun d => if d = 0 then .syntheticRoot else .user
    isAbstract := fun d => d == 1 || d == 2
    name := fun d => if d = 0 then "Sing" else "C"
    multiplicity := fun _ => unrestricted }
  id d := ⟨d.val⟩
  group d := if d = 3 then one else unrestricted

def inheritanceCertificate : CoreCertificate 6 where
  parentRank d := if d = 5 then 2 else if d = 3 ∨ d = 4 then 1 else 0
  superRank d := if d = 2 then 1 else if d = 3 ∨ d = 4 then 2 else 0
  unused _ := false

def nested : Candidate 6 where
  size := 4
  root := 0
  head d x := (d == 0 && x == 0) || ((d == 1 || d == 2) && (x == 1 || x == 2)) ||
    (d == 3 && x == 1) || (d == 4 && x == 2) || (d == 5 && x == 3)
  contains d p x := ((d == 3 && x == 1 || d == 4 && x == 2) && p == 0) ||
    (d == 5 && p == 1 && x == 3)
  deref _ _ _ := false

theorem inheritance_valid : inheritance.WellFormed :=
  admitted_wellFormed _ inheritanceCertificate (by decide) (by decide)
theorem inheritance_supported : inheritance.Supported :=
  admitted_supported _ inheritanceCertificate (by decide)
theorem nested_accepts : check inheritance nested = true := by decide
theorem nested_satisfies : StructuralSatisfies inheritance (realize nested) :=
  (check_correct _ _ inheritance_valid inheritance_supported).mp nested_accepts
theorem nested_reachable (x : Fin nested.size) : (realize nested).Reaches x :=
  structural_reaches inheritance_valid inheritance_supported nested_satisfies x

def siblingOverlap : Candidate 6 := {
  size := 4
  root := 0
  deref := nested.deref
  head := fun d x => nested.head d x || (d == 4 && x == 1)
  contains := fun d p x => nested.contains d p x || (d == 4 && p == 0 && x == 1) }
theorem sibling_overlap_rejected : check inheritance siblingOverlap = false := by decide

/-- Containment ancestry is not super ancestry: the nested field shares its
owner's object, and all endpoints remain typed. -/
def nestedOverlap : Candidate 6 where
  size := 3
  root := 0
  head d x := (d == 0 && x == 0) || ((d == 1 || d == 2) && x != 0) ||
    ((d == 3 || d == 5) && x == 1) || (d == 4 && x == 2)
  contains d p x := (p == 0 && ((d == 3 && x == 1) || (d == 4 && x == 2))) ||
    (d == 5 && p == 1 && x == 1)
  deref _ _ _ := false

theorem nested_overlap_typed : (realize nestedOverlap).Typed inheritance := by decide
theorem nested_overlap_rejected : check inheritance nestedOverlap = false := by decide

/-- Separate abstract roots, each covered by its own concrete child. -/
def separateTrees : EffectiveCore 5 where
  family := {
    root := 0
    parent d := if d = 3 ∨ d = 4 then some 0 else none
    reference _ := .basic
    super d := if d = 3 then some 1 else if d = 4 then some 2 else none
    origin d := if d = 0 then .syntheticRoot else .user
    isAbstract d := d == 1 || d == 2
    name d := if d = 0 then "Sing" else "same-name"
    multiplicity _ := unrestricted }
  id d := ⟨d.val⟩
  group _ := unrestricted

def treeCertificate : CoreCertificate 5 where
  parentRank d := if d = 3 ∨ d = 4 then 1 else 0
  superRank d := if d = 3 ∨ d = 4 then 1 else 0
  unused _ := false

def treeOverlap : RawCandidate where
  objects := [0, 1]
  root := 0
  members := [(⟨0⟩, 0), (⟨1⟩, 1), (⟨2⟩, 1), (⟨3⟩, 1), (⟨4⟩, 1)]
  containment := [(⟨3⟩, 0, 1), (⟨4⟩, 0, 1)]
  references := []

theorem separate_trees_overlap_violates :
    run separateTrees treeCertificate treeOverlap = .candidate .violates := by decide

def distinctTrees : RawCandidate where
  objects := [0, 1, 2]
  root := 0
  members := [(⟨0⟩, 0), (⟨1⟩, 1), (⟨2⟩, 2), (⟨3⟩, 1), (⟨4⟩, 2)]
  containment := [(⟨3⟩, 0, 1), (⟨4⟩, 0, 2)]
  references := []

theorem separate_trees_distinct_satisfy :
    run separateTrees treeCertificate distinctTrees = .candidate .satisfies := by decide

def uncovered : Candidate 6 := {
  size := 4
  root := 0
  contains := nested.contains
  deref := nested.deref
  head := fun d x => nested.head d x || (d == 1 && x == 3) }
theorem uncovered_abstract_rejected : check inheritance uncovered = false := by decide

def emptyClasses : Candidate 6 where
  size := 1
  root := 0
  head d _ := d == 0
  contains _ _ _ := false
  deref _ _ _ := false
theorem empty_classes_accept : check inheritance emptyClasses = true := by decide

def cyclic : EffectiveCore 3 where
  family := {
    root := 0
    parent := fun d => if d = 0 then none else if d = 1 then some 0 else some 1
    reference := fun d => if d = 0 then .basic else if d = 1 then .bag 2 else .bag 1
    super := fun _ => none
    origin := fun d => if d = 0 then .syntheticRoot else .user
    isAbstract := fun _ => false
    name := fun d => if d = 0 then "Sing" else "R"
    multiplicity := fun _ => one }
  id d := ⟨d.val⟩
  group _ := unrestricted

def cycle : Candidate 3 where
  size := 3
  root := 0
  head d x := d == x
  contains d p x := (d == 1 && p == 0 && x == 1) || (d == 2 && p == 1 && x == 2)
  deref d x t := (d == 1 && x == 1 && t == 2) || (d == 2 && x == 2 && t == 1)
theorem reference_cycle_accepts : check cyclic cycle = true := by decide

/-- Test-only mutant: count distinct dereferenced targets in place of reference
occurrences. The unchanged optional-card fixture exposes the lost duplicate. -/
def collapsedMultiplicity (m : EffectiveCore n) (c : Candidate n) : Prop :=
  ∀ d p, m.family.parent d = some p → ∀ x, c.head p x = true →
    CountInRange (m.family.multiplicity d)
      (if (m.family.reference d).kind = .basic then
        Fintype.card {y : Fin c.size // c.contains d x y = true}
       else Fintype.card {t : Fin c.size // ∃ y,
         c.contains d x y = true ∧ c.deref d y t = true})

instance (m : EffectiveCore n) (c : Candidate n) : Decidable (collapsedMultiplicity m c) := by
  unfold collapsedMultiplicity
  infer_instance

def collapseMutant (m : EffectiveCore n) (c : Candidate n) : Bool :=
  decide ((realize c).Typed m ∧ (realize c).Rooted m ∧ (realize c).Inherits m ∧
    (realize c).Abstracts m ∧ (realize c).Parents m ∧ (realize c).References m ∧
    (realize c).Keys m ∧ collapsedMultiplicity m c ∧ groupChecks m c ∧
    (realize c).DeclarationDisjoint m)

/-- Test-only mutant that deliberately drops all local upper bounds. -/
def upperBoundMutant (m : EffectiveCore n) (c : Candidate n) : Bool :=
  check {m with family := {m.family with multiplicity := fun d =>
    ⟨(m.family.multiplicity d).lower, .unbounded⟩}} c

theorem collapse_mutant_killed : check (refs false optional) bag = false ∧
    collapseMutant (refs false optional) bag = true := by decide
theorem upper_bound_mutant_killed : check (refs false optional) bag = false ∧
    upperBoundMutant (refs false optional) bag = true := by decide

def noOccurrences : Candidate 3 where
  size := 2
  root := 0
  head d x := (d == 0 && x == 0) || (d == 1 && x == 1)
  contains d p x := d == 1 && p == 0 && x == 1
  deref _ _ _ := false

theorem zero_accepts_empty : check (refs false ⟨0, .finite 0⟩) noOccurrences = true := by decide
theorem optional_accepts_empty : check (refs true optional) noOccurrences = true := by decide
theorem optional_accepts_one : check (refs true optional) collapsed = true := by decide

def twoParents : EffectiveCore 3 := {
  refs true one with family := { (refs true one).family with
    parent := fun d => if d = 0 then none else if d = 1 then some 0 else some 1
    multiplicity := fun d => if d = 1 then ⟨2, .finite 2⟩ else one } }

def sharedTarget : Candidate 3 where
  size := 5
  root := 0
  head d x := (d == 0 && x == 0) || (d == 1 && (x == 1 || x == 2)) ||
    (d == 2 && (x == 3 || x == 4))
  contains d p x := (d == 1 && p == 0 && (x == 1 || x == 2)) ||
    (d == 2 && ((p == 1 && x == 3) || (p == 2 && x == 4)))
  deref d x t := d == 2 && (x == 3 || x == 4) && t == 1

theorem set_shared_target_accepts : check twoParents sharedTarget = true := by decide

def multipleParents : Candidate 3 where
  size := 5
  root := 0
  head := sharedTarget.head
  contains d p x := sharedTarget.contains d p x || (d == 2 && p == 2 && x == 3)
  deref := sharedTarget.deref

def multipleTargets : Candidate 3 where
  size := 5
  root := 0
  head := sharedTarget.head
  contains := sharedTarget.contains
  deref d x t := sharedTarget.deref d x t || (d == 2 && x == 3 && t == 2)

theorem multiple_parents_typed : (realize multipleParents).Typed twoParents := by decide
theorem multiple_parents_rejected : check twoParents multipleParents = false := by decide
theorem multiple_targets_typed : (realize multipleTargets).Typed twoParents := by decide
theorem multiple_targets_rejected : check twoParents multipleTargets = false := by decide

def unusedChain : EffectiveCore 3 where
  family := {
    root := 0
    parent _ := none
    reference _ := .basic
    super d := if d = 2 then some 1 else none
    origin d := if d = 0 then .syntheticRoot else .user
    isAbstract d := d != 0
    name d := if d = 0 then "Sing" else "A"
    multiplicity _ := ⟨0, .finite 0⟩ }
  id d := ⟨d.val⟩
  group _ := unrestricted

def unusedCertificate : CoreCertificate 3 where
  parentRank _ := 0
  superRank d := d.val
  unused d := d != 0

def onlyRoot : Candidate 3 where
  size := 1
  root := 0
  head d _ := d == 0
  contains _ _ _ := false
  deref _ _ _ := false

theorem unused_chain_valid : unusedChain.WellFormed :=
  admitted_wellFormed _ unusedCertificate (by decide) (by decide)
theorem unused_chain_supported : unusedChain.Supported :=
  admitted_supported _ unusedCertificate (by decide)
theorem unused_chain_satisfies : StructuralSatisfies unusedChain (realize onlyRoot) :=
  (check_correct _ _ unused_chain_valid unused_chain_supported).mp (by decide)

theorem set_not_satisfies : ¬ StructuralSatisfies (refs true) (realize bag) := by
  intro h
  have hc := (checks_iff (refs true) bag).mpr h
  have hb : check (refs true) bag = true := decide_eq_true hc
  rw [set_rejects_repetition] at hb
  contradiction

theorem duplicate_membership : verify (refs false)
    {rawBag with members := (⟨0⟩, 10) :: rawBag.members} = .malformed .duplicateMembership := by decide
theorem missing_root : verify (refs false)
    {rawBag with root := 99} = .malformed .missingRoot := by decide

/-- Existing parent, declared child slot, but zero realized children. -/
def missingChild : Candidate 6 where
  size := 3
  root := 0
  head d x := (d == 0 && x == 0) || ((d == 1 || d == 2) && x != 0) ||
    (d == 3 && x == 1) || (d == 4 && x == 2)
  contains d p x := p == 0 && ((d == 3 && x == 1) || (d == 4 && x == 2))
  deref _ _ _ := false

def relaxedGroup : EffectiveCore 6 := {inheritance with group := fun _ => unrestricted}

theorem missing_child_group_rejected : check inheritance missingChild = false := by decide

theorem missing_child_locally_valid : (realize missingChild).LocalConditions inheritance := by
  have hc : check relaxedGroup missingChild = true := by decide
  have hs := (checks_iff relaxedGroup missingChild).mp (of_decide_eq_true hc)
  exact ((realize missingChild).structural_split relaxedGroup).mp hs |>.2.2

/-- Ordinary native assertions. These do not create fresh theorem certificates. -/
def executableTests : IO Unit := do
  let tests := [
    check (refs false) bag,
    !(check (refs false ⟨2, .finite 2⟩ ⟨2, .finite 2⟩) overlapping),
    !(check (refs true) bag),
    check inheritance nested,
    !(check inheritance nestedOverlap),
    decide (run (refs false) refCertificate rawOverlap = .candidate .violates),
    decide (run separateTrees treeCertificate treeOverlap = .candidate .violates),
    decide (run separateTrees treeCertificate distinctTrees = .candidate .satisfies),
    check inheritance emptyClasses,
    !(check inheritance missingChild),
    !(check inheritance siblingOverlap),
    !(check inheritance uncovered),
    check cyclic cycle,
    check twoParents sharedTarget,
    !(check twoParents multipleParents),
    !(check twoParents multipleTargets),
    check unusedChain onlyRoot,
    check (refs false ⟨0, .finite 0⟩) noOccurrences,
    check (refs true optional) noOccurrences,
    check (refs true optional) collapsed,
    !(check (refs false optional) bag) && collapseMutant (refs false optional) bag,
    !(check (refs false optional) bag) && upperBoundMutant (refs false optional) bag,
    check (refs false) bag != check (refs false) collapsed,
    check (refs false optional) bag != check (refs false unrestricted) bag,
    decide (verify (refs false) rawBag = .satisfies),
    decide (verify (refs false) { rawBag with references := [] } = .violates)]
  unless tests.all id do throw (IO.userError "structural checker regression")
  IO.println s!"{tests.length} structural checker assertions passed (including two killed mutants)"


end Clafer.Verification.Examples
