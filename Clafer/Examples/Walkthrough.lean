module

public import Clafer.Verification.Admission

/-!
[impl->req~lean-walkthrough~1]
[proof->req~lean-walkthrough~1]
-/

/-!
# A phone with an optional camera

Small manually resolved example for docs/getting-started.md. Nesting and local
cardinality follow SoSyM §5.3–5.5 and §6.2.2–5 through the existing effective-core
contract. This file does not parse Clafer text or introduce a new semantics.
-/

@[expose] public section
namespace Clafer.Examples.Walkthrough
open Semantics Verification DPGraph.Predicates

/-- Declaration IDs: 0 = synthetic root, 1 = phone, 2 = camera. -/
def model : EffectiveCore 3 where
  family := {
    root := 0
    parent := fun d => if d = 0 then none else if d = 1 then some 0 else some 1
    reference := fun _ => .basic
    super := fun _ => none
    origin := fun d => if d = 0 then .syntheticRoot else .user
    isAbstract := fun _ => false
    name := fun d => if d = 0 then "Sing" else if d = 1 then "phone" else "camera"
    multiplicity := fun d => if d = 2 then optional else one }
  id d := ⟨d.val⟩
  group _ := unrestricted

def certificate : CoreCertificate 3 where
  parentRank d := d.val
  superRank _ := 0
  unused _ := false

theorem model_valid : model.WellFormed :=
  admitted_wellFormed _ certificate (by decide) (by decide)

theorem model_supported : model.Supported :=
  admitted_supported _ certificate (by decide)

/-- Object IDs 0 and 1 denote the root and phone; each later ID is a camera. -/
def configuration (cameras : Nat) : Candidate 3 where
  size := cameras + 2
  root := ⟨0, by omega⟩
  head d x := (d == 0 && x.val == 0) || (d == 1 && x.val == 1) ||
    (d == 2 && x.val >= 2)
  contains d p x := (d == 1 && p.val == 0 && x.val == 1) ||
    (d == 2 && p.val == 1 && x.val >= 2)
  deref _ _ _ := false

theorem accepts_no_camera : check model (configuration 0) = true := by decide
theorem accepts_one_camera : check model (configuration 1) = true := by decide
theorem rejects_two_cameras : check model (configuration 2) = false := by decide

theorem no_camera_satisfies : StructuralSatisfies model (realize (configuration 0)) :=
  (check_correct _ _ model_valid model_supported).mp accepts_no_camera

theorem one_camera_satisfies : StructuralSatisfies model (realize (configuration 1)) :=
  (check_correct _ _ model_valid model_supported).mp accepts_one_camera

theorem two_cameras_violate : ¬ StructuralSatisfies model (realize (configuration 2)) := by
  intro h
  have accepted := (check_correct _ _ model_valid model_supported).mpr h
  rw [rejects_two_cameras] at accepted
  contradiction

end Clafer.Examples.Walkthrough
