module

public import Clafer.Semantics.Realization
public import Clafer.Verification.Finite

-- [proof->req~clafer-inherited-realization~1]

/-! # Compatibility with #50's supported structural checker

The guarded fragment has no inherited field bodies. In that fragment the two
abstract classifications coincide, and the inherited union reduces to own heads.
Both relations require #87 declaration disjointness; their admitted fragment
and effective-core erasure coincide.
-/

@[expose] public section
namespace Clafer.Semantics.Realization
open Compile MCS DPGraph.Predicates
variable {n : Nat} {U : Type} (m : Core n) (s : Configuration (Fin n) U)

theorem strict_ancestor_abstract (supported : m.toEffectiveCore.Supported)
    {p a : Fin n} (path : Compile.Groups.Ancestor m.family p a) (hne : a ≠ p) :
    m.family.isAbstract a = true := by
  cases path with
  | refl => exact (hne rfl).elim
  | tail path edge => exact (supported.2.2.1 _ _ edge).1

theorem guarded_groups (supported : m.toEffectiveCore.Supported)
    (flags : m.explicitAbstract = m.family.isAbstract)
    (bounds : ∀ d, m.group d = (m.family.group d).effective.range) :
    Groups m s ↔ s.Groups m.toEffectiveCore := by
  have fibers (d : Fin n) (x y : U) :
      Compile.Groups.ChildObjects m.family s d x y ↔ s.Child m.toEffectiveCore d x y := by
    apply Compile.Groups.direct_child_iff m.toEffectiveCore s d
    intro a path hne c
    exact (supported.2.1 a (strict_ancestor_abstract m supported path hne)).2.2.1 c
  unfold Groups Configuration.Groups Compile.Groups.Holds
  simp only [flags, bounds]
  apply forall_congr'
  intro d
  apply imp_congr_right
  intro _
  constructor
  · intro h x hx
    exact (inRange_iff _ (Equiv.subtypeEquivRight (fun y => fibers d x y))).mp (h ⟨x,hx⟩)
  · intro h x
    exact (inRange_iff _ (Equiv.subtypeEquivRight (fun y => fibers d x.val y))).mpr (h x.val x.property)

theorem guarded_flags (selected : m.Selected) (supported : m.toEffectiveCore.Supported) :
    m.explicitAbstract = m.family.isAbstract := by
  funext d
  cases ha : m.family.isAbstract d with
  | true => exact selected.2.1 d (supported.2.1 d ha).1 ha
  | false =>
    cases he : m.explicitAbstract d with
    | false => rfl
    | true => have hh := (selected.1 d he).1; simp [ha] at hh

/-- Explicit metadata equality, not a caller-supplied satisfaction equivalence.
For an AST the extension reads its original authored flag; #50 has no such data. -/
theorem guarded_compatibility (supported : m.toEffectiveCore.Supported)
    (flags : m.explicitAbstract = m.family.isAbstract)
    (bounds : ∀ d, m.group d = (m.family.group d).effective.range) :
    Satisfies m s ↔ StructuralSatisfies m.toEffectiveCore s := by
  have ha : Abstracts m s ↔ s.Abstracts m.toEffectiveCore := by
    simp only [Abstracts, Configuration.Abstracts, flags]
  rw [Satisfies, guarded_groups m s supported flags bounds, ha]
  unfold StructuralSatisfies Configuration.LocalConditions
  tauto

/-- For a selected AST projection, compatibility needs no supplied flag equality. -/
theorem supported_input_compatibility {a : AST} (i : Input a)
    (selected : (Core.ofInput i).Selected) (supported : (EffectiveCore.erase i).Supported)
    (s : Configuration a.Occurrence U) :
    Satisfies (Core.ofInput i) s ↔ StructuralSatisfies (EffectiveCore.erase i) s :=
  guarded_compatibility _ s supported (guarded_flags _ selected supported) (fun _ => rfl)

theorem supported_checker_compatibility {a : AST} (i : Input a)
    (selected : (Core.ofInput i).Selected) (supported : (EffectiveCore.erase i).Supported)
    (c : Verification.Candidate a.entries.length) :
    Verification.check (EffectiveCore.erase i) c = true ↔
      Satisfies (Core.ofInput i) (Verification.realize c) :=
  (Verification.check_correct _ c (EffectiveCore.erase_wellFormed i) supported).trans
    (supported_input_compatibility i selected supported _).symm

end Clafer.Semantics.Realization
