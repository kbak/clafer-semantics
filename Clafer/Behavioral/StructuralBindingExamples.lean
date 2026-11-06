module

public import Clafer.Behavioral.StructuralBinding
public import Clafer.Behavioral.StructuralExamples

/-! Resolved support over the fully admitted S6/inherited-reference fixture.
Every map kind is exercised, including repeated dereference occurrences and a
target map whose equal endpoints still have two distinct intermediate heads. -/

@[expose] public section
namespace Clafer.Behavioral.StructuralBindingExamples
open Constraints StructuralBinding StructuralExamples

abbrev support : Support where
  classCount := 8
  mapCount := 6
  classId d := ⟨d.val⟩
  mapRef e := match e.val with
    | 0 => ⟨⟨5⟩, .head, 3, 5, "head"⟩
    | 1 => ⟨⟨5⟩, .parent, 5, 3, "parent"⟩
    | 2 => ⟨⟨5⟩, .dereference, 5, 6, "dref"⟩
    | 3 => ⟨⟨5⟩, .target, 3, 6, "target"⟩
    | 4 => ⟨⟨5⟩, .inclusion, 5, 7, "super"⟩
    | _ => ⟨⟨5⟩, .dereference, 5, 6, "dref"⟩
  context := 5

def resolved (t : Nat) : Resolution (model false false) (trace false) t support :=
  .ofRoles _ _ _ (admitted false false).2 id (fun _ => 5) (fun _ => rfl)
    (by intro e; fin_cases e <;> rfl) (by
      intro e
      fin_cases e
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, 7, inherited_owner, rfl⟩
      · exact ⟨rfl, 7, inherited_owner, rfl⟩
      · exact ⟨rfl, Relation.ReflTransGen.single (by rfl)⟩
      · exact ⟨rfl, 7, inherited_owner, rfl⟩)

-- [utest->req~behavioral-reference-atoms~1]
theorem inherited_dereference (t : Nat) :
    ambientRelation ((resolved t).map (support.arrow 2)) =
      {p | InheritedReference.deref (model false false).family
        ((trace false).raw (model false false).toEffectiveCore t) 5 p.1 p.2} :=
  (resolved t).dereference_relation 2 rfl

theorem repeated_occurrence (t : Nat) :
    (resolved t).map (support.arrow 2) = (resolved t).map (support.arrow 5) := rfl

def firstTarget : Link (model false false) (trace false) 0 5 .target :=
  ⟨⟨2, 3, 5⟩, ⟨⟨trivial, trivial, rfl⟩, .refl, by decide⟩, inherited_bag_changes_target.1⟩

def secondTarget : Link (model false false) (trace false) 0 5 .target :=
  ⟨⟨2, 4, 5⟩, ⟨⟨trivial, trivial, rfl⟩, .refl, by decide⟩, inherited_bag_changes_target.2.1⟩

-- [utest->req~behavioral-reference-atoms~1]
theorem target_links_not_collapsed :
    firstTarget ≠ secondTarget ∧
    ((resolved 0).map (support.arrow 3)).source firstTarget =
      ((resolved 0).map (support.arrow 3)).source secondTarget ∧
    ((resolved 0).map (support.arrow 3)).target firstTarget =
      ((resolved 0).map (support.arrow 3)).target secondTarget := by
  refine ⟨?_, rfl, rfl⟩
  intro h
  have h := congrArg (fun l => l.val.2.1) h
  contradiction

theorem explicit_deref_changes :
    (3, 5) ∈ ambientRelation ((resolved 0).map (support.arrow 2)) ∧
    (3, 6) ∈ ambientRelation ((resolved 1).map (support.arrow 2)) := by
  rw [inherited_dereference, inherited_dereference]
  exact ⟨inherited_bag_changes_target.1, inherited_bag_changes_target.2.2.1⟩

theorem inclusion_valid (t : Nat) :
    DPGraph.Predicates.Inclusion ((resolved t).map (support.arrow 4)) :=
  (resolved t).inclusion 4 rfl

end Clafer.Behavioral.StructuralBindingExamples
