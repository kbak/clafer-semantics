module

public import Clafer.Constraints.DenotationExamples

/-! # Distinct support occurrences of the same resolved maps

SoSyM D.2–D.4, §6.2.2. Duplicate graph occurrences retain the very same
span link carriers. They do not duplicate elements of a set-valued expression.
-/

@[expose] public section
namespace Clafer.Constraints.RepeatedDenotation
open IntegerExamples VersionNavigation

abbrev duplicatedSupport : Support :=
  {support with mapCount := 2, mapRef := fun _ => support.mapRef 4}

abbrev original := (IntegerExamples.model 2 3).toIntegerBinding

def model : IntegerBinding duplicatedSupport U where
  realization := original.realization
  model := {
    obj := original.model.obj
    map := by
      rintro x y ⟨_,hs,ht⟩
      subst x; subst y
      exact original.model.map (support.arrow 4) }
  same_id := original.same_id
  inclusion := by intro i hi; cases hi
  integer_domain := original.integer_domain

/-- Edges 0 and 1 are different occurrences of the same server-head map. -/
theorem distinct_occurrences : (0 : duplicatedSupport.Edge) ≠ 1 := by decide

theorem same_resolved_identity :
    duplicatedSupport.mapRef 0 = duplicatedSupport.mapRef 1 := rfl

theorem same_links : Nonempty (LinkEquivalence
    (model.model.map (duplicatedSupport.arrow 0))
    (model.model.map (duplicatedSupport.arrow 1))) :=
  ⟨⟨Equiv.refl _,fun _ => rfl,fun _ => rfl⟩⟩

-- [proof->req~clafer-appendix-f-expressions~1]
theorem repeated_meaning :
    (Expr.map 0 : Expr duplicatedSupport [] _).denote model (.closed display.val) =
      (Expr.map 1 : Expr duplicatedSupport [] _).denote model (.closed display.val) := rfl

-- [proof->req~clafer-constraint-semantic-laws~1]
theorem repeated_union :
    (Expr.setOp .union
      (Expr.map 0 : Expr duplicatedSupport [] (.collection (.relation 0 4)))
      (Expr.map 1 : Expr duplicatedSupport [] (.collection (.relation 0 4)))).denote
      model (.closed display.val) =
    (Expr.map 0 : Expr duplicatedSupport [] _).denote model (.closed display.val) := by
  change some (collectionOp .union
    (ambientRelation (original.model.map (support.arrow 4)))
    (ambientRelation (original.model.map (support.arrow 4)))) = _
  simp [collectionOp,Expr.denote]
  rfl

end Clafer.Constraints.RepeatedDenotation
