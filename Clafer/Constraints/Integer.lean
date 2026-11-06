module

public import Clafer.Constraints.Typing
public import FormalCD.Integer
public import DPGraph.Predicates.Navigation

/-!
[impl->req~clafer-integer-extraction~1]
[proof->req~clafer-integer-extraction~1]
-/

/-!
# Integer operands from navigation

SoSyM D.3–D.4 and Appendix 6, PDF p.34. This supplies the partial meaning of
`Expr.integerOf`, for the relational set result of navigation. It does not
interpret other expressions or use the special Figure 21 VC predicate.
The realization embeds all mathematical integers; no bit width is imposed.
-/

@[expose] public section
universe u w
namespace Clafer.Constraints
open CategoryTheory DPGraph.Predicates

export FormalCD (IntegerRealization)

namespace IntegerRealization
export FormalCD.IntegerRealization (Extracts WellDefined encode_decode extracts_unique
  wellDefined_iff extract extract_eq_some_iff extract_none_iff extract_encoded extract_empty
  extract_multiple extract_wrong_domain objectEquiv)
end IntegerRealization

/-- A semantic support binding preserves resolved identities and actual inheritance
inclusions. Only vertices explicitly marked integer receive this realization. -/
structure IntegerBinding (s : Support) (U : Type u) where
  realization : IntegerRealization U
  model : s.graph ⥤q semanticGraph.{u,w} U
  same_id : ∀ x y, s.classId x = s.classId y → model.obj x = model.obj y
  inclusion : ∀ e, (s.mapRef e).kind = .inclusion → Inclusion (model.map (s.arrow e))
  integer_domain : ∀ x, s.integer x = true → model.obj x = realization.domain

/-- Widening changes class membership evidence and preserves ambient objects. -/
theorem IntegerBinding.widen_subset {s U} (b : IntegerBinding.{u,w} s U)
    {x y} (h : Widen s x y) : Set.Subset (b.model.obj x) (b.model.obj y) := by
  induction h with
  | same he => exact (b.same_id _ _ he) ▸ Set.Subset.refl _
  | inclusion e he => exact inclusion_subset (b.inclusion e he)
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

/-- A typed integer collection supplies the domain hypothesis, not uniqueness. -/
theorem IntegerBinding.singleton_defined {s U} (b : IntegerBinding.{u,w} s U)
    {v} (primitive : s.integer v = true) {x : U} (hx : (b.model.obj v : Set U) x) :
    b.realization.extract {x} = some (b.realization.decode x) := by
  apply (b.realization.extract_eq_some_iff _ _).mpr
  exact congrArg (fun z : U => ({z} : Set U)) (b.realization.encode_decode ((b.integer_domain v primitive) ▸ hx)).symm

export DPGraph.Predicates (navigationImage navigationImage_empty navigationImage_subset
  navigationImage_singleton navigationImage_one function_one navigationImage_function)

end Clafer.Constraints
