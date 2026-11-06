module

public import Clafer.Constraints.DenotationInvariance

/-!
[proof->req~clafer-constraint-denotation~1]
[proof->req~clafer-constraint-environments~1]
[proof->req~clafer-constraint-semantic-laws~1]
-/

/-! # Independence from unobserved support occurrences

SoSyM D.2–D.4. Complete support graphs may contain isolated vertices and
unused maps. These footprints describe observations of denotation, not a
replacement for the full binding or its structural typing obligations.
-/

@[expose] public section
universe u w
namespace Clafer.Constraints

/-- Object extents read by a body (as opposed to endpoints used only for typing). -/
noncomputable def Expr.extents {s Γ t} (e : Expr s Γ t) : Set s.Vertex :=
  match e with
  | .extent x => {x}
  | .and a b | .equal a b | .less a b | .arithmetic _ a b
  | .setOp _ a b | .subset a b | .image a b | .join a b => a.extents ∪ b.extents
  | .not a | .integerOf _ a | .cardinality a | .widenObjects _ a
  | .widenRelation _ _ a => a.extents
  | .all _ _ a b => a.extents ∪ b.extents
  | _ => ∅

/-- Map occurrences read by a body; repeated occurrences need no deduplication
of the underlying model's original links. -/
noncomputable def Expr.maps {s Γ t} (e : Expr s Γ t) : Set s.Edge :=
  match e with
  | .map f => {f}
  | .and a b | .equal a b | .less a b | .arithmetic _ a b
  | .setOp _ a b | .subset a b | .image a b | .join a b => a.maps ∪ b.maps
  | .not a | .integerOf _ a | .cardinality a | .widenObjects _ a
  | .widenRelation _ _ a => a.maps
  | .all _ _ a b => a.maps ∪ b.maps
  | _ => ∅

/-- Changes to unobserved extents or maps leave the meaning unchanged.
The explicit environment and primitive realization remain fixed. -/
theorem Expr.denote_support_congr {s : Support} {U : Type u} {Γ t}
    (e : Expr s Γ t) (m n : IntegerBinding.{u,w} s U)
    (hR : m.realization = n.realization)
    (hV : ∀ x ∈ e.extents, m.model.obj x = n.model.obj x)
    (hE : ∀ f ∈ e.maps, ambientRelation (m.model.map (s.arrow f)) =
      ambientRelation (n.model.map (s.arrow f)))
    (ρ : Environment s U Γ) : e.denote m ρ = e.denote n ρ := by
  induction e with
  | extent x => exact congrArg Option.some (hV x (Set.mem_singleton x))
  | map f => exact congrArg Option.some (hE f (Set.mem_singleton f))
  | all b fresh domain body ihd ihb =>
    simp only [Expr.extents, Expr.maps, Set.forall_mem_union] at hV hE
    simp only [Expr.denote, ihd hV.1 hE.1]
    congr 1
    funext S
    congr 1
    funext x
    exact ihb hV.2 hE.2 _
  | _ =>
    simp only [Expr.extents, Expr.maps, Set.forall_mem_union] at hV hE
    simp_all [Expr.denote]

end Clafer.Constraints
