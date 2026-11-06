module

public import Clafer.Constraints.DenotationLaws

/-!
[impl->req~clafer-constraint-denotation~1]
[impl->req~clafer-constraint-environments~1]
[impl->req~clafer-constraint-semantic-laws~1]
[proof->req~clafer-constraint-denotation~1]
[proof->req~clafer-constraint-environments~1]
[proof->req~clafer-constraint-semantic-laws~1]
-/

/-! # Observable support and environment invariance

SoSyM D.2–D.4 and B.1. Display names and link labels cannot change
constraint meaning; complete supports may include unused occurrences.
-/

@[expose] public section
universe u w
namespace Clafer.Constraints

export DPGraph.Predicates (ambientRelation_iso)

/-- Equality of resolved map identity preserves the original link occurrences,
including their ambient endpoints, even across repeated support vertices. -/
structure LinkEquivalence {U : Type u} {A B C D : Set U}
    (q : DPGraph.Span.{u,u,max u w} A B) (r : DPGraph.Span.{u,u,max u w} C D) where
  equiv : q.Link ≃ r.Link
  source : ∀ l, (r.source (equiv l)).val = (q.source l).val
  target : ∀ l, (r.target (equiv l)).val = (q.target l).val

theorem LinkEquivalence.reduction {U : Type u} {A B C D : Set U}
    {q : DPGraph.Span.{u,u,max u w} A B} {r : DPGraph.Span.{u,u,max u w} C D}
    (h : LinkEquivalence q r) : ambientRelation q = ambientRelation r := by
  ext p
  constructor
  · rintro ⟨l,hs,ht⟩
    exact ⟨h.equiv l,(h.source l).trans hs,(h.target l).trans ht⟩
  · rintro ⟨l,hs,ht⟩
    refine ⟨h.equiv.symm l,?_,?_⟩
    · exact (h.source (h.equiv.symm l)).symm.trans (by simpa using hs)
    · exact (h.target (h.equiv.symm l)).symm.trans (by simpa using ht)

/-- Raw graph bindings become resolved model environments only when repeated
map identities agree on links as well as classes. Names remain irrelevant. -/
def IntegerBinding.Coherent {s : Support} {U : Type u} (m : IntegerBinding.{u,w} s U) : Prop :=
  ∀ e f, (s.mapRef e).owner = (s.mapRef f).owner →
    (s.mapRef e).kind = (s.mapRef f).kind →
    Nonempty (LinkEquivalence (m.model.map (s.arrow e)) (m.model.map (s.arrow f)))

theorem repeated_map_denotation {s : Support} {U : Type u} {Γ}
    (m : IntegerBinding.{u,w} s U) (h : m.Coherent) (ρ : Environment s U Γ)
    (e f : s.Edge) (ho : (s.mapRef e).owner = (s.mapRef f).owner)
    (hk : (s.mapRef e).kind = (s.mapRef f).kind) :
    (Expr.map e).denote m ρ = (Expr.map f).denote m ρ := by
  obtain ⟨he⟩ := h e f ho hk
  exact congrArg Option.some he.reduction

/-- Only the primitive realization and the support's observable object/relation
assignments enter the equations. Proofs of admissibility are not observations. -/
theorem Expr.denote_congr {s : Support} {U : Type u} {Γ t}
    (e : Expr s Γ t) (m n : IntegerBinding.{u,w} s U)
    (hR : m.realization = n.realization)
    (hV : ∀ x, m.model.obj x = n.model.obj x)
    (hE : ∀ f, ambientRelation (m.model.map (s.arrow f)) =
      ambientRelation (n.model.map (s.arrow f)))
    (ρ : Environment s U Γ) : e.denote m ρ = e.denote n ρ := by
  induction e with
  | all b fresh domain body ihd ihb =>
    simp only [Expr.denote, ihd]
    congr 1
    funext S
    congr 1
    funext x
    exact ihb _
  | _ => simp_all [Expr.denote]

/-- Extensional environment agreement is enough, even when the environments
carry distinct membership proofs or were built by different lexical extensions. -/
theorem Expr.environment_congr {s : Support} {U : Type u} {Γ t}
    (e : Expr s Γ t) (m : IntegerBinding.{u,w} s U)
    (ρ σ : Environment s U Γ) (hc : ρ.this = σ.this)
    (hv : ∀ x (v : Var Γ x), ρ.lookup v = σ.lookup v) :
    e.denote m ρ = e.denote m σ := by
  have he : ρ = σ := by
    apply Environment.ext hc
    funext x v
    exact hv x v
  exact congrArg (e.denote m) he

/-- Choosing another valid inheritance path changes only the typing witness. -/
theorem widening_path_irrelevant {s : Support} {U : Type u} {Γ x y}
    (m : IntegerBinding.{u,w} s U) (ρ : Environment s U Γ)
    (h k : Widen s x y) (a : Expr s Γ (.collection (.objects x))) :
    (Expr.widenObjects h a).denote m ρ = (Expr.widenObjects k a).denote m ρ := rfl

end Clafer.Constraints
