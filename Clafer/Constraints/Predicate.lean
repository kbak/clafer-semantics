module

public import Clafer.Constraints.DenotationInvariance

/-!
# Meanings of source-constraint symbols

SoSyM §6.2.2, Appendix D.4 and B.5. A predicate interprets its complete
support diagram and universally closes the explicitly supplied external domains.
The primitive realization is fixed independently of truth. Invalid support
diagrams, undefined operations and defined false bodies do not satisfy it.
-/

@[expose] public section
universe u w
namespace Clafer.Constraints
open CategoryTheory DPGraph DPGraph.Predicates

/-- Close external binders in their lexical order. An outer domain is evaluated
before its binder is introduced, exactly as for an authored `all` expression.
Domains are semantic input data; their mere existence in `Constraint.Input`
does not select a domain or authorize an arbitrary choice of one. -/
noncomputable def Domains.close {s : Support} {Γ : List (Local s)}
    (domains : Domains s Γ) (body : Expr s Γ .boolean) : Expr s [] .boolean :=
  match domains with
  | .nil => body
  | .cons b outer fresh domain => outer.close (.all b fresh domain body)

/-- An attached constraint is evaluated at every object of its enclosing class.
Empty context classes impose no body obligation. External domains are closed
explicitly; undefined domains are not silently treated as empty collections. -/
def Constraint.Holds (q : Constraint) (domains : Domains q.support q.locals)
    {U : Type u} (m : IntegerBinding.{u,w} q.support U) : Prop :=
  ∀ x, (m.model.obj q.support.context : Set U) x →
    (domains.close q.body).Holds m (Environment.closed x)

theorem IntegerBinding.ext {s : Support} {U : Type u}
    {m n : IntegerBinding.{u,w} s U}
    (hr : m.realization = n.realization) (hm : m.model = n.model) : m = n := by
  cases m
  cases n
  cases hr
  cases hm
  rfl

-- [impl->req~clafer-constraint-predicates~1]
/-- Each occurrence's meaning is derived from its typed body and domains.
The existential packages admissibility proofs for the supplied arity diagram;
it cannot choose different object sets, spans or an integer encoding. -/
noncomputable def predicateInterpretation {ι : Type} (qs : ι → Constraint)
    (domains : ∀ q, Domains (qs q).support (qs q).locals)
    {U : Type u} (R : IntegerRealization U) :
    Interpretation (signature qs) (semanticGraph.{u,w} U) where
  meaning q diagram := ∃ m : IntegerBinding (qs q).support U,
    m.realization = R ∧ m.model = diagram ∧ m.Coherent ∧
      (qs q).Holds (domains q) m

/-- Arity interpretation is exactly independently defined source truth when
the full diagram has the stated resolved identities and primitive realization. -/
theorem predicate_meaning_iff {ι : Type} (qs : ι → Constraint)
    (domains : ∀ q, Domains (qs q).support (qs q).locals)
    {U : Type u} (R : IntegerRealization U) (q : ι)
    (m : IntegerBinding.{u,w} (qs q).support U)
    (hr : m.realization = R) (hc : m.Coherent) :
    m.model ∈ (predicateInterpretation qs domains R).meaning q ↔
      (qs q).Holds (domains q) m := by
  constructor
  · rintro ⟨n, hn, hm, _, ht⟩
    have he : n = m := IntegerBinding.ext (hn.trans hr.symm) hm
    simpa only [he] using ht
  · intro h
    exact ⟨m, hr, rfl, hc, h⟩

-- [proof->req~clafer-constraint-predicates~1]
theorem closed_constraint_iff (s : Support) {U : Type u}
    (body : Expr s [] .boolean) (m : IntegerBinding.{u,w} s U) :
    (Constraint.mk s [] body).Holds .nil m ↔
      ∀ x, (m.model.obj s.context : Set U) x → body.Holds m (Environment.closed x) := Iff.rfl

end Clafer.Constraints
