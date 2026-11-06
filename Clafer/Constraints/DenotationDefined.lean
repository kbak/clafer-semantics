module

public import Clafer.Constraints.DenotationLaws
public import Clafer.Constraints.IntegerNavigation

/-!
[proof->req~clafer-constraint-denotation~1]
[proof->req~clafer-constraint-environments~1]
[proof->req~clafer-constraint-semantic-laws~1]
-/

/-! # Structural definedness of numeric navigation

SoSyM Appendix 6 PDF p.34, D.3–D.4. Head multiplicities and total functional
references supply singleton operands. They do not imply the inequality.
-/

@[expose] public section
universe u w
namespace Clafer.Constraints
theorem Expr.Defined.not {s : Support} {U : Type u} {Γ}
    {m : IntegerBinding.{u,w} s U} {ρ : Environment s U Γ} {e : Expr s Γ .boolean}
    (h : e.Defined m ρ) : (Expr.not e).Defined m ρ := by
  obtain ⟨p,hp⟩ := h
  exact ⟨⟨¬p.down⟩,by simp [Expr.denote,hp]⟩

theorem Expr.Defined.and {s : Support} {U : Type u} {Γ}
    {m : IntegerBinding.{u,w} s U} {ρ : Environment s U Γ} {a b : Expr s Γ .boolean}
    (ha : a.Defined m ρ) (hb : b.Defined m ρ) : (Expr.and a b).Defined m ρ := by
  obtain ⟨p,hp⟩ := ha
  obtain ⟨q,hq⟩ := hb
  exact ⟨⟨p.down ∧ q.down⟩,by simp [Expr.denote,lift₂,hp,hq]⟩

theorem Expr.Defined.equal {s : Support} {U : Type u} {Γ t}
    {m : IntegerBinding.{u,w} s U} {ρ : Environment s U Γ} {a b : Expr s Γ t}
    (ha : a.Defined m ρ) (hb : b.Defined m ρ) : (Expr.equal a b).Defined m ρ := by
  obtain ⟨p,hp⟩ := ha
  obtain ⟨q,hq⟩ := hb
  exact ⟨⟨p = q⟩,by simp [Expr.denote,lift₂,hp,hq]⟩

theorem Expr.Defined.less {s : Support} {U : Type u} {Γ}
    {m : IntegerBinding.{u,w} s U} {ρ : Environment s U Γ} {a b : Expr s Γ .integer}
    (ha : a.Defined m ρ) (hb : b.Defined m ρ) : (Expr.less a b).Defined m ρ := by
  obtain ⟨p,hp⟩ := ha
  obtain ⟨q,hq⟩ := hb
  exact ⟨⟨p.down < q.down⟩,by simp [Expr.denote,lift₂,hp,hq]⟩

theorem Expr.Defined.implies {s : Support} {U : Type u} {Γ}
    {m : IntegerBinding.{u,w} s U} {ρ : Environment s U Γ} {a b : Expr s Γ .boolean}
    (ha : a.Defined m ρ) (hb : b.Defined m ρ) : (a.implies b).Defined m ρ :=
  (ha.and hb.not).not

theorem Expr.Defined.iff {s : Support} {U : Type u} {Γ}
    {m : IntegerBinding.{u,w} s U} {ρ : Environment s U Γ} {a b : Expr s Γ .boolean}
    (ha : a.Defined m ρ) (hb : b.Defined m ρ) : (a.iff b).Defined m ρ :=
  (ha.implies hb).and (hb.implies ha)

namespace VersionNavigation
variable {U : Type u} (m : Model.{u,w} U)
variable (d : Subtype (m.model.obj (0 : support.Vertex)))

/-- The general denotation follows the exact existing primitive bridge. -/
theorem denote_version {Γ} (ρ : Environment support U Γ)
    (a : Expr support Γ (.collection (.objects 2))) (S : Set U)
    (ha : a.denote m.toIntegerBinding ρ = Option.some S) :
    (version a).denote m.toIntegerBinding ρ =
      (m.realization.extract (m.versionObjects S)).map ULift.up := by
  simp only [version, Expr.denote, ha, lift₂, Option.bind_some, Option.map_some,
    Model.versionObjects]
  exact congrArg (fun T => (m.realization.extract T).map (ULift.up : Int → ULift.{u} Int))
    ((image_span (m.model.map (support.arrow 3)) _).trans
      (congrArg (navigationImage (m.model.map (support.arrow 3)))
        (image_span (m.model.map (support.arrow 2)) S)))

theorem denote_displayVersion :
    displayVersion.denote m.toIntegerBinding (Environment.closed d.val) =
      (m.realization.extract (m.versionObjects {d.val})).map ULift.up := by
  exact denote_version m _ _ _ rfl

theorem denote_serverVersion :
    serverVersion.denote m.toIntegerBinding (Environment.closed d.val) =
      (m.realization.extract (m.versionObjects (m.serverObjects d))).map ULift.up := by
  apply denote_version m
  simp only [Expr.denote, lift₂, Option.bind_some, Option.map_some, Model.serverObjects]
  exact congrArg Option.some
    ((image_span (m.model.map (support.arrow 5)) _).trans
      (congrArg (navigationImage (m.model.map (support.arrow 5)))
        (image_span (m.model.map (support.arrow 4)) {d.val})))

/-- Well-definedness is derived from the four source map obligations in Model;
no evaluator success, final singleton, or desired comparison is assumed. -/
theorem denotation_defined :
    comparison.Defined m.toIntegerBinding (Environment.closed d.val) := by
  obtain ⟨hd,hs⟩ := m.operands_defined d
  obtain ⟨i,hi⟩ := (m.realization.wellDefined_iff _).mp hd
  obtain ⟨j,hj⟩ := (m.realization.wellDefined_iff _).mp hs
  have ei := (m.realization.extract_eq_some_iff _ _).mpr hi
  have ej := (m.realization.extract_eq_some_iff _ _).mpr hj
  refine ⟨⟨j ≤ i⟩, ?_⟩
  simp [comparison, denote_displayVersion m d, denote_serverVersion m d, ei,ej,lift₂]

/-- Agreement with the independently delivered partial comparison of #67.
The proposition has its D.4 meaning even when the result is false. -/
theorem comparison_agrees (i j : Int)
    (hd : m.versionObjects {d.val} = {m.realization.encode i})
    (hs : m.versionObjects (m.serverObjects d) = {m.realization.encode j}) :
    comparison.denote m.toIntegerBinding (Environment.closed d.val) = Option.some ⟨j ≤ i⟩ := by
  simp [comparison, denote_displayVersion m d, denote_serverVersion m d,hd,hs,lift₂]

end VersionNavigation
end Clafer.Constraints
