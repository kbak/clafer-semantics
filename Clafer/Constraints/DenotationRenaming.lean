module

public import Clafer.Constraints.DenotationInvariance

/-! # Lexical alpha-renaming

SoSyM D.2–D.4: binder names are metadata; positions, fresh IDs and
singleton objects retain their meaning when display names change.
-/

@[expose] public section
universe u w
namespace Clafer.Constraints

abbrev Local.rename {s : Support} (f : String → String) (b : Local s) : Local s :=
  {b with name := f b.name}

noncomputable def Var.rename {s Γ x} (f : String → String) (v : @Var s Γ x) :
    Var (Γ.map (Local.rename f)) x := by
  induction v with
  | here => exact .here
  | there _ ih => exact .there ih

/-- Every new lexical position still denotes the original singleton. -/
noncomputable def Environment.rename {s U Γ} (f : String → String)
    (ρ : Environment s U Γ) : Environment s U (Γ.map (Local.rename f)) where
  this := ρ.this
  lookup := fun {x} v => ρ.lookup (back Γ x v)
where
  back (Γ : List (Local s)) (x : s.Vertex) (v : Var (Γ.map (Local.rename f)) x) : Var Γ x :=
    match Γ, v with
    | _ :: _, .here => .here
    | _ :: bs, .there w => .there (back bs _ w)

noncomputable def Expr.rename {s Γ t} (f : String → String) (e : Expr s Γ t) :
    Expr s (Γ.map (Local.rename f)) t :=
  match e with
  | .boolean b => .boolean b
  | .integer n => .integer n
  | .empty k => .empty k
  | .this => .this
  | .extent x => .extent x
  | .var v => .var (v.rename f)
  | .map k => .map k
  | .and a b => .and (a.rename f) (b.rename f)
  | .not a => .not (a.rename f)
  | .equal a b => .equal (a.rename f) (b.rename f)
  | .less a b => .less (a.rename f) (b.rename f)
  | .arithmetic op a b => .arithmetic op (a.rename f) (b.rename f)
  | .integerOf h a => .integerOf h (a.rename f)
  | .cardinality a => .cardinality (a.rename f)
  | .setOp op a b => .setOp op (a.rename f) (b.rename f)
  | .subset a b => .subset (a.rename f) (b.rename f)
  | .image a b => .image (a.rename f) (b.rename f)
  | .join a b => .join (a.rename f) (b.rename f)
  | .widenObjects h a => .widenObjects h (a.rename f)
  | .widenRelation h k a => .widenRelation h k (a.rename f)
  | .all b fresh domain body => .all (b.rename f)
      (by
        intro old hold
        obtain ⟨previous,hprevious,rfl⟩ := List.mem_map.mp hold
        exact fresh previous hprevious)
      (domain.rename f) (body.rename f)

-- [proof->req~clafer-constraint-environments~1]
theorem Environment.rename_lookup {s U Γ x} (f : String → String)
    (ρ : Environment s U Γ) (v : Var Γ x) :
    (ρ.rename f).lookup (v.rename f) = ρ.lookup v := by
  have h : Environment.rename.back f Γ x (v.rename f) = v := by
    clear ρ
    induction v with
    | here => rfl
    | @there b Γ x v ih =>
      exact congrArg (@Var.there s b Γ x) ih
  exact congrArg ρ.lookup h

theorem Environment.rename_push {s U Γ} (f : String → String)
    (ρ : Environment s U Γ) (b : Local s) (x : U) :
    (ρ.push b x).rename f = (ρ.rename f).push (b.rename f) x := by
  apply Environment.ext
  · rfl
  · funext y v
    cases v <;> rfl

-- [proof->req~clafer-constraint-denotation~1]
-- [proof->req~clafer-constraint-semantic-laws~1]
/-- All constructors, including nested shadowing, preserve meaning under
arbitrary display-name changes. IDs and domain types remain fixed. -/
theorem Expr.denote_rename {s U Γ t} (f : String → String) (e : Expr s Γ t)
    (m : IntegerBinding.{u,w} s U) (ρ : Environment s U Γ) :
    (e.rename f).denote m (ρ.rename f) = e.denote m ρ := by
  induction e with
  | var v => simp [Expr.rename,Expr.denote,Environment.rename_lookup]
  | extent _ => rfl
  | arithmetic op a b iha ihb =>
    simp_all [Expr.rename,Expr.denote,Environment.rename]
    rfl
  | all b fresh domain body ihd ihb =>
    simp only [Expr.rename,Expr.denote]
    rw [ihd ρ]
    congr 1
    funext S
    congr 1
    funext x
    rw [← Environment.rename_push]
    exact ihb _
  | _ => simp_all [Expr.rename,Expr.denote,Environment.rename]

end Clafer.Constraints
