module

public import Clafer.Behavioral.Environment
public import Clafer.Constraints.Denotation

/-! # Static expressions in captured environments

SoSyM Appendix 4/§6.2.2, behavioral §5 expressions, and accepted D1.
The binding is supplied at the observation time. Lexical variables retain sets;
quantifiers capture singleton identities after evaluating the domain. Static
agreement holds for live `this` and singleton-compatible environments; typing
admissibility remains explicit. Undefined primitive results are never Booleanized.
-/

@[expose] public section
namespace Clafer.Behavioral.CapturedStatic
open Constraints
universe u w

variable {s : Support} {U : Type u}

def Compatible {Γ : List (Local s)} (ρ : Behavioral.Environment U Γ.length)
    (σ : Constraints.Environment s U Γ) : Prop :=
  ρ.this = σ.this ∧ ∀ x (v : Var Γ x), ρ.lookup ⟨v.index, v.index_lt⟩ = {σ.lookup v}

/-- Every static environment has a concrete singleton capture. -/
noncomputable def capture : {Γ : List (Local s)} → Constraints.Environment s U Γ →
    Behavioral.Environment U Γ.length
  | [], σ => .closed σ.this
  | _ :: _, σ => (capture ⟨σ.this, fun v => σ.lookup (.there v)⟩).push {σ.lookup .here}

-- [proof->req~behavioral-reference-atoms~1]
theorem capture_compatible {Γ : List (Local s)} (σ : Constraints.Environment s U Γ) :
    Compatible (capture σ) σ := by
  induction Γ with
  | nil => exact ⟨rfl, fun _ v => nomatch v⟩
  | cons b Γ ih =>
    have h := ih (⟨σ.this, fun v => σ.lookup (.there v)⟩ : Constraints.Environment s U Γ)
    refine ⟨h.1, ?_⟩
    intro x v
    cases v with
    | here => rfl
    | there v => exact h.2 _ v

-- [proof->req~behavioral-reference-atoms~1]
theorem compatible_push {Γ : List (Local s)} {ρ : Behavioral.Environment U Γ.length}
    {σ : Constraints.Environment s U Γ} (h : Compatible ρ σ) (b : Local s) (x : U) :
    Compatible (ρ.push {x}) (σ.push b x) := by
  refine ⟨h.1, ?_⟩
  intro c v
  cases v with
  | here => rfl
  | there v => exact h.2 _ v

-- [impl->req~behavioral-reference-atoms~1]
noncomputable def eval (live : Set U) (m : IntegerBinding.{u,w} s U)
    {Γ t} (e : Expr s Γ t) (ρ : Behavioral.Environment U Γ.length) : Option (Value U t) :=
  match e with
  | .boolean b => some ⟨b = true⟩
  | .integer i => some ⟨i⟩
  | .empty _ => some ∅
  | .this => some {x | x = ρ.this ∧ x ∈ live}
  | .extent d => some (m.model.obj d)
  | .var v => some (ρ.lookup ⟨v.index, v.index_lt⟩)
  | .map f => some (ambientRelation (m.model.map (s.arrow f)))
  | .and a b => lift₂ (fun p q => ⟨p.down ∧ q.down⟩) (eval live m a ρ) (eval live m b ρ)
  | .not a => (eval live m a ρ).map (fun p => ⟨¬ p.down⟩)
  | .equal a b => lift₂ (fun p q => ⟨p = q⟩) (eval live m a ρ) (eval live m b ρ)
  | .less a b => lift₂ (fun p q => ⟨p.down < q.down⟩) (eval live m a ρ) (eval live m b ρ)
  | .arithmetic op a b => lift₂ (fun p q => ⟨match op with
      | .add => p.down + q.down | .subtract => p.down - q.down⟩) (eval live m a ρ) (eval live m b ρ)
  | .integerOf _ a => (eval live m a ρ).bind (fun S => (m.realization.extract S).map ULift.up)
  | .cardinality a => (eval live m a ρ).bind finiteCard
  | .setOp op a b => lift₂ (collectionOp op) (eval live m a ρ) (eval live m b ρ)
  | .subset a b => lift₂ (fun S T => ⟨S ⊆ T⟩) (eval live m a ρ) (eval live m b ρ)
  | .image a b => lift₂ relationalImage (eval live m a ρ) (eval live m b ρ)
  | .join a b => lift₂ relationalJoin (eval live m a ρ) (eval live m b ρ)
  | .widenObjects _ a => let result := eval live m a ρ; result
  | .widenRelation _ _ a => let result := eval live m a ρ; result
  | .all _ _ domain body => (eval live m domain ρ).bind
      (fun S => universal S (fun x => eval live m body (ρ.push {x})))

-- [proof->req~behavioral-reference-atoms~1]
/-- All constructors, including partial values and quantified bodies. Captured
sets of multiple identities are outside the singleton static environment domain. -/
theorem agrees (live : Set U) (m : IntegerBinding.{u,w} s U) {Γ t} (e : Expr s Γ t)
    (ρ : Behavioral.Environment U Γ.length) (σ : Constraints.Environment s U Γ)
    (same : Compatible ρ σ) (present : ρ.this ∈ live) :
    eval live m e ρ = e.denote m σ := by
  induction e with
  | this =>
    change some {x | x = ρ.this ∧ x ∈ live} = some {σ.this}
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    rw [← same.1]
    exact ⟨And.left, fun he => ⟨he, he ▸ present⟩⟩
  | var v => exact congrArg some (same.2 _ v)
  | all b fresh domain body ihd ihb =>
    simp only [eval, Expr.denote, ihd ρ σ same present]
    congr 1
    funext S
    congr 1
    funext x
    exact ihb (ρ.push {x}) (σ.push b x) (compatible_push same b x) present
  | and a b iha ihb | equal a b iha ihb | less a b iha ihb
  | subset a b iha ihb | image a b iha ihb | join a b iha ihb =>
    simp only [eval, Expr.denote, iha ρ σ same present, ihb ρ σ same present]
  | arithmetic op a b iha ihb =>
    simp only [eval, Expr.denote, iha ρ σ same present, ihb ρ σ same present]
    cases op <;> rfl
  | setOp op a b iha ihb =>
    simp only [eval, Expr.denote, iha ρ σ same present, ihb ρ σ same present]
  | not a ih | cardinality a ih =>
    simp only [eval, Expr.denote, ih ρ σ same present]
  | integerOf p a ih | widenObjects p a ih =>
    simp only [eval, Expr.denote, ih ρ σ same present]
  | widenRelation p q a ih =>
    simp only [eval, Expr.denote, ih ρ σ same present]
  | _ => rfl

theorem defined_iff (live : Set U) (m : IntegerBinding.{u,w} s U) {Γ t} (e : Expr s Γ t)
    (ρ : Behavioral.Environment U Γ.length) (σ : Constraints.Environment s U Γ)
    (same : Compatible ρ σ) (present : ρ.this ∈ live) :
    (∃ v, eval live m e ρ = some v) ↔ e.Defined m σ := by
  rw [agrees live m e ρ σ same present]
  rfl

/-- Runtime typing is required separately; agreement alone is valid even for
raw singleton environments and must not be advertised as a typing theorem. -/
theorem admissible_push {Γ : List (Local s)} (m : IntegerBinding.{u,w} s U)
    (ρ : Behavioral.Environment U Γ.length) (σ : Constraints.Environment s U Γ)
    (same : Compatible ρ σ) (typed : σ.Admissible m) (b : Local s) {x : U}
    (member : (m.model.obj b.element : Set U) x) :
    Compatible (ρ.push {x}) (σ.push b x) ∧ (σ.push b x).Admissible m :=
  ⟨compatible_push same b x, Constraints.Environment.push_admissible typed b member⟩

theorem quantifier_domain_first (live : Set U) (m : IntegerBinding.{u,w} s U)
    {Γ : List (Local s)} (b : Local s) (fresh : ∀ old ∈ Γ, old.id ≠ b.id)
    (domain : Expr s Γ (.collection (.objects b.element)))
    (body : Expr s (b :: Γ) .boolean) (ρ : Behavioral.Environment U Γ.length) :
    eval live m (.all b fresh domain body) ρ =
      (eval live m domain ρ).bind (fun S => universal S (fun x => eval live m body (ρ.push {x}))) := rfl

-- [proof->req~behavioral-reference-atoms~1]
theorem undefined_negation (live : Set U) (m : IntegerBinding.{u,w} s U)
    {Γ : List (Local s)} (e : Expr s Γ .boolean) (ρ : Behavioral.Environment U Γ.length)
    (missing : eval live m e ρ = none) : eval live m (.not e) ρ = none := by
  simp only [eval, missing, Option.map_none]

end Clafer.Behavioral.CapturedStatic
