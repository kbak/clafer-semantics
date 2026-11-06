module

public import Clafer.Constraints.Integer
public import Mathlib.Data.Set.Card

/-!
# Independent meaning of resolved constraints

SoSyM D.1–D.4/Figure 28, with Q3 ordinary intersection. These are
mathematical, partial denotations over sets, not a finite-search evaluator.
The only partial operations are finite cardinality and integer extraction;
undefined operands propagate, including inside a nonempty quantifier domain.
-/

@[expose] public section
universe u w
namespace Clafer.Constraints

/-- Unary and binary collections have different ambient element types. -/
abbrev Collection.Carrier {s : Support} (U : Type u) : Collection s → Type u
  | .objects _ => U
  | .relation _ _ => U × U

abbrev Value {s : Support} (U : Type u) : Ty s → Type u
  | .boolean => ULift.{u} Prop
  | .integer => ULift.{u} Int
  | .collection k => Set (k.Carrier U)

/-- Positions select individual objects. Neither a name nor a set can be stored
as the value of a bound variable. Membership is an independent admissibility
condition, so the equations remain meaningful on raw environments too. -/
@[ext] structure Environment (s : Support) (U : Type u) (Γ : List (Local s)) where
  this : U
  lookup : ∀ {x}, Var Γ x → U

namespace Environment

def push {s U Γ} (ρ : Environment s U Γ) (b : Local s) (x : U) :
    Environment s U (b :: Γ) where
  this := ρ.this
  lookup := fun v => match v with
    | .here => x
    | .there v => ρ.lookup v

def closed {s U} (x : U) : Environment s U [] := ⟨x, fun v => nomatch v⟩

def Admissible {s U Γ} (ρ : Environment s U Γ) (b : IntegerBinding.{u,w} s U) : Prop :=
  (b.model.obj s.context : Set U) ρ.this ∧ ∀ x (v : Var Γ x), (b.model.obj x : Set U) (ρ.lookup v)

theorem push_admissible {s U Γ} {ρ : Environment s U Γ}
    {m : IntegerBinding.{u,w} s U} (h : ρ.Admissible m) (b : Local s)
    {x : U} (hx : (m.model.obj b.element : Set U) x) : (ρ.push b x).Admissible m := by
  refine ⟨h.1, ?_⟩
  intro y v
  cases v with
  | here => exact hx
  | there v => exact h.2 _ v

@[simp] theorem push_this {s U Γ} (ρ : Environment s U Γ) (b : Local s) (x : U) :
    (ρ.push b x).this = ρ.this := rfl

@[simp] theorem push_here {s U Γ} (ρ : Environment s U Γ) (b : Local s) (x : U) :
    (ρ.push b x).lookup .here = x := rfl

@[simp] theorem push_there {s U Γ} (ρ : Environment s U Γ) (b : Local s) (x : U)
    {y} (v : Var Γ y) : (ρ.push b x).lookup (.there v) = ρ.lookup v := rfl

end Environment

export DPGraph.Predicates (ambientRelation relationalImage relationalJoin image_span join_span)

def collectionOp {A : Type u} : SetOp → Set A → Set A → Set A
  | .union, a, b => a ∪ b
  | .difference, a, b => a \ b
  | .intersection, a, b => a ∩ b

/-- Finiteness is required only for the collection actually being counted.
In particular, the complete integer domain is not assumed finite. -/
noncomputable def finiteCard {A : Type u} (S : Set A) : Option (ULift.{u} Int) := by
  classical
  exact if S.Finite then Option.some ⟨(S.ncard : Int)⟩ else none

/-- Strict lifting of mathematical operations, independent of execution. -/
def lift₂ {A B C : Type u} (f : A → B → C) (a : Option A) (b : Option B) : Option C :=
  a.bind fun x => b.map (f x)

/-- Empty domains give true. Only members of the domain require a defined body. -/
noncomputable def universal {U : Type u} (S : Set U)
    (body : U → Option (ULift.{u} Prop)) : Option (ULift.{u} Prop) := by
  classical
  exact if (∀ x ∈ S, (body x).isSome = true) then
    Option.some ⟨∀ x ∈ S, body x = Option.some ⟨True⟩⟩ else none

/-- Denotation of each resolved constructor. Boolean values are propositions;
truth is not defined by any executable checker's success. -/
noncomputable def Expr.denote {s : Support} {U : Type u}
    (m : IntegerBinding.{u,w} s U) {Γ t} (e : Expr s Γ t)
    (ρ : Environment s U Γ) : Option (Value U t) :=
  match e with
  | .boolean b => Option.some ⟨b = true⟩
  | .integer n => Option.some ⟨n⟩
  | .empty _ => Option.some ∅
  | .this => Option.some {ρ.this}
  | .extent x => Option.some (m.model.obj x)
  | .var v => Option.some {ρ.lookup v}
  | .map f => Option.some (ambientRelation (m.model.map (s.arrow f)))
  | .and a b => lift₂ (fun p q => ⟨p.down ∧ q.down⟩) (a.denote m ρ) (b.denote m ρ)
  | .not a => (a.denote m ρ).map (fun p => ⟨¬ p.down⟩)
  | .equal a b => lift₂ (fun p q => ⟨p = q⟩) (a.denote m ρ) (b.denote m ρ)
  | .less a b => lift₂ (fun p q => ⟨p.down < q.down⟩) (a.denote m ρ) (b.denote m ρ)
  | .arithmetic op a b => lift₂ (fun p q => ⟨match op with
      | .add => p.down + q.down | .subtract => p.down - q.down⟩) (a.denote m ρ) (b.denote m ρ)
  | .integerOf _ a => (a.denote m ρ).bind (fun S => (m.realization.extract S).map ULift.up)
  | .cardinality a => (a.denote m ρ).bind finiteCard
  | .setOp op a b => lift₂ (collectionOp op) (a.denote m ρ) (b.denote m ρ)
  | .subset a b => lift₂ (fun S T => ⟨S ⊆ T⟩) (a.denote m ρ) (b.denote m ρ)
  | .image a b => lift₂ relationalImage (a.denote m ρ) (b.denote m ρ)
  | .join a b => lift₂ relationalJoin (a.denote m ρ) (b.denote m ρ)
  | .widenObjects _ a => a.denote m ρ
  | .widenRelation _ _ a => a.denote m ρ
  | .all b _ domain body => (domain.denote m ρ).bind
      (fun S => universal S (fun x => body.denote m (ρ.push b x)))

/-- Definedness and satisfaction are separate: false is a defined result. -/
def Expr.Defined {s U Γ t} (e : Expr s Γ t) (m : IntegerBinding.{u,w} s U)
    (ρ : Environment s U Γ) : Prop := ∃ v, e.denote m ρ = Option.some v

def Expr.Holds {s U Γ} (e : Expr s Γ .boolean) (m : IntegerBinding.{u,w} s U)
    (ρ : Environment s U Γ) : Prop := e.denote m ρ = Option.some ⟨True⟩

end Clafer.Constraints
