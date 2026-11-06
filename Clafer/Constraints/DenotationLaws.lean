module

public import Clafer.Constraints.Denotation

/-! # Constructor equations for SoSyM D.4 and resolved sugar -/

@[expose] public section
universe u w
namespace Clafer.Constraints
variable {s : Support} {U : Type u} {Γ : List (Local s)}
variable (m : IntegerBinding.{u,w} s U) (ρ : Environment s U Γ)

-- [proof->req~clafer-constraint-denotation~1]
@[simp] theorem denote_boolean (b : Bool) :
    (Expr.boolean b : Expr s Γ _).denote m ρ = Option.some ⟨b = true⟩ := rfl
@[simp] theorem denote_integer (n : Int) :
    (Expr.integer n : Expr s Γ _).denote m ρ = Option.some ⟨n⟩ := rfl
@[simp] theorem denote_empty (k : Collection s) :
    (Expr.empty k : Expr s Γ _).denote m ρ = Option.some ∅ := rfl
-- [proof->req~clafer-constraint-environments~1]
@[simp] theorem denote_this :
    (Expr.this : Expr s Γ _).denote m ρ = Option.some {ρ.this} := rfl
@[simp] theorem denote_extent (x : s.Vertex) :
    (Expr.extent x : Expr s Γ _).denote m ρ = Option.some (m.model.obj x) := rfl
@[simp] theorem denote_var {x} (v : Var Γ x) :
    (Expr.var v).denote m ρ = Option.some {ρ.lookup v} := rfl
@[simp] theorem denote_map (f : s.Edge) :
    (Expr.map f : Expr s Γ _).denote m ρ =
      Option.some (ambientRelation (m.model.map (s.arrow f))) := rfl
@[simp] theorem denote_and (a b : Expr s Γ .boolean) :
    (Expr.and a b).denote m ρ = lift₂ (fun p q => ⟨p.down ∧ q.down⟩)
      (a.denote m ρ) (b.denote m ρ) := rfl
@[simp] theorem denote_not (a : Expr s Γ .boolean) :
    (Expr.not a).denote m ρ = (a.denote m ρ).map (fun p => ⟨¬ p.down⟩) := rfl
@[simp] theorem denote_equal {t} (a b : Expr s Γ t) :
    (Expr.equal a b).denote m ρ = lift₂ (fun p q => ⟨p = q⟩)
      (a.denote m ρ) (b.denote m ρ) := rfl
@[simp] theorem denote_less (a b : Expr s Γ .integer) :
    (Expr.less a b).denote m ρ = lift₂ (fun p q => ⟨p.down < q.down⟩)
      (a.denote m ρ) (b.denote m ρ) := rfl
@[simp] theorem denote_arithmetic (op) (a b : Expr s Γ .integer) :
    (Expr.arithmetic op a b).denote m ρ = lift₂ (fun p q => ⟨match op with
      | .add => p.down + q.down | .subtract => p.down - q.down⟩)
      (a.denote m ρ) (b.denote m ρ) := rfl
@[simp] theorem denote_integerOf {x} (h : s.integer x = true)
    (a : Expr s Γ (.collection (.objects x))) :
    (Expr.integerOf h a).denote m ρ = (a.denote m ρ).bind
      (fun S => (m.realization.extract S).map ULift.up) := rfl
@[simp] theorem denote_cardinality {k} (a : Expr s Γ (.collection k)) :
    (Expr.cardinality a).denote m ρ = (a.denote m ρ).bind finiteCard := rfl
@[simp] theorem denote_setOp {k} (op) (a b : Expr s Γ (.collection k)) :
    (Expr.setOp op a b).denote m ρ = lift₂ (collectionOp op)
      (a.denote m ρ) (b.denote m ρ) := rfl
@[simp] theorem denote_subset {k} (a b : Expr s Γ (.collection k)) :
    (Expr.subset a b).denote m ρ = lift₂ (fun S T => ⟨S ⊆ T⟩)
      (a.denote m ρ) (b.denote m ρ) := rfl
@[simp] theorem denote_image {x y} (a : Expr s Γ (.collection (.objects x)))
    (b : Expr s Γ (.collection (.relation x y))) :
    (Expr.image a b).denote m ρ = lift₂ relationalImage (a.denote m ρ) (b.denote m ρ) := rfl
@[simp] theorem denote_join {x y z} (a : Expr s Γ (.collection (.relation x y)))
    (b : Expr s Γ (.collection (.relation y z))) :
    (Expr.join a b).denote m ρ = lift₂ relationalJoin (a.denote m ρ) (b.denote m ρ) := rfl
@[simp] theorem denote_widenObjects {x y} (h : Widen s x y)
    (a : Expr s Γ (.collection (.objects x))) :
    (Expr.widenObjects h a).denote m ρ = a.denote m ρ := rfl
@[simp] theorem denote_widenRelation {x y x' y'} (h : Widen s x x') (k : Widen s y y')
    (a : Expr s Γ (.collection (.relation x y))) :
    (Expr.widenRelation h k a).denote m ρ = a.denote m ρ := rfl
@[simp] theorem denote_all (b : Local s) (h : ∀ old ∈ Γ, old.id ≠ b.id)
    (domain : Expr s Γ (.collection (.objects b.element))) (body : Expr s (b :: Γ) .boolean) :
    (Expr.all b h domain body).denote m ρ = (domain.denote m ρ).bind
      (fun S => universal S (fun x => body.denote m (ρ.push b x))) := rfl

@[simp] theorem finiteCard_finite {A : Type u} (S : Set A) (h : S.Finite) :
    finiteCard S = Option.some ⟨(S.ncard : Int)⟩ := by simp [finiteCard,h]
@[simp] theorem finiteCard_infinite {A : Type u} (S : Set A) (h : S.Infinite) :
    finiteCard S = none := by simp [finiteCard,h]

-- [proof->req~clafer-constraint-semantic-laws~1]
@[simp] theorem universal_empty (body : U → Option (ULift.{u} Prop)) :
    universal ∅ body = Option.some ⟨True⟩ := by simp [universal]

theorem universal_defined (S : Set U) (body : U → Option (ULift.{u} Prop))
    (h : ∀ x ∈ S, ∃ p, body x = Option.some p) :
    universal S body = Option.some ⟨∀ x ∈ S, body x = Option.some ⟨True⟩⟩ := by
  have hh : ∀ x ∈ S, (body x).isSome = true := by
    intro x hx; obtain ⟨p,hp⟩ := h x hx; simp [hp]
  simp only [universal, ite_eq_left hh]

/-- One undefined body on a domain member makes the quantifier undefined. -/
theorem universal_undefined (S : Set U) (body : U → Option (ULift.{u} Prop))
    (x : U) (hx : x ∈ S) (hb : body x = none) : universal S body = none := by
  have h : ¬ ∀ y ∈ S, (body y).isSome = true := by
    intro hall
    have he := hall x hx
    simp [hb] at he
  simp only [universal, ite_eq_right h]

theorem denotes_some {k} (a : Expr s Γ (.collection k)) (S : Set (k.Carrier U))
    (ha : a.denote m ρ = Option.some S) (hf : S.Finite) :
    a.some.denote m ρ = Option.some ⟨S.Nonempty⟩ := by
  simp only [Expr.some, denote_less, denote_integer, denote_cardinality, ha,
    Option.bind_some, finiteCard_finite S hf, lift₂, Option.map_some]
  congr 2
  exact propext (by simpa using Set.ncard_pos hf)

theorem denotes_no {k} (a : Expr s Γ (.collection k)) (S : Set (k.Carrier U))
    (ha : a.denote m ρ = Option.some S) (hf : S.Finite) :
    a.no.denote m ρ = Option.some ⟨S = ∅⟩ := by
  simp [Expr.no,ha,hf,lift₂, Set.ncard_eq_zero hf]

theorem denotes_one {k} (a : Expr s Γ (.collection k)) (S : Set (k.Carrier U))
    (ha : a.denote m ρ = Option.some S) (hf : S.Finite) :
    a.one.denote m ρ = Option.some ⟨S.ncard = 1⟩ := by
  simp [Expr.one,ha,hf,lift₂]

theorem denotes_lone {k} (a : Expr s Γ (.collection k)) (S : Set (k.Carrier U))
    (ha : a.denote m ρ = Option.some S) (hf : S.Finite) :
    a.lone.denote m ρ = Option.some ⟨S.ncard ≤ 1⟩ := by
  simp [Expr.lone,ha,hf,lift₂]

theorem denotes_implies (a b : Expr s Γ .boolean) (P Q : Prop)
    (ha : a.denote m ρ = Option.some ⟨P⟩) (hb : b.denote m ρ = Option.some ⟨Q⟩) :
    (a.implies b).denote m ρ = Option.some ⟨P → Q⟩ := by
  classical
  simp [Expr.implies,ha,hb,lift₂]

theorem denotes_iff (a b : Expr s Γ .boolean) (P Q : Prop)
    (ha : a.denote m ρ = Option.some ⟨P⟩) (hb : b.denote m ρ = Option.some ⟨Q⟩) :
    (a.iff b).denote m ρ = Option.some ⟨P ↔ Q⟩ := by
  rw [Expr.iff, denote_and, denotes_implies m ρ a b P Q ha hb,
    denotes_implies m ρ b a Q P hb ha]
  simp only [lift₂,Option.bind_some,Option.map_some]
  exact congrArg (fun p => Option.some (ULift.up p)) (propext ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.mp,h.mpr⟩⟩)

theorem denotes_ge (a b : Expr s Γ .integer) (i j : Int)
    (ha : a.denote m ρ = Option.some ⟨i⟩) (hb : b.denote m ρ = Option.some ⟨j⟩) :
    (a.ge b).denote m ρ = Option.some ⟨j ≤ i⟩ := by
  simp [Expr.ge,ha,hb,lift₂]

theorem denotes_iff_true (a b : Expr s Γ .boolean)
    (hb : b.denote m ρ = Option.some ⟨True⟩) :
    (a.iff b).denote m ρ = a.denote m ρ := by
  classical
  cases ha : a.denote m ρ with
  | none => simp [Expr.iff,Expr.implies,Expr.denote,lift₂,ha,hb]
  | some p => simp [Expr.iff,Expr.implies,Expr.denote,lift₂,ha,hb]

end Clafer.Constraints
