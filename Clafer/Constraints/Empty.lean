module

public import Clafer.Constraints.DenotationLaws
public import Clafer.Constraints.DenotationSupport

/-!
# Empty collections

Adopted language extension #134 to SoSyM Appendix 4/Figure 28. Alloy's
Subtypes and Relational Expressions sections motivate bottom element typing
with fixed arity. These laws use independent set denotation, not a solver.
-/

@[expose] public section
universe u w
namespace Clafer.Constraints
variable {s : Support} {U : Type u} {Γ : List (Local s)}
variable (m : IntegerBinding.{u,w} s U) (ρ : Environment s U Γ)

theorem empty_defined (k : Collection s) : (Expr.empty k : Expr s Γ _).Defined m ρ :=
  ⟨∅, rfl⟩

@[simp] theorem empty_extents (k : Collection s) :
    (Expr.empty k : Expr s Γ _).extents = ∅ := rfl
@[simp] theorem empty_maps (k : Collection s) :
    (Expr.empty k : Expr s Γ _).maps = ∅ := rfl

@[simp] theorem cardinality_empty (k : Collection s) :
    (Expr.cardinality (.empty k) : Expr s Γ _).denote m ρ = Option.some ⟨0⟩ := by
  simp [finiteCard]

@[simp] theorem no_empty (k : Collection s) :
    (Expr.no (.empty k) : Expr s Γ _).Holds m ρ := by
  simp [Expr.Holds, Expr.no, lift₂]
@[simp] theorem lone_empty (k : Collection s) :
    (Expr.lone (.empty k) : Expr s Γ _).Holds m ρ := by
  simp [Expr.Holds, Expr.lone, lift₂]
@[simp] theorem some_empty (k : Collection s) :
    (Expr.some (.empty k) : Expr s Γ _).denote m ρ = Option.some ⟨False⟩ := by
  simp [Expr.some, lift₂]
@[simp] theorem one_empty (k : Collection s) :
    (Expr.one (.empty k) : Expr s Γ _).denote m ρ = Option.some ⟨False⟩ := by
  simp [Expr.one, lift₂]

theorem union_empty {k} (a : Expr s Γ (.collection k)) :
    (Expr.setOp .union a (.empty k)).denote m ρ = a.denote m ρ := by
  simp [lift₂, collectionOp]
theorem empty_union {k} (a : Expr s Γ (.collection k)) :
    (Expr.setOp .union (.empty k) a).denote m ρ = a.denote m ρ := by
  cases h : a.denote m ρ <;> simp [lift₂, collectionOp, h]
theorem difference_empty {k} (a : Expr s Γ (.collection k)) :
    (Expr.setOp .difference a (.empty k)).denote m ρ = a.denote m ρ := by
  simp [lift₂, collectionOp]

/-- The hypothesis preserves strict undefined propagation. -/
theorem intersection_empty {k} (a : Expr s Γ (.collection k))
    (h : a.Defined m ρ) :
    (Expr.setOp .intersection a (.empty k)).denote m ρ = Option.some ∅ := by
  obtain ⟨S,hS⟩ := h
  simp [lift₂, collectionOp, hS]
theorem empty_difference {k} (a : Expr s Γ (.collection k))
    (h : a.Defined m ρ) :
    (Expr.setOp .difference (.empty k) a).denote m ρ = Option.some ∅ := by
  obtain ⟨S,hS⟩ := h
  simp [lift₂, collectionOp, hS]
theorem empty_subset {k} (a : Expr s Γ (.collection k))
    (h : a.Defined m ρ) : (Expr.subset (.empty k) a).Holds m ρ := by
  obtain ⟨S,hS⟩ := h
  simp [Expr.Holds, lift₂, hS]

theorem image_empty {x y} (r : Expr s Γ (.collection (.relation x y)))
    (h : r.Defined m ρ) :
    (Expr.image (.empty (.objects x)) r).denote m ρ = Option.some ∅ := by
  obtain ⟨R,hR⟩ := h
  simp [lift₂, hR, relationalImage]
theorem join_empty {x y z} (r : Expr s Γ (.collection (.relation x y)))
    (h : r.Defined m ρ) :
    (Expr.join r (.empty (.relation y z))).denote m ρ = Option.some ∅ := by
  obtain ⟨R,hR⟩ := h
  simp [lift₂, hR, relationalJoin]

theorem all_empty (b : Local s) (fresh : ∀ old ∈ Γ, old.id ≠ b.id)
    (body : Expr s (b :: Γ) .boolean) :
    (Expr.all b fresh (.empty (.objects b.element)) body).Holds m ρ := by
  simp [Expr.Holds]

@[simp] theorem integerOf_empty {x} (h : s.integer x = true) :
    (Expr.integerOf h (.empty (.objects x)) : Expr s Γ _).denote m ρ = none := by
  simp

end Clafer.Constraints
