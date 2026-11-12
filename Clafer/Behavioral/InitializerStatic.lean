module

public import Clafer.Behavioral.InitializerCompatibility

/-! # Static primitive observations for initializer compatibility

SoSyM structural embedding and behavioral §5 Definition 5. These results
supply the constant-observation premises for resolved primitive RHSs. Temporal
conditions retain their separate time-sensitive contract; a constant structural
trace alone does not erase `initially`/`finally` inside a source value.
-/

@[expose] public section
namespace Clafer.Behavioral.Initializers.Static
universe u
variable {k : Nat} {U : Type u} {m : Semantics.EffectiveCore k}
  {s : Semantics.Configuration (Fin k) U} {ids : Identities (Fin k) U}
  (c : StaticCorrespondence m s ids) (R : Constraints.IntegerRealization U)

-- [proof->req~behavioral-snapshot-bridge~1]
theorem set_constant {n : Nat} (e : SetExpr (Fin k) n) (ρ : Environment U n) (t : Nat) :
    e.eval m c.constant ρ t = e.eval m c.constant ρ 0 := by
  induction e <;> simp_all [SetExpr.eval, Step.image, Step.relation, Trace.raw,
    Trace.ParentAt, StaticCorrespondence.constant]

mutual
  theorem collection_constant {n : Nat} (e : CollectionExpr (Fin k) n)
      (ρ : Environment U n) (t : Nat) :
      PrimitiveExpression.collection m c.constant R ρ t e =
        PrimitiveExpression.collection m c.constant R ρ 0 e := by
    cases e with
    | set a => simp only [PrimitiveExpression.collection, set_constant c a ρ t]
    | literal _ => rfl
    | integer a => simp only [PrimitiveExpression.collection, integer_constant a ρ t]
    | extreme op a => simp only [PrimitiveExpression.collection, collection_constant a ρ t]
    | union a b | inter a b | diff a b =>
      simp only [PrimitiveExpression.collection, collection_constant a ρ t,
        collection_constant b ρ t]
  termination_by sizeOf e

  theorem integer_constant {n : Nat} (e : IntegerExpr (Fin k) n)
      (ρ : Environment U n) (t : Nat) :
      PrimitiveExpression.integerValue m c.constant R ρ t e =
        PrimitiveExpression.integerValue m c.constant R ρ 0 e := by
    cases e with
    | literal _ => rfl
    | coerce a | extract a | cardinality a =>
      simp only [PrimitiveExpression.integerValue, collection_constant a ρ t]
    | binary op a b =>
      simp only [PrimitiveExpression.integerValue, integer_constant a ρ t,
        integer_constant b ρ t]
    | negate a => simp only [PrimitiveExpression.integerValue, integer_constant a ρ t]
    | fold op ds body =>
      simp only [PrimitiveExpression.integerValue, collections_constant ds ρ t,
        integer_constant body]
  termination_by sizeOf e

  theorem collections_constant {n : Nat} (e : CollectionList (Fin k) n)
      (ρ : Environment U n) (t : Nat) :
      PrimitiveExpression.collections m c.constant R ρ t e =
        PrimitiveExpression.collections m c.constant R ρ 0 e := by
    cases e with
    | nil => rfl
    | cons a rest =>
      simp only [PrimitiveExpression.collections, collection_constant a ρ t,
        collections_constant rest ρ t]
  termination_by sizeOf e
end

-- [proof->req~behavioral-structural-compatibility~1]
/-- The actual richer primitive adapter supplies stable observations on the
historical constant embedding. Common-fragment support and validity are kept. -/
theorem observed_primitive_constant (support : m.Supported)
    (satisfies : Semantics.StructuralSatisfies m s) {n : Nat}
    (e : CollectionExpr (Fin k) n) (ρ : Environment U n) (t : Nat) :
    PrimitiveExpression.collection m (Structural.observed (Structural.Core.ofEffective m) c.constant)
        R ρ t e =
      PrimitiveExpression.collection m (Structural.observed (Structural.Core.ofEffective m) c.constant)
        R ρ 0 e := by
  rw [Structural.observed_common c.constant support (c.constant_valid satisfies)]
  exact collection_constant c R e ρ t

/-- Source environment transport and RHS stability are discharged for actual
primitive expressions on the canonical structural embedding. Admission remains
an independent bound certificate, supplied by concrete multiplicity or scalar
analysis, never by assuming initializer satisfaction. -/
theorem production_constant_agreement (wf : m.WellFormed) (support : m.Supported)
    (groups : ∀ d, m.group d = (m.family.group d).effective.range)
    (satisfies : Semantics.StructuralSatisfies m s) {d o : Fin k}
    (owner : InheritedReference.Owner m.family d o) (rhs : CollectionExpr (Fin k) 0)
    (admission : ∀ p ∈ Structure.contexts (Structural.Core.ofEffective m) c.constant d 0,
      (Structure.heads (Structural.Core.ofEffective m) c.constant d 0 p).Subsingleton ∨
      ∀ S, PrimitiveExpression.collection m c.constant R (.closed p) 0 rhs = some S → S.Subsingleton) :
    let valid := (Structural.valid_iff_common wf support groups c.constant).mpr (c.constant_valid satisfies)
    let v := Structure.view (Structural.Core.ofEffective m) c.constant valid owner
    let source := fun e ρ t => PrimitiveExpression.collection m
      (Structural.observed (Structural.Core.ofEffective m) c.constant) R ρ t e
    let static := Candidate.Static (c.constant.live 0) (v.contexts 0) (v.heads 0)
      (v.targets 0) (fun p => source rhs (.closed p) 0)
    (Meaning c.constant v source ⟨d, Structure.origin (Structural.Core.ofEffective m) d,
      .instanceBirth, rhs⟩ ↔ static) ∧
    (Meaning c.constant v source ⟨d, Structure.origin (Structural.Core.ofEffective m) d,
      .everyLive, rhs⟩ ↔ static) := by
  dsimp only
  constructor
  · apply Compatibility.single_constant_aggregate _ _ _ owner _ rhs (fun _ => rfl)
    intro p hp
    simpa only [Structural.observed_common c.constant support (c.constant_valid satisfies)]
      using admission p hp
  · exact (Compatibility.collection_constant c.constant _ _ d _ rhs (fun _ => rfl)
      (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun t p => observed_primitive_constant c R support satisfies rhs (.closed p) t)).2

end Clafer.Behavioral.Initializers.Static
