module

public import Clafer.Compile.Binding
public import Clafer.Compile.Local
public import FormalCD.Signature
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum

/-!
# Compile: resolved AST to a well-formed MCS

SoSyM §6.2.4, Figure 23 and Tables 5–8 (see Appendix 5). The disjoint signature
extension retains built-in predicates and uses the established syntax-only
constraint signature. It does not interpret expression bodies or assert
semantic preservation. The input supplies typed bodies for every AST boundary.
-/

@[expose] public section
namespace Clafer.Compile
open CategoryTheory MCS

variable {a : AST}

noncomputable def vocabulary (i : Input a) : FormalCD.Vocabulary :=
  FormalCD.Vocabulary.extend (Constraints.signature i.constraint)

abbrev FormulaId (i : Input a) := LocalId (family i) ⊕ ConstraintId a

-- [impl->req~clafer-compile-formulas~1]
noncomputable def formula (i : Input a) : FormulaId i →
    DPGraph.Formula (vocabulary i).signature (roles i).graph
  | .inl l => (vocabulary i).embed l.formula
  | .inr q => ⟨.inr q, binding i q⟩

noncomputable def formulas (i : Input a) : Formulas (roles i) (vocabulary i).signature where
  Id := FormulaId i
  owner | .inl l => l.owner | .inr q => q.1
  formula := formula i

theorem formulas_wellFormed (i : Input a) : (formulas i).WellFormed where
  total_args f := by
    cases f with
    | inl l => exact ⟨l.arg⟩
    | inr q =>
      let e : (support i q).Edge := ⟨0, i.positive_support q⟩
      exact ⟨⟨((support i q).mapRef e).source, ((support i q).mapRef e).target,
        (support i q).arrow e⟩⟩
  literal_key x y hs hb := by
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        exact congrArg Sum.inl (LocalId.key_unique x y (Sum.inl.inj hs) hb)
      | inr y => cases hs
    | inr x =>
      cases y with
      | inl y => cases hs
      | inr y => exact congrArg Sum.inr (Sum.inr.inj hs)

-- [impl->req~clafer-compile-contract~1]
-- [impl->req~clafer-compile-structure~1]
/-- The structural Compile transformation. All output disciplines are derived;
no MCS well-formedness proof is assumed by the input. -/
noncomputable def compile (i : Input a) :
    Model a.Occurrence a.Occurrence (vocabulary i).signature where
  family := family i
  roles := roles i
  labels := labels i
  formulas := formulas i
  valid := ⟨family_wellFormed i, (family i).canonical_cojoining,
    naming i, formulas_wellFormed i⟩

-- [proof->req~clafer-compile-contract~1]
theorem wellFormed (i : Input a) : Valid (compile i).labels (compile i).formulas :=
  (compile i).valid

/-- All local Shape declarations appear with their complete translated binding. -/
theorem shape_declared (i : Input a) (c : a.Occurrence)
    (φ : DPGraph.Formula DPGraph.Predicates.signature ((family i).shape c).carrier)
    (h : φ ∈ Shape.declarations ((family i).shape c)) :
    (vocabulary i).embed (φ.translate ((roles i).binding c)) ∈
      (compile i).formulas.diagram.declarations := by
  obtain ⟨l, _, hl⟩ := local_complete (family i) c φ h
  exact ⟨.inl l, congrArg (vocabulary i).embed hl⟩

theorem inclusion_declared (i : Input a) (s : (family i).InclusionSlot) :
    (vocabulary i).embed (LocalId.formula (.inclusion s)) ∈
      (compile i).formulas.diagram.declarations := ⟨.inl (.inclusion s), rfl⟩

-- [proof->req~clafer-compile-formulas~1]
/-- Completeness for authored constraints is indexed by the attached occurrence. -/
theorem constraint_declared (i : Input a) (q : ConstraintId a) :
    (⟨.inr q, binding i q⟩ : DPGraph.Formula (vocabulary i).signature (roles i).graph) ∈
      (compile i).formulas.diagram.declarations := ⟨.inr q, rfl⟩

theorem constraint_owner (i : Input a) (q : ConstraintId a) :
    (compile i).formulas.owner (.inr q) = q.1 := rfl

theorem constraint_binding (i : Input a) (q : ConstraintId a) :
    ((compile i).formulas.formula (.inr q)).binding = binding i q := rfl

-- [proof->req~clafer-compile-structure~1]
/-- Distinct generated heads remain distinct even if their display names agree. -/
theorem fresh_heads (i : Input a) {c d : a.Occurrence} (h : c ≠ d) :
    (compile i).roles.head c ≠ (compile i).roles.head d :=
  fun he => h ((heads_bijective i).1 he)

theorem fresh_maps (i : Input a) {c d : a.Occurrence} (h : c ≠ d)
    (m : Clafer.Roles.Map ((family i).shape c).kind ((family i).shape c).hasParent)
    (n : Clafer.Roles.Map ((family i).shape d).kind ((family i).shape d).hasParent) :
    Family.MapId.ordinary c m ≠ .ordinary d n := fun he => h (ordinary_owner_unique he)

/-- Target sharing is exactly resolved-ID sharing, independent of source names. -/
theorem shared_target (i : Input a) (c d t : a.Occurrence)
    (hc : (a.at c).declaration.reference.target = some (sourceId a t))
    (hd : (a.at d).declaration.reference.target = some (sourceId a t))
    (kc : ((family i).shape c).kind ≠ .basic)
    (kd : ((family i).shape d).kind ≠ .basic) :
    (roles i).vertex c (Shape.targetClass _ kc) =
      (roles i).vertex d (Shape.targetClass _ kd) :=
  ((family i).canonical_cojoining.target c t ((target_eq i c t).mpr hc) kc).trans
    ((family i).canonical_cojoining.target d t ((target_eq i d t).mpr hd) kd).symm

/-- The generated class and map carriers are finite without restricting DPGraph. -/
theorem maps_finite (i : Input a) : Finite (family i).MapId := by
  let generate : ((Σ c, Clafer.Roles.Map ((family i).shape c).kind
      ((family i).shape c).hasParent) ⊕ (family i).InclusionSlot) → (family i).MapId
    | .inl ⟨c, m⟩ => .ordinary c m
    | .inr s => .inclusion s
  apply Finite.of_surjective generate
  intro m
  cases m with
  | ordinary c m => exact ⟨.inl ⟨c, m⟩, rfl⟩
  | inclusion s => exact ⟨.inr s, rfl⟩

end Clafer.Compile
