module

public import Clafer.Behavioral.PrimitiveExpression
public import Clafer.Behavioral.StructuralBinding
public import Mathlib.Tactic.FinCases

/-! An infinite integer carrier with two reference heads. The support includes
the complete integer extent, while each head observation is finite. -/

@[expose] public section
namespace Clafer.Behavioral.PrimitiveExpressionExamples
open Semantics Constraints DPGraph.Predicates

abbrev Object := Fin 3 ⊕ Int

def model : Structural.Core 3 where
  family := {
    root := 0
    parent := fun d => if d = 0 then none else some 0
    reference := fun d => if d = 1 then .bag 2 else .basic
    super := fun _ => none
    origin := fun d => if d = 0 then .syntheticRoot else if d = 2 then .primitive .int else .user
    isAbstract := fun _ => false
    name := fun _ => ""
    multiplicity := fun _ => unrestricted }
  id d := ⟨d.val⟩
  group _ := unrestricted
  authoredAbstract _ := false

def pool : Identities (Fin 3) Object where
  root := .inl 0
  directType := fun x => match x with
    | .inl i => if i = 0 then 0 else 1
    | .inr _ => 2
  parent x := if x = .inl 0 then none else some (.inl 0)

def trace : Trace (Fin 3) Object where
  identities := pool
  live _ := Set.univ
  deref t d x y := d = 1 ∧ (x = .inl 1 ∨ x = .inl 2) ∧ y = .inr (if t = 0 then 3 else 5)

def integers : IntegerRealization Object where
  encode := ⟨Sum.inr, Sum.inr_injective⟩
  decode := fun x => match x with | .inr i => i | .inl _ => 0
  decode_encode _ := rfl

@[simp] theorem ancestry (a b : Fin 3) : model.toEffectiveCore.Ancestor a b ↔ a = b := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ edge _ => cases edge
  · rintro rfl; exact .refl

@[simp] theorem heads (t : Nat) (d : Fin 3) (x : Object) :
    x ∈ (trace.raw model.toEffectiveCore t).head d ↔ pool.directType x = d := by
  simp [Trace.raw, trace]

@[simp] theorem containment (t : Nat) (d : Fin 3) (p x : Object) :
    (trace.raw model.toEffectiveCore t).contains d p x ↔
      pool.parent x = some p ∧ pool.directType x = d ∧ d ≠ 0 := by
  change (True ∧ True ∧ pool.parent x = some p) ∧
    model.toEffectiveCore.Ancestor (pool.directType x) d ∧
      (if d = 0 then none else some (0 : Fin 3)) ≠ none ↔ _
  simp

-- [utest->req~behavioral-structural-compatibility~1]
theorem wellFormed : model.WellFormed := by
  constructor
  · decide
  · simp [model]
  · intro d p hp; fin_cases d <;> simp [model] at hp ⊢
  · intro d e p hd he
    fin_cases d <;> fin_cases e <;> simp [model] at hd he ⊢
  · decide
  · decide
  · decide
  · intro d s o a b hs; cases hs
  · exact ⟨Fin.val, by decide⟩
  · exact ⟨fun _ => 0, by decide⟩
  · intro a b he; exact Fin.ext (congrArg Clafer.DeclId.value he)
  · intro d; trivial
  · intro d; trivial
  · intro d; rfl

private theorem root_type_iff (x : Object) : pool.directType x = 0 ↔ x = .inl 0 := by
  cases x with
  | inl i => fin_cases i <;> decide
  | inr i => simp [pool]

private theorem reference_type_iff (x : Object) :
    pool.directType x = 1 ↔ x = .inl 1 ∨ x = .inl 2 := by
  cases x with
  | inl i => fin_cases i <;> decide
  | inr i => simp [pool]

private theorem unrestricted_range (A : Type) : InRange unrestricted A :=
  ⟨⟨{ toFun := Fin.elim0, inj' := fun i => Fin.elim0 i }⟩, trivial⟩

-- [utest->req~behavioral-reference-atoms~1]
theorem valid : Structural.Valid model trace := by
  constructor
  · constructor
    · rfl
    · exact fun x h => (root_type_iff x).mp h
    · intro x; rfl
    · simp [trace, pool]
    · intro x hx; exact ⟨.inl 0, by simpa [trace, pool, hx]⟩
    · intro x p hp
      have hx : x ≠ .inl 0 := by intro he; subst x; simp [trace, pool] at hp
      have hpar : p = .inl 0 := by simpa [trace, pool, hx] using hp.symm
      subst p
      refine ⟨0, ?_, .refl⟩
      have ht := mt (root_type_iff x).mp hx
      simp [model, trace, ht]
  · intro t; trivial
  · intro t x p hx hp; trivial
  · intro t
    constructor
    · constructor
      · intro d p x h
        rw [containment] at h
        refine ⟨(heads t d x).mpr h.2.1, 0, ?_, ?_⟩
        · simp [model, h.2.2]
        · have hx : x ≠ .inl 0 := by intro he; subst x; exact h.2.2 h.2.1.symm
          have hp : p = .inl 0 := by simpa [pool, hx] using h.1.symm
          subst p; exact (heads t 0 _).mpr rfl
      · intro d x y h
        rcases h with ⟨rfl, hx, rfl⟩
        exact ⟨(heads t 1 x).mpr ((reference_type_iff x).mpr hx), 2, rfl,
          (heads t 2 _).mpr rfl⟩
    · intro x; exact (heads t 0 x).trans (root_type_iff x)
    · intro d hd hx; exact hd ((heads t d _).mp hx).symm
    · intro d s hs; cases hs
    · intro d hd; cases hd
    · intro d p hd x hx
      have hn : d ≠ 0 := by intro he; subst d; cases hd
      have hp : p = 0 := by simpa [model, hn] using hd.symm
      subst p
      have ht := (heads t d x).mp hx
      have hnroot : x ≠ .inl 0 := by intro he; subst x; exact hn ht.symm
      refine ⟨.inl 0, (containment t d _ x).mpr ⟨by simp [pool, hnroot], ht, hn⟩, ?_⟩
      intro y hy
      have hpar := ((containment t d y x).mp hy).1
      simpa [pool, hnroot] using hpar.symm
    · intro d c hd x hx
      have he : d = 1 := by
        by_contra hn
        simp [model, hn, MCS.ReferenceTo.target] at hd
      subst d
      have ht := (reference_type_iff x).mp ((heads t 1 x).mp hx)
      exact ⟨.inr (if t = 0 then 3 else 5), ⟨rfl, ht, rfl⟩, fun y hy => hy.2.2⟩
    · intro d e x y z hy hz; exact hy.2.2.trans hz.2.2.symm
    · intro d o ho hk
      have noSet : ∀ o, (model.family.reference o).kind ≠ .referenceSet := by decide
      exact (noSet o hk).elim
    · intro d p hd x hx; exact unrestricted_range _
    · intro d hd x; exact unrestricted_range _
    · intro d e x hd he
      exact Or.inl ((ancestry d e).mpr (((heads t d x).mp hd).symm.trans ((heads t e x).mp he)))
    · intro x hx
      by_cases hr : x = .inl 0
      · subst x; exact .refl
      · exact Relation.ReflTransGen.single ⟨pool.directType x,
          (containment t _ _ x).mpr ⟨by change pool.parent x = some (.inl 0); simp [pool, hr],
            rfl, mt (root_type_iff x).mp hr⟩⟩

theorem admitted : Structural.Admissible model trace := ⟨wellFormed, valid⟩

abbrev support : Support where
  classCount := 3
  mapCount := 1
  classId d := ⟨d.val⟩
  mapRef _ := ⟨⟨1⟩, .dereference, 1, 2, "dref"⟩
  context := 1
  integer d := d == 2

def resolution (t : Nat) : StructuralBinding.Resolution model trace t support :=
  .ofRoles _ _ _ valid id (fun _ => 1) (fun _ => rfl) (fun _ => rfl)
    (fun _ => ⟨rfl, 1, .declared (by simp [model]), rfl⟩)

def binding (t : Nat) : IntegerBinding support Object :=
  (resolution t).binding wellFormed.ids integers (by
    intro v hv
    have he : v = 2 := by simpa using hv
    subst v
    change (trace.raw model.toEffectiveCore t).head 2 = integers.domain
    ext x
    rw [heads]
    cases x with
    | inl i =>
      change pool.directType (.inl i) = 2 ↔ ∃ n, Sum.inr n = Sum.inl i
      fin_cases i <;> simp [pool]
    | inr i =>
      change (2 : Fin 3) = 2 ↔ ∃ n, Sum.inr n = (Sum.inr i : Object)
      simp)

-- [utest->req~behavioral-reference-atoms~1]
theorem complete_static_agreement {Γ ty} (e : Expr support Γ ty)
    (σ : Constraints.Environment support Object Γ) (t : Nat) :
    CapturedStatic.eval (trace.live t) (binding t) e (CapturedStatic.capture σ) =
      e.denote (binding t) σ :=
  CapturedStatic.agrees _ _ _ _ _ (CapturedStatic.capture_compatible σ) trivial

open PrimitiveExpression

def targetVariable {n : Nat} : SetExpr (Fin 3) (n + 1) := .step (.deref 1) (.var 0)

theorem current_target {n : Nat} (ρ : Behavioral.Environment Object n) (t : Nat)
    {x : Object} (hx : x = .inl 1 ∨ x = .inl 2) :
    targetVariable.eval model.toEffectiveCore (Structural.observed model trace) (ρ.push {x}) t =
      {integers.encode (if t = 0 then 3 else 5)} := by
  ext y
  change y ∈ Structural.eval model trace (.step (.deref 1) (.var 0)) (ρ.push {x}) t ↔ _
  rw [Structural.captured_deref model trace valid]
  rw [InheritedReference.deref_owner (InheritedReference.Owner.declared (by simp [model]) :
    InheritedReference.Owner model.family 1 1)]
  simp only [heads, Set.mem_singleton_iff]
  exact ⟨fun h => h.2.2.2, fun h => ⟨(reference_type_iff x).mpr hx, rfl, hx, h⟩⟩

theorem current_value {n : Nat} (ρ : Behavioral.Environment Object n) (t : Nat)
    {x : Object} (hx : x = .inl 1 ∨ x = .inl 2) :
    integer model.toEffectiveCore (Structural.observed model trace) integers (ρ.push {x}) t
      (.coerce (.set targetVariable)) = some (if t = 0 then 3 else 5) := by
  rw [coerce_eval]
  simp only [collection, current_target ρ t hx, Option.bind_some, IntegerObservation.coerce_singleton]

-- [utest->req~behavioral-reference-atoms~1]
theorem stored_head_current_value :
    integer model.toEffectiveCore (Structural.observed model trace) integers
      ((Behavioral.Environment.closed (.inl 0)).push {.inl 1}) 1
      (.coerce (.set targetVariable)) = some 5 := current_value _ 1 (Or.inl rfl)

theorem captured_target_unchanged :
    (SetExpr.var 0).eval model.toEffectiveCore (Structural.observed model trace)
      ((Behavioral.Environment.closed (.inl 0)).push {integers.encode 3}) 1 = {integers.encode 3} := rfl

private theorem head_extent (t : Nat) :
    (trace.raw model.toEffectiveCore t).head 1 = {Sum.inl 1, Sum.inl 2} := by
  ext x; rw [heads, reference_type_iff]; rfl

private theorem two_occurrences :
    occurrences ([{Sum.inl 1, Sum.inl 2}] : List (Set Object)) =
      {((0 : Fin 1), Sum.inl 1), ((0 : Fin 1), Sum.inl 2)} := by
  ext p
  obtain ⟨i, x⟩ := p
  have hi : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
  subst i
  simp [occurrences]

-- [utest->req~behavioral-reference-atoms~1]
theorem reference_head_sum :
    integer model.toEffectiveCore (Structural.observed model trace) integers
      (Behavioral.Environment.closed (.inl 0)) 0
      (.fold .sum (.cons (.set (.extent 1)) .nil) (.coerce (.set targetVariable))) = some 6 := by
  classical
  rw [fold_eval]
  simp only [collections, collection, SetExpr.eval, Structural.observed_head,
    head_extent, lift₂, Option.bind_some, Option.map_some, two_occurrences]
  rw [Aggregate.fold_finite _ ((Set.finite_singleton _).insert _) _ (by
    intro p hp
    have h := Set.mem_insert_iff.mp hp
    rcases h with rfl | h
    · rw [current_value _ 0 (Or.inl rfl)]; rfl
    · have hp := Set.mem_singleton_iff.mp h; subst p
      rw [current_value _ 0 (Or.inr rfl)]; rfl)]
  simp [current_value _ 0 (x := Sum.inl 1) (Or.inl rfl),
    current_value _ 0 (x := Sum.inl 2) (Or.inr rfl)]

theorem empty_extrema_not_zero :
    (PrimitiveExpression.Atom.equal (.extreme .minimum (.set .empty)) (.literal 0)).eval
      model.toEffectiveCore (Structural.observed model trace) integers
      (Behavioral.Environment.closed (.inl 0)) 0 = some False := by
  simp [PrimitiveExpression.Atom.eval, collection, SetExpr.eval, Aggregate.select_empty]

theorem whole_integer_extent_undefined :
    integer model.toEffectiveCore (Structural.observed model trace) integers
      (Behavioral.Environment.closed (.inl 0)) 0 (.coerce (.set (.extent 2))) = none := by
  rw [coerce_eval]
  simp only [collection, SetExpr.eval, Structural.observed_head, Option.bind_some]
  apply IntegerObservation.coerce_infinite
  have he : (trace.raw model.toEffectiveCore 0).head 2 = Set.range (Sum.inr : Int → Object) := by
    ext x; rw [heads]; cases x with
    | inl i => fin_cases i <;> simp [pool]
    | inr i => simp [pool]
  rw [he]
  exact Set.infinite_range_of_injective Sum.inr_injective

end Clafer.Behavioral.PrimitiveExpressionExamples
