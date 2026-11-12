module

public import Clafer.Behavioral.InitializerCandidate

/-! # Scalar admission for abstract initializers

Behavioral §5 Definitions 3–5 and §6.1; the accepted #170 supported-form
restriction. Bounds concern distinct targets when evaluation is defined.
Leaf certificates come from resolved declarations/navigation, never arbitrary
model constraints. This module does not perform name resolution or change the
partial evaluator. See docs/behavioral-initializers.md. -/

@[expose] public section
namespace Clafer.Behavioral.Initializers.Bounds
universe u

-- [impl->req~behavioral-initializer-contract~1]
/-- Conservative, compositional admission. Union of equal integer literals is
recognized without discarding partial operands. Other unions need a future
sound bound rule; arithmetic and extrema have at most one result when defined.
Like the source evaluator, this kernel-reducible definition suppresses native
helpers generated for recursion over the mutual syntax. -/
noncomputable def scalar {C : Type} {n : Nat} (leaf : SetExpr C n → Bool)
    (e : CollectionExpr C n) : Bool := match e with
  | .set a => leaf a
  | .literal _ | .integer _ | .extreme _ _ => true
  | .union (.literal i) (.literal j) => decide (i = j)
  | .union _ _ => false
  | .inter a b => scalar leaf a || scalar leaf b
  | .diff a _ => scalar leaf a
termination_by structural e

private theorem selected_scalar {U : Type u} (op : Aggregate.Extreme)
    (R : Constraints.IntegerRealization U) {S T : Set U}
    (h : op.select R S = some T) : T.Subsingleton := by
  obtain ⟨finite, typed⟩ := (Aggregate.select_defined_iff op R S).mp ⟨T, h⟩
  rcases S.eq_empty_or_nonempty with empty | present
  · subst S
    have eq : (∅ : Set U) = T := Option.some.inj ((Aggregate.select_empty op R).symm.trans h)
    exact eq ▸ Set.subsingleton_empty
  · obtain ⟨x, _, hx⟩ := Aggregate.select_singleton op R finite typed present
    have eq := Option.some.inj (hx.symm.trans h)
    exact eq ▸ Set.subsingleton_singleton

-- [proof->req~behavioral-initializer-contract~1]
/-- Every admitted defined result is scalar. No definedness premise is added
to the language: the conditional statement also permits undefined results. -/
theorem scalar_sound {k n : Nat} {U : Type u} (m : Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) (R : Constraints.IntegerRealization U)
    (ρ : Environment U n) (t : Nat) (leaf : SetExpr (Fin k) n → Bool)
    (leaf_sound : ∀ a, leaf a = true → (a.eval m τ ρ t).Subsingleton)
    (e : CollectionExpr (Fin k) n) (admitted : scalar leaf e = true)
    {T : Set U} (value : PrimitiveExpression.collection m τ R ρ t e = some T) :
    T.Subsingleton := by
  cases e with
  | set a =>
    have eq := Option.some.inj value
    exact eq ▸ leaf_sound a admitted
  | literal i =>
    have eq := Option.some.inj value
    exact eq ▸ Set.subsingleton_singleton
  | integer a =>
    cases h : PrimitiveExpression.integerValue m τ R ρ t a with
    | none => simp [PrimitiveExpression.collection, h] at value
    | some i =>
      have eq : ({R.encode i.down} : Set U) = T := by
        simpa [PrimitiveExpression.collection, h] using value
      exact eq ▸ Set.subsingleton_singleton
  | extreme op a =>
    cases h : PrimitiveExpression.collection m τ R ρ t a with
    | none => simp [PrimitiveExpression.collection, h] at value
    | some S =>
      exact selected_scalar op R (by simpa [PrimitiveExpression.collection, h] using value)
  | union a b =>
    cases a <;> cases b <;> simp only [scalar, Bool.false_eq_true] at admitted
    rename_i i j
    have eq : i = j := of_decide_eq_true admitted
    subst j
    have eqT : ({R.encode i} : Set U) = T := by
      simpa [PrimitiveExpression.collection, Constraints.lift₂] using value
    exact eqT ▸ Set.subsingleton_singleton
  | inter a b =>
    cases ha : PrimitiveExpression.collection m τ R ρ t a with
    | none => simp [PrimitiveExpression.collection, Constraints.lift₂, ha] at value
    | some A =>
      cases hb : PrimitiveExpression.collection m τ R ρ t b with
      | none => simp [PrimitiveExpression.collection, Constraints.lift₂, hb] at value
      | some B =>
        have eq : A ∩ B = T := by
          simpa [PrimitiveExpression.collection, Constraints.lift₂, ha, hb] using value
        subst T
        have either : scalar leaf a = true ∨ scalar leaf b = true := by
          simpa only [scalar, Bool.or_eq_true] using admitted
        rcases either with h | h
        · intro x hx y hy
          exact scalar_sound m τ R ρ t leaf leaf_sound a h ha hx.1 hy.1
        · intro x hx y hy
          exact scalar_sound m τ R ρ t leaf leaf_sound b h hb hx.2 hy.2
  | diff a b =>
    cases ha : PrimitiveExpression.collection m τ R ρ t a with
    | none => simp [PrimitiveExpression.collection, Constraints.lift₂, ha] at value
    | some A =>
      cases hb : PrimitiveExpression.collection m τ R ρ t b with
      | none => simp [PrimitiveExpression.collection, Constraints.lift₂, hb] at value
      | some B =>
        have eq : A \ B = T := by
          simpa [PrimitiveExpression.collection, Constraints.lift₂, ha, hb] using value
        subst T
        intro x hx y hy
        exact scalar_sound m τ R ρ t leaf leaf_sound a admitted ha hx.1 hy.1
termination_by e

-- [proof->req~behavioral-initializer-contract~1]
/-- A declared at-most-one head bound and functional references supply a
scalar target bound. The bound is independent of any initializer equality. -/
theorem reference_image_scalar {H V : Type u} {heads : Set H} {ref : H → V → Prop}
    (oneHead : heads.Subsingleton)
    (functional : ∀ x ∈ heads, ∀ y z, ref x y → ref x z → y = z) :
    {y | ∃ x ∈ heads, ref x y}.Subsingleton := by
  rintro y ⟨x, hx, hxy⟩ z ⟨w, hw, hwz⟩
  have eq := oneHead hx hw
  subst w
  exact functional x hx y z hxy hwz

theorem heads_scalar_of_bound {U : Type u} (heads : Set U) (lower : Nat)
    (bound : DPGraph.Predicates.InRange ⟨lower, .finite 1⟩ {x // x ∈ heads}) :
    heads.Subsingleton := by
  obtain ⟨f⟩ := bound.2
  intro x hx y hy
  have eq : f ⟨x, hx⟩ = f ⟨y, hy⟩ := Subsingleton.elim _ _
  exact congrArg Subtype.val (f.injective eq)

-- [proof->req~behavioral-initializer-contract~1]
/-- A resolved optional head collection supplies a sound dereference-leaf
certificate, including inherited references. This uses the actual navigation
evaluator and structural functionality, not the initializer being checked. -/
theorem captured_deref_scalar {k n : Nat} {U : Type u} (m : Structural.Core k)
    (τ : Trace (Fin k) U) (valid : Structural.Valid m τ)
    (ρ : Environment U n) (t : Nat) (d : Fin k) (S : Set U) (lower : Nat)
    (bound : DPGraph.Predicates.InRange ⟨lower, .finite 1⟩ {x // x ∈ S}) :
    (Structural.eval m τ (.step (.deref d) (.var 0)) (ρ.push S) t).Subsingleton := by
  rintro y ⟨x, hx, link⟩ z ⟨w, hw, other⟩
  have same := heads_scalar_of_bound S lower bound hx hw
  subst w
  exact valid.refined_reference_agrees
    ((Structural.observed_deref m τ valid t d x y).mp link)
    ((Structural.observed_deref m τ valid t d x z).mp other)

-- [proof->req~behavioral-initializer-contract~1]
/-- Scalar admission lets aggregate equality be checked per head.
Every head uses the same RHS observation in its original lexical
context; environment transport is not assumed from matching source names. -/
theorem aggregate_iff_singletons {U : Type u} (heads : Set U) (target : U → U)
    (rhs : Option (Set U)) (scalarRhs : ∀ S, rhs = some S → S.Subsingleton) :
    Candidate.Guarded heads (target '' heads) rhs ↔
      ∀ x ∈ heads, rhs = some {target x} := by
  constructor
  · intro h x hx
    have eq := h ⟨x, hx⟩
    have one := scalarRhs _ eq
    have image_eq : target '' heads = {target x} := by
      ext y
      constructor
      · intro hy
        exact one hy ⟨x, hx, rfl⟩
      · rintro rfl
        exact ⟨x, hx, rfl⟩
    exact eq.trans (congrArg some image_eq)
  · intro h present
    obtain ⟨x, hx⟩ := present
    have image_eq : target '' heads = {target x} := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact Set.singleton_injective (Option.some.inj ((h z hz).symm.trans (h x hx)))
      · rintro rfl
        exact ⟨x, hx, rfl⟩
    exact (h x hx).trans (congrArg some image_eq.symm)

/-- Concrete single declarations obtain aggregate/singleton agreement from
their head bound, even for a multi-target or undefined RHS. They need no
abstract scalar-admission restriction. -/
theorem aggregate_iff_singletons_of_head_bound {U : Type u} (heads : Set U)
    (target : U → U) (rhs : Option (Set U)) (one : heads.Subsingleton) :
    Candidate.Guarded heads (target '' heads) rhs ↔
      ∀ x ∈ heads, rhs = some {target x} := by
  have image_eq (x : U) (hx : x ∈ heads) : target '' heads = {target x} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact congrArg target (one hz hx)
    · rintro rfl
      exact ⟨x, hx, rfl⟩
  constructor
  · intro h x hx
    simpa only [image_eq x hx] using h ⟨x, hx⟩
  · intro h ⟨x, hx⟩
    simpa only [image_eq x hx] using h x hx

-- [proof->req~behavioral-initializer-contract~1]
/-- Supported-domain static compatibility for one attachment. All
heads share the RHS in its original lexical context. Live/head/target/RHS
stability and either a concrete head bound or abstract scalar admission are
explicit; undefined RHSs are still allowed when the head set is empty. -/
theorem supported_constant_iff_aggregate {C : Type} {U : Type u}
    (τ : Trace C U) (heads : Nat → Set U) (target : Nat → U → U)
    (rhs : Nat → Option (Set U))
    (live : ∀ t, τ.live t = τ.live 0) (head : ∀ t, heads t = heads 0)
    (targets : ∀ t x, target t x = target 0 x) (value : ∀ t, rhs t = rhs 0)
    (present : heads 0 ⊆ τ.live 0)
    (admission : (heads 0).Subsingleton ∨ ∀ S, rhs 0 = some S → S.Subsingleton) :
    (Candidate.SingleBirths τ heads target (fun t _ => rhs t) ↔
      Candidate.Guarded (heads 0) (target 0 '' heads 0) (rhs 0)) ∧
    (Candidate.EveryLive τ heads (fun _ x => {x}) (fun t x => {target t x})
      (fun t _ => rhs t) ↔
      Candidate.Guarded (heads 0) (target 0 '' heads 0) (rhs 0)) := by
  have bridge := Candidate.single_constant_iff τ heads target (fun t _ => rhs t)
    live head targets (fun t _ => value t)
  have grouping : Candidate.Guarded (heads 0) (target 0 '' heads 0) (rhs 0) ↔
      ∀ x ∈ heads 0, rhs 0 = some {target 0 x} := by
    rcases admission with bound | scalarRhs
    · exact aggregate_iff_singletons_of_head_bound _ _ _ bound
    · exact aggregate_iff_singletons _ _ _ scalarRhs
  have aggregate : Candidate.Static (τ.live 0) (heads 0) (fun x => {x})
      (fun x => {target 0 x}) (fun _ => rhs 0) ↔
      Candidate.Guarded (heads 0) (target 0 '' heads 0) (rhs 0) := by
    rw [grouping]
    constructor
    · intro h x hx
      exact h x hx (present hx) (Set.singleton_nonempty x)
    · intro h x hx _ _
      exact h x hx
  exact ⟨bridge.1.trans aggregate, bridge.2.trans aggregate⟩

end Clafer.Behavioral.Initializers.Bounds
