module

public import Clafer.Behavioral.InitializerStructure

/-! # Production initializer compatibility

Behavioral §5 Definitions 3–5 / §6.1, accepted #169–#171. Scalar admission
and fixed original environments connect production meaning to the independent
aggregate and constant-trace results. Structural and observation assumptions
remain independent of initializer satisfaction.
-/

@[expose] public section
namespace Clafer.Behavioral.Initializers.Compatibility
universe u
open Structure

-- [proof->req~behavioral-initializer-contract~1]
/-- A strict conditional preserves a scalar bound from both branches. This
includes full temporal formula conditions and undefined inactive results. -/
theorem choose_scalar {U : Type u} (c : Option Bool) (a b : Option (Set U))
    (sa : ∀ S, a = some S → S.Subsingleton)
    (sb : ∀ S, b = some S → S.Subsingleton)
    (S : Set U) (h : Transport.choose c a b = some S) : S.Subsingleton := by
  cases c with
  | none => simp [Transport.choose] at h
  | some c =>
    cases a with
    | none => simp [Transport.choose] at h
    | some A =>
      cases b with
      | none => simp [Transport.choose] at h
      | some B =>
        cases c
        · have eq : B = S := Option.some.inj h
          exact eq ▸ sb B rfl
        · have eq : A = S := Option.some.inj h
          exact eq ▸ sa A rfl

/-- A concrete scalar certificate supplied by the accepted resolved bound
analysis, against the actual original-context primitive evaluator. -/
theorem primitive_scalar {k n : Nat} {U : Type u} (m : Structural.Core k)
    (τ : Trace (Fin k) U) (R : Constraints.IntegerRealization U)
    (ρ : Environment U n) (t : Nat) (leaf : SetExpr (Fin k) n → Bool)
    (leafSound : ∀ a, leaf a = true → (Structural.eval m τ a ρ t).Subsingleton)
    (rhs : CollectionExpr (Fin k) n) (admitted : Bounds.scalar leaf rhs = true) :
    ∀ S, PrimitiveExpression.collection m.toEffectiveCore (Structural.observed m τ)
      R ρ t rhs = some S → S.Subsingleton :=
  fun _ value => Bounds.scalar_sound _ _ _ _ _ leaf leafSound rhs admitted value

-- [proof->req~behavioral-snapshot-bridge~1]
/-- For a constant live trace, production per-head births collapse to the
static aggregate guard. The RHS context is derived from structural ownership.
There is no definedness assumption on absent heads. -/
theorem single_constant_aggregate {k : Nat} {U : Type u} {V : Type}
    (m : Structural.Core k) (τ : Trace (Fin k) U) (valid : Structural.Valid m τ)
    {d o : Fin k} (owner : InheritedReference.Owner m.family d o)
    (source : V → Transport.Value U (Set U) 0) (rhs : V)
    (live : ∀ t, τ.live t = τ.live 0)
    (admission : ∀ p ∈ contexts m τ d 0,
      (heads m τ d 0 p).Subsingleton ∨
        ∀ S, source rhs (.closed p) 0 = some S → S.Subsingleton) :
    Meaning τ (view m τ valid owner) source ⟨d, origin m d, .instanceBirth, rhs⟩ ↔
      Candidate.Static (τ.live 0) (contexts m τ d 0) (heads m τ d 0)
        ((view m τ valid owner).targets 0) (fun p => source rhs (.closed p) 0) := by
  rw [single_fibers m τ valid owner source rhs]
  have grouping (p : U) (hp : p ∈ contexts m τ d 0) :
      Candidate.Guarded (heads m τ d 0 p) ((view m τ valid owner).targets 0 p)
        (source rhs (.closed p) 0) ↔
      ∀ x ∈ heads m τ d 0 p, source rhs (.closed p) 0 = some {target m τ valid owner 0 x} := by
    rcases admission p hp with one | scalar
    · exact Bounds.aggregate_iff_singletons_of_head_bound _ _ _ one
    · exact Bounds.aggregate_iff_singletons _ _ _ scalar
  constructor
  · intro init p hp _
    apply (grouping p hp).mpr
    intro x hx
    exact init 0 p hp x hx ((τ.starts_zero x).mpr (head_mem m τ hx).1)
  · intro init t p hp x hx birth
    have zero := ((Candidate.starts_constant_live τ live t x).mp birth).2
    subst t
    exact (grouping p hp).mp (init p hp (contexts_live m τ valid d 0 hp)) x hx

/-- The concrete-head branch obtains its bound from structural multiplicity,
not from the initializer's own target equation. -/
theorem concrete_head_bound {k : Nat} {U : Type u} (m : Structural.Core k)
    (τ : Trace (Fin k) U) (valid : Structural.Valid m τ) {d c : Fin k}
    (parent : m.family.parent d = some c) (lower upper : Nat) (small : upper ≤ 1)
    (bound : m.family.multiplicity d = ⟨lower, .finite upper⟩)
    (t : Nat) (p : U) (hp : p ∈ contexts m τ d t) :
    (heads m τ d t p).Subsingleton := by
  have typed : p ∈ (τ.raw m.toEffectiveCore t).head c := by
    simpa [contexts, parent] using hp
  have range := (valid.states t).multiplicities d c parent p typed
  rw [bound] at range
  obtain ⟨f⟩ := range.2
  intro x hx y hy
  have ownedX : (τ.raw m.toEffectiveCore t).contains d p x := by
    simpa only [heads, parent, ReferenceObservation.heads, Structural.current,
      Structural.observed_contains, Set.mem_ofPred_eq] using hx
  have ownedY : (τ.raw m.toEffectiveCore t).contains d p y := by
    simpa only [heads, parent, ReferenceObservation.heads, Structural.current,
      Structural.observed_contains, Set.mem_ofPred_eq] using hy
  have eq : f ⟨x, ownedX⟩ = f ⟨y, ownedY⟩ := by
    apply Fin.ext
    have ax := (f ⟨x, ownedX⟩).isLt
    have ay := (f ⟨y, ownedY⟩).isLt
    omega
  exact congrArg Subtype.val (f.injective eq)

-- [proof->req~behavioral-structural-compatibility~1]
/-- Collection production retains precisely the candidate constant-trace
assumptions. Temporal RHS conditions need not be stable merely because the
structural trace is constant; source static classification is separate. -/
theorem collection_constant {C V : Type} {U : Type u} (τ : Trace C U) (v : View U)
    (source : V → Transport.Value U (Set U) 0) (d : C) (origin : Transport.Origin) (rhs : V)
    (live : ∀ t, τ.live t = τ.live 0) (contexts : ∀ t, v.contexts t = v.contexts 0)
    (heads : ∀ t p, v.heads t p = v.heads 0 p)
    (targets : ∀ t p, v.targets t p = v.targets 0 p)
    (values : ∀ t p, source rhs (.closed p) t = source rhs (.closed p) 0) :
    (Meaning τ v source ⟨d, origin, .parentBirth, rhs⟩ ↔
      Candidate.Static (τ.live 0) (v.contexts 0) (v.heads 0) (v.targets 0)
        (fun p => source rhs (.closed p) 0)) ∧
    (Meaning τ v source ⟨d, origin, .everyLive, rhs⟩ ↔
      Candidate.Static (τ.live 0) (v.contexts 0) (v.heads 0) (v.targets 0)
        (fun p => source rhs (.closed p) 0)) :=
  Candidate.collection_constant_iff τ _ _ _ _ live contexts heads targets values

/-- A parentless global initializer is already its static root guard at zero;
no stability or RHS-definedness premise is needed for this clock. -/
theorem global_static {C V : Type} {U : Type u} (τ : Trace C U) (v : View U)
    (source : V → Transport.Value U (Set U) 0) (d : C) (rhs : V)
    (contexts : v.contexts 0 = {τ.identities.root}) (rootLive : τ.identities.root ∈ τ.live 0) :
    Meaning τ v source ⟨d, .root, .globalZero, rhs⟩ ↔
      Candidate.Static (τ.live 0) (v.contexts 0) (v.heads 0) (v.targets 0)
        (fun p => source rhs (.closed p) 0) := by
  constructor
  · intro h p hp _
    have eq : p = τ.identities.root := by simpa only [contexts, Set.mem_singleton_iff] using hp
    subst p
    exact h
  · intro h
    exact h τ.identities.root (by rw [contexts]; exact rfl) rootLive

/-- Independent static source values embed with stable observations by
construction; `none` remains available behind an empty declaration guard. -/
def staticValue {U : Type u} (value : U → Option (Set U)) : Transport.Value U (Set U) 0 :=
  fun ρ _ => value ρ.this

@[simp] theorem staticValue_stable {U : Type u} (value : U → Option (Set U))
    (ρ : Environment U 0) (t : Nat) : staticValue value ρ t = staticValue value ρ 0 := rfl

end Clafer.Behavioral.Initializers.Compatibility
