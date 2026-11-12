module

public import Clafer.Behavioral.Initializers
public import Clafer.Behavioral.Snapshot

/-! # Candidate presence-guarded initializer equations

Behavioral §5 Definitions 3–5 and §6.1, T7/T9, with the accepted #169/#170
definedness extension. These equations analyze the proposed initializer contract;
they do not change `Initializers.elaborate` or select a collection classifier.
Resolved observations retain their enclosing lexical environment. No RHS
definedness is assumed outside the applicable presence/birth guard.
-/

@[expose] public section
namespace Clafer.Behavioral.Initializers.Candidate
universe u
variable {C : Type} {U : Type u}

-- [impl->req~behavioral-structural-compatibility~1]
/-- A declaration guard, not an object-language Boolean implication. Heads and
targets are supplied resolved observations; `none` and `some ∅` stay distinct. -/
def Guarded (heads targets : Set U) (rhs : Option (Set U)) : Prop :=
  heads.Nonempty → rhs = some targets

def Static (live contexts : Set U) (heads targets : U → Set U)
    (rhs : U → Option (Set U)) : Prop :=
  ∀ p ∈ contexts, p ∈ live → Guarded (heads p) (targets p) (rhs p)

def EveryLive (τ : Trace C U) (contexts : Nat → Set U)
    (heads targets : Nat → U → Set U) (rhs : Nat → U → Option (Set U)) : Prop :=
  ∀ t p, p ∈ contexts t → p ∈ τ.live t → Guarded (heads t p) (targets t p) (rhs t p)

/-- Collection `:=` checks the whole target image only at parent birth. -/
def CollectionBirths (τ : Trace C U) (parents : Nat → Set U)
    (heads targets : Nat → U → Set U) (rhs : Nat → U → Option (Set U)) : Prop :=
  ∀ t p, p ∈ parents t → τ.Starts t p → Guarded (heads t p) (targets t p) (rhs t p)

/-- Per-instance `:=`: `rhs t x` is the RHS observed in x's resolved parent
environment at this birth, not an expression re-resolved in x's namespace. -/
def SingleBirths (τ : Trace C U) (heads : Nat → Set U)
    (target : Nat → U → U) (rhs : Nat → U → Option (Set U)) : Prop :=
  ∀ t x, x ∈ heads t → τ.Starts t x → rhs t x = some {target t x}

-- [proof->req~behavioral-reference-atoms~1]
@[simp] theorem empty_guard (targets : Set U) (rhs : Option (Set U)) :
    Guarded ∅ targets rhs := by simp [Guarded]

theorem nonempty_guard {heads targets : Set U} {rhs : Option (Set U)}
    (present : heads.Nonempty) : Guarded heads targets rhs ↔ rhs = some targets :=
  ⟨fun h => h present, fun h _ => h⟩

theorem undefined_iff_empty (heads targets : Set U) :
    Guarded heads targets none ↔ heads = ∅ := by
  simp [Guarded, Set.not_nonempty_iff_eq_empty]

/-- Reference totality supplies the nonempty target-image premise. A defined
empty set is not undefined, but cannot equal this nonempty image. -/
theorem empty_rhs_rejected {heads targets : Set U}
    (present : heads.Nonempty) (total : targets.Nonempty) :
    ¬ Guarded heads targets (some ∅) := by
  intro h
  have eq := Option.some.inj (h present)
  exact total.ne_empty eq.symm

-- [proof->req~behavioral-snapshot-bridge~1]
theorem starts_constant_live (τ : Trace C U)
    (stable : ∀ t, τ.live t = τ.live 0) (t : Nat) (x : U) :
    τ.Starts t x ↔ x ∈ τ.live 0 ∧ t = 0 := by
  constructor
  · rintro ⟨live, zero | ⟨k, _, absent⟩⟩
    · exact ⟨by simpa only [stable t] using live, zero⟩
    · exact (absent (by simpa only [stable k, stable t] using live)).elim
  · rintro ⟨live, rfl⟩
    exact (τ.starts_zero x).mpr live

-- [proof->req~behavioral-structural-compatibility~1]
/-- Exact collection statement with separate observation-stability hypotheses.
In particular, RHS stability permits `none`; it does not require a value. -/
theorem collection_constant_iff (τ : Trace C U) (contexts : Nat → Set U)
    (heads targets : Nat → U → Set U) (rhs : Nat → U → Option (Set U))
    (live : ∀ t, τ.live t = τ.live 0)
    (context : ∀ t, contexts t = contexts 0)
    (head : ∀ t p, heads t p = heads 0 p)
    (target : ∀ t p, targets t p = targets 0 p)
    (value : ∀ t p, rhs t p = rhs 0 p) :
    (CollectionBirths τ contexts heads targets rhs ↔
      Static (τ.live 0) (contexts 0) (heads 0) (targets 0) (rhs 0)) ∧
    (EveryLive τ contexts heads targets rhs ↔
      Static (τ.live 0) (contexts 0) (heads 0) (targets 0) (rhs 0)) := by
  constructor
  · constructor
    · intro h p hp hl
      exact h 0 p hp ((τ.starts_zero p).mpr hl)
    · intro h t p hp birth
      obtain ⟨hl, rfl⟩ := (starts_constant_live τ live t p).mp birth
      exact h p hp hl
  · constructor
    · intro h p hp hl
      exact h 0 p hp hl
    · intro h t p hp hl
      simpa only [head t p, target t p, value t p] using
        h p (by simpa only [context t] using hp) (by simpa only [live t] using hl)

/-- A single reference is tested at its own births. On constant observations
this agrees with the static singleton equation, hence with every-live equality. -/
theorem single_constant_iff (τ : Trace C U) (heads : Nat → Set U)
    (target : Nat → U → U) (rhs : Nat → U → Option (Set U))
    (live : ∀ t, τ.live t = τ.live 0) (head : ∀ t, heads t = heads 0)
    (targets : ∀ t x, target t x = target 0 x)
    (value : ∀ t x, rhs t x = rhs 0 x) :
    (SingleBirths τ heads target rhs ↔
      Static (τ.live 0) (heads 0) (fun x => {x}) (fun x => {target 0 x}) (rhs 0)) ∧
    (EveryLive τ heads (fun _ x => {x}) (fun t x => {target t x}) rhs ↔
      Static (τ.live 0) (heads 0) (fun x => {x}) (fun x => {target 0 x}) (rhs 0)) := by
  constructor
  · constructor
    · intro h x hx hl _
      exact h 0 x hx ((τ.starts_zero x).mpr hl)
    · intro h t x hx birth
      obtain ⟨hl, rfl⟩ := (starts_constant_live τ live t x).mp birth
      exact h x hx hl (Set.singleton_nonempty x)
  · exact (collection_constant_iff τ heads (fun _ x => {x})
      (fun t x => {target t x}) rhs live head (fun _ _ => rfl)
      (fun t x => congrArg (fun y : U => ({y} : Set U)) (targets t x)) value).2

/-- The existing structural embedding is one concrete supplier of the constant
live trace. Structural validity still requires `constant_valid`'s hypotheses. -/
theorem structural_collection_iff {n : Nat} {m : Semantics.EffectiveCore n}
    {s : Semantics.Configuration (Fin n) U} {ids : Identities (Fin n) U}
    (c : StaticCorrespondence m s ids) (parents : Set U)
    (heads targets : U → Set U) (rhs : U → Option (Set U)) :
    CollectionBirths c.constant (fun _ => parents) (fun _ => heads)
      (fun _ => targets) (fun _ => rhs) ↔ Static Set.univ parents heads targets rhs :=
  (collection_constant_iff c.constant (fun _ => parents) (fun _ => heads)
    (fun _ => targets) (fun _ => rhs) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)).1

-- [proof->req~behavioral-reference-atoms~1]
/-- Connect the independent equation to actual strict primitive equality.
The target observation is defined; the RHS is allowed to be undefined. -/
theorem primitive_equation_iff {k n : Nat} (m : Structural.Core k)
    (τ : Trace (Fin k) U) (R : Constraints.IntegerRealization U) (ρ : Environment U n)
    (t : Nat) (left value : CollectionExpr (Fin k) n) (targets : Set U)
    (hl : PrimitiveExpression.collection m.toEffectiveCore (Structural.observed m τ)
      R ρ t left = some targets) :
    (Formula.atom (.equal left value) : Formula (PrimitiveExpression.Atom (Fin k))
      (CollectionExpr (Fin k)) n).Satisfies τ (.primitives m τ R) true ρ t ↔
    PrimitiveExpression.collection m.toEffectiveCore (Structural.observed m τ)
      R ρ t value = some targets := by
  cases hv : PrimitiveExpression.collection m.toEffectiveCore (Structural.observed m τ)
      R ρ t value with
  | none => simp [Formula.Satisfies, Formula.Defined, PartialObservation.primitives,
      PrimitiveExpression.Atom.eval, hl, hv]
  | some values => simp [Formula.Satisfies, Formula.Defined, Formula.denote, polarity,
      PartialObservation.primitives, PrimitiveExpression.Atom.eval,
      PartialObservation.canonical, PartialObservation.complete, hl, hv, eq_comm]
                   intro _
                   exact ⟨_, Iff.rfl⟩

theorem guarded_primitive_iff {k n : Nat} (m : Structural.Core k)
    (τ : Trace (Fin k) U) (R : Constraints.IntegerRealization U) (ρ : Environment U n)
    (t : Nat) (left value : CollectionExpr (Fin k) n) (heads targets : Set U)
    (hl : PrimitiveExpression.collection m.toEffectiveCore (Structural.observed m τ)
      R ρ t left = some targets) :
    (heads.Nonempty → (Formula.atom (.equal left value) :
      Formula (PrimitiveExpression.Atom (Fin k)) (CollectionExpr (Fin k)) n).Satisfies
        τ (.primitives m τ R) true ρ t) ↔
    Guarded heads targets (PrimitiveExpression.collection m.toEffectiveCore
      (Structural.observed m τ) R ρ t value) := by
  unfold Guarded
  exact imp_congr_right (fun _ => primitive_equation_iff m τ R ρ t left value targets hl)

/-- The old strict Boolean guard rejects an undefined RHS even with no heads.
This is a counterexample to using it for the newly accepted declaration guard. -/
theorem old_constant_rejects_undefined {k n : Nat} (m : Structural.Core k)
    (τ : Trace (Fin k) U) (R : Constraints.IntegerRealization U) (ρ : Environment U n)
    (t : Nat) (heads left value : CollectionExpr (Fin k) n)
    (missing : PrimitiveExpression.collection m.toEffectiveCore (Structural.observed m τ)
      R ρ t value = none) :
    ¬ (Initializers.constant heads left value).Satisfies τ (.primitives m τ R) true ρ t := by
  intro h
  obtain ⟨p, hp⟩ := h.1.2
  simp only [PartialObservation.primitives, PrimitiveExpression.Atom.eval, missing] at hp
  cases PrimitiveExpression.collection m.toEffectiveCore (Structural.observed m τ)
    R ρ t left <;> simp at hp

end Clafer.Behavioral.Initializers.Candidate
