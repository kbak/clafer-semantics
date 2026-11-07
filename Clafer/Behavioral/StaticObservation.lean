module

public import Clafer.Behavioral.CapturedStatic
public import Clafer.Behavioral.PartialCompatibility

/-! # Partial static atoms in temporal formulas

The existing typed expression language, including joins and quantification,
is available as an atom/domain family. Resolved binder metadata stays attached
to each expression; lexical depth merely indexes the captured environment.
The binding is chosen at the observation time. Static agreement retains the
live-this, singleton-compatibility and independent typing obligations.
-/

@[expose] public section
namespace Clafer.Behavioral.StaticObservation
open Constraints
universe u w

-- [impl->req~behavioral-reference-atoms~1]
structure Atom (s : Support) (n : Nat) where
  locals : List (Local s)
  arity : locals.length = n
  expression : Expr s locals .boolean

structure Domain (s : Support) (n : Nat) where
  locals : List (Local s)
  arity : locals.length = n
  element : s.Vertex
  expression : Expr s locals (.collection (.objects element))

def Atom.ofExpr {s : Support} {Γ} (e : Expr s Γ .boolean) : Atom s Γ.length := ⟨Γ, rfl, e⟩
def Domain.ofExpr {s : Support} {Γ x} (e : Expr s Γ (.collection (.objects x))) :
    Domain s Γ.length := ⟨Γ, rfl, x, e⟩

noncomputable def observation {s : Support} {U : Type u} (live : Nat → Set U)
    (binding : Nat → IntegerBinding.{u,w} s U) : PartialObservation (Atom s) (Domain s) U where
  atom a ρ t := (CapturedStatic.eval (live t) (binding t) a.expression (a.arity.symm ▸ ρ)).map ULift.down
  domain a ρ t := CapturedStatic.eval (live t) (binding t) a.expression (a.arity.symm ▸ ρ)

-- [proof->req~behavioral-reference-atoms~1]
theorem atom_agrees {s : Support} {U : Type u} (live : Nat → Set U)
    (binding : Nat → IntegerBinding.{u,w} s U) {Γ} (e : Expr s Γ .boolean)
    (ρ : Behavioral.Environment U Γ.length) (σ : Constraints.Environment s U Γ) (t : Nat)
    (same : CapturedStatic.Compatible ρ σ) (present : ρ.this ∈ live t) :
    (observation live binding).atom (.ofExpr e) ρ t = (e.denote (binding t) σ).map ULift.down :=
  congrArg (Option.map ULift.down) (CapturedStatic.agrees _ _ e ρ σ same present)

theorem domain_agrees {s : Support} {U : Type u} (live : Nat → Set U)
    (binding : Nat → IntegerBinding.{u,w} s U) {Γ x} (e : Expr s Γ (.collection (.objects x)))
    (ρ : Behavioral.Environment U Γ.length) (σ : Constraints.Environment s U Γ) (t : Nat)
    (same : CapturedStatic.Compatible ρ σ) (present : ρ.this ∈ live t) :
    (observation live binding).domain (.ofExpr e) ρ t = e.denote (binding t) σ :=
  CapturedStatic.agrees _ _ e ρ σ same present

theorem defined_iff {s : Support} {C : Type} {U : Type u} (τ : Trace C U)
    (binding : Nat → IntegerBinding.{u,w} s U) {Γ} (e : Expr s Γ .boolean)
    (ρ : Behavioral.Environment U Γ.length) (σ : Constraints.Environment s U Γ) (t : Nat)
    (same : CapturedStatic.Compatible ρ σ) (present : ρ.this ∈ τ.live t) :
    (Formula.atom (.ofExpr e)).Defined τ (observation τ.live binding) ρ t ↔
      e.Defined (binding t) σ := by
  unfold Formula.Defined Expr.Defined
  rw [atom_agrees _ _ _ _ _ _ same present]
  cases e.denote (binding t) σ <;> simp
  exact ⟨_, Iff.rfl⟩

theorem signed_atom_agrees {s : Support} {C : Type} {U : Type u} (τ : Trace C U)
    (binding : Nat → IntegerBinding.{u,w} s U) {Γ} (e : Expr s Γ .boolean)
    (ρ : Behavioral.Environment U Γ.length) (σ : Constraints.Environment s U Γ) (t : Nat)
    (same : CapturedStatic.Compatible ρ σ) (present : ρ.this ∈ τ.live t) (sign : Bool) :
    (Formula.atom (.ofExpr e)).Satisfies τ (observation τ.live binding) sign ρ t ↔
      ∃ p, e.denote (binding t) σ = some ⟨p⟩ ∧ polarity sign p := by
  unfold Formula.Satisfies Formula.Defined Formula.denote
  have he := atom_agrees τ.live binding e ρ σ t same present
  simp only [PartialObservation.canonical, PartialObservation.complete, he]
  cases h : e.denote (binding t) σ with
  | none => simp
  | some v =>
    cases v with
    | up p =>
      simp only [Option.map_some, Option.some.injEq, Option.getD_some,
        ULift.up.injEq]
      exact ⟨fun h => ⟨p, rfl, h.2⟩, fun ⟨q, hq, h⟩ => ⟨⟨p, rfl⟩, hq ▸ h⟩⟩

end Clafer.Behavioral.StaticObservation
