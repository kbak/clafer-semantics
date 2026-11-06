module

public import Clafer.Behavioral.PartialLowering
public import Clafer.Behavioral.Verification

/-! # Certified finite partial observations

The clock includes initial history. Atom/domain agreement covers every captured
environment and absolute time, including missing observations. No finite table
can represent arbitrary time-dependent or unbounded-history observations without
this proof. Integer arithmetic remains mathematical; a backend range is separate.
-/

@[expose] public section
namespace Clafer.Behavioral

-- [impl->req~behavioral-qualification~1]
structure FinitePartialObservation (A D : Nat → Type) (size last : Nat) where
  atom : ∀ {n}, A n → FiniteEnvironment size n → Lasso.Clock last → Option Bool
  domain : ∀ {n}, D n → FiniteEnvironment size n → Lasso.Clock last → Option (Finset (Fin size))

namespace FinitePartialObservation
variable {A D : Nat → Type} {C : Type} {size last : Nat}

structure Agrees (F : FinitePartialObservation A D size last) (L : Lasso C size last)
    (O : PartialObservation A D (Fin size)) : Prop where
  atom : ∀ {n} (a : A n) ρ t,
    (F.atom a ρ (L.clock t)).map (fun b => b = true) = O.atom a ρ.realize t
  domain : ∀ {n} (d : D n) ρ t,
    (F.domain d ρ (L.clock t)).map (fun S => (↑S : Set (Fin size))) = O.domain d ρ.realize t

def checked (F : FinitePartialObservation A D size last) :
    FiniteObservation (CheckedAtom A D) D size last where
  atom
    | .value a, ρ, s => (F.atom a ρ s).getD false
    | .atomDefined a, ρ, s => (F.atom a ρ s).isSome
    | .domainDefined d, ρ, s => (F.domain d ρ s).isSome
  domain d ρ s := (F.domain d ρ s).getD ∅

-- [proof->req~behavioral-qualification~1]
theorem checked_agrees (F : FinitePartialObservation A D size last)
    (L : Lasso C size last) (O : PartialObservation A D (Fin size)) (h : F.Agrees L O) :
    F.checked.Agrees L O.checked where
  atom a ρ t := by
    cases a with
    | value a =>
      change (F.atom a ρ (L.clock t)).getD false = true ↔ (O.atom a ρ.realize t).getD False
      rw [← h.atom]
      cases F.atom a ρ (L.clock t) with
      | none => simp
      | some b => cases b <;> simp
    | atomDefined a =>
      change (F.atom a ρ (L.clock t)).isSome = true ↔ ∃ p, O.atom a ρ.realize t = some p
      rw [← h.atom]
      cases F.atom a ρ (L.clock t) with
      | none => simp
      | some b => exact ⟨fun _ => ⟨b = true, rfl⟩, fun _ => rfl⟩
    | domainDefined d =>
      change (F.domain d ρ (L.clock t)).isSome = true ↔ ∃ S, O.domain d ρ.realize t = some S
      rw [← h.domain]
      cases F.domain d ρ (L.clock t) <;> simp
  domain d ρ t := by
    change (↑((F.domain d ρ (L.clock t)).getD ∅) : Set (Fin size)) =
      (O.domain d ρ.realize t).getD ∅
    rw [← h.domain]
    cases F.domain d ρ (L.clock t) <;> simp

def ofTotal (F : FiniteObservation A D size last) : FinitePartialObservation A D size last where
  atom a ρ s := some (F.atom a ρ s)
  domain d ρ s := some (F.domain d ρ s)

theorem ofTotal_agrees (F : FiniteObservation A D size last) (L : Lasso C size last)
    (O : Observation A D (Fin size)) (h : F.Agrees L O) :
    (ofTotal F).Agrees L (.ofTotal O) where
  atom a ρ t := by simp [ofTotal, PartialObservation.ofTotal, propext (h.atom a ρ t)]
  domain d ρ t := by simp [ofTotal, PartialObservation.ofTotal, h.domain]

end FinitePartialObservation

-- [impl->req~behavioral-qualification~1]
structure FinitePartialAdapter {A D : Nat → Type} {C : Type} {size last : Nat}
    (L : Lasso C size last) (O : PartialObservation A D (Fin size)) where
  observations : FinitePartialObservation A D size last
  agrees : observations.Agrees L O

namespace Formula
variable {A D : Nat → Type} {C : Type} {size last n : Nat}

-- [impl->req~behavioral-qualification~1]
/-- Executable clients provide syntax and prove it is the source translation.
This does not assume semantic preservation or run a noncomputable normalizer. -/
structure Program (a : Formula A D n) (sign : Bool) where
  domain : Core (CheckedAtom A D) D n
  value : Core (CheckedAtom A D) D n
  domain_eq : domain = a.domainFormula.lower
  value_eq : value = (a.normalize sign).lower.mapAtoms CheckedAtom.value

namespace Program
inductive Result where
  | undefined | violated | satisfied
  deriving DecidableEq, Repr

def check {a : Formula A D n} {sign : Bool} (p : a.Program sign)
    (L : Lasso C size last) (F : FinitePartialObservation A D size last)
    (ρ : FiniteEnvironment size n) (t : Nat) : Result :=
  if p.domain.finite L F.checked ρ (L.clock t) then
    if p.value.finite L F.checked ρ (L.clock t) then .satisfied else .violated
  else .undefined

-- [proof->req~behavioral-qualification~1]
theorem domain_agrees {a : Formula A D n} {sign : Bool} (p : a.Program sign)
    (L : Lasso C size last) {O : PartialObservation A D (Fin size)}
    (F : FinitePartialAdapter L O) (ρ : FiniteEnvironment size n) (t : Nat) :
    p.domain.finite L F.observations.checked ρ (L.clock t) = true ↔
      a.Defined L.unfold O ρ.realize t := by
  rw [Core.finite_agrees L _ _ (F.observations.checked_agrees L O F.agrees),
    p.domain_eq, lower_agrees, domainFormula_agrees]

theorem value_agrees {a : Formula A D n} {sign : Bool} (p : a.Program sign)
    (L : Lasso C size last) {O : PartialObservation A D (Fin size)}
    (F : FinitePartialAdapter L O) (ρ : FiniteEnvironment size n) (t : Nat) :
    p.value.finite L F.observations.checked ρ (L.clock t) = true ↔
      a.denote L.unfold O.canonical sign ρ.realize t := by
  rw [Core.finite_agrees L _ _ (F.observations.checked_agrees L O F.agrees), p.value_eq,
    Core.mapAtoms_agrees L.unfold O.canonical O.checked CheckedAtom.value
      (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => rfl), normalize_lower_agrees]

theorem check_satisfied {a : Formula A D n} {sign : Bool} (p : a.Program sign)
    (L : Lasso C size last) {O : PartialObservation A D (Fin size)}
    (F : FinitePartialAdapter L O) (ρ : FiniteEnvironment size n) (t : Nat) :
    p.check L F.observations ρ t = .satisfied ↔ a.Satisfies L.unfold O sign ρ.realize t := by
  simp only [check, Satisfies, ← p.domain_agrees L F ρ t, ← p.value_agrees L F ρ t]
  split <;> (try split) <;> simp_all

theorem check_undefined {a : Formula A D n} {sign : Bool} (p : a.Program sign)
    (L : Lasso C size last) {O : PartialObservation A D (Fin size)}
    (F : FinitePartialAdapter L O) (ρ : FiniteEnvironment size n) (t : Nat) :
    p.check L F.observations ρ t = .undefined ↔ ¬ a.Defined L.unfold O ρ.realize t := by
  simp only [check, ← p.domain_agrees L F ρ t]
  split <;> simp_all
  split <;> simp_all

theorem check_violated {a : Formula A D n} {sign : Bool} (p : a.Program sign)
    (L : Lasso C size last) {O : PartialObservation A D (Fin size)}
    (F : FinitePartialAdapter L O) (ρ : FiniteEnvironment size n) (t : Nat) :
    p.check L F.observations ρ t = .violated ↔
      a.Defined L.unfold O ρ.realize t ∧ ¬ a.denote L.unfold O.canonical sign ρ.realize t := by
  simp only [check, ← p.domain_agrees L F ρ t, ← p.value_agrees L F ρ t]
  split <;> (try split) <;> simp_all

end Program
end Formula
end Clafer.Behavioral
