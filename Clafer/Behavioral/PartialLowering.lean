module

public import Clafer.Behavioral.PartialCompatibility

/-! # Strict partial source meaning in the ordinary temporal core

Behavioral §5 Definition 4, T2/T7 and the adopted D3 strict domain. Definedness
is translated from the original source tree, before signed normalization. In
particular, Boolean short circuits and counting barriers cannot erase it.
-/

@[expose] public section
namespace Clafer.Behavioral
universe u

-- [impl->req~behavioral-qualification~1]
inductive CheckedAtom (A D : Nat → Type) (n : Nat) where
  | value (a : A n)
  | atomDefined (a : A n)
  | domainDefined (d : D n)

def PartialObservation.checked {A D : Nat → Type} {U : Type u}
    (O : PartialObservation A D U) : Observation (CheckedAtom A D) D U where
  atom
    | .value a, ρ, t => O.canonical.atom a ρ t
    | .atomDefined a, ρ, t => ∃ p, O.atom a ρ t = some p
    | .domainDefined d, ρ, t => ∃ S, O.domain d ρ t = some S
  domain := O.canonical.domain

namespace Core
variable {A B D : Nat → Type} {C : Type} {U : Type u}

noncomputable def mapAtoms (f : ∀ {n}, A n → B n) {n} : Core A D n → Core B D n
  | .truth => .truth
  | .atom (.source a) => .atom (.source (f a))
  | .atom .parentPresent => .atom .parentPresent
  | .atom .starts => .atom .starts
  | .atom .ends => .atom .ends
  | .not a => .not (a.mapAtoms f)
  | .and a b => .and (a.mapAtoms f) (b.mapAtoms f)
  | .or a b => .or (a.mapAtoms f) (b.mapAtoms f)
  | .next a => .next (a.mapAtoms f)
  | .eventually a => .eventually (a.mapAtoms f)
  | .always a => .always (a.mapAtoms f)
  | .strongUntil a b => .strongUntil (a.mapAtoms f) (b.mapAtoms f)
  | .weakUntil a b => .weakUntil (a.mapAtoms f) (b.mapAtoms f)
  | .quant q d a => .quant q d (a.mapAtoms f)
  | .letSet d a => .letSet d (a.mapAtoms f)

theorem mapAtoms_agrees (τ : Trace C U) (O : Observation A D U)
    (P : Observation B D U) (f : ∀ {n}, A n → B n)
    (atoms : ∀ n (a : A n) ρ t, P.atom (f a) ρ t ↔ O.atom a ρ t)
    (domains : ∀ n (d : D n) ρ t, P.domain d ρ t = O.domain d ρ t)
    {n} (a : Core A D n) (ρ : Environment U n) (t : Nat) :
    (a.mapAtoms f).eval τ P ρ t ↔ a.eval τ O ρ t := by
  induction a generalizing t with
  | atom a => cases a <;> simp [mapAtoms, eval, atoms]
  | _ => simp_all [mapAtoms, eval, Quantifier.eval, Temporal.next,
      Temporal.eventually, Temporal.always, Temporal.strongUntil, Temporal.weakUntil]

end Core

namespace Formula
variable {A D : Nat → Type} {C : Type} {U : Type u}

-- [impl->req~behavioral-qualification~1]
/-- Domain obligations use all members even for `some`, `no`, `one` and `lone`,
and the entire active parent suffix even for an already-witnessed eventuality. -/
noncomputable def domainFormula {n} : Formula A D n → Formula (CheckedAtom A D) D n
  | .truth => .truth
  | .atom a => .atom (.atomDefined a)
  | .not a => a.domainFormula
  | .and a b | .or a b | .implies a b | .iff a b | .xor a b =>
      .and a.domainFormula b.domainFormula
  | .ite c a b => .and c.domainFormula (.and a.domainFormula b.domainFormula)
  | .next a => .next a.domainFormula
  | .eventually a | .always a => .always a.domainFormula
  | .strongUntil a b | .weakUntil a b => .always (.and a.domainFormula b.domainFormula)
  | .initially a => .initially a.domainFormula
  | .finally a => .finally a.domainFormula
  | .quant _ d a => .and (.atom (.domainDefined d)) (.quant .all d a.domainFormula)
  | .letSet d a => .and (.atom (.domainDefined d)) (.letSet d a.domainFormula)

-- [proof->req~behavioral-qualification~1]
theorem domainFormula_agrees (τ : Trace C U) (O : PartialObservation A D U)
    {n} (a : Formula A D n) (ρ : Environment U n) (t : Nat) :
    a.domainFormula.raw τ O.checked ρ t ↔ a.Defined τ O ρ t := by
  induction a generalizing t with
  | quant _ d a ih | letSet d a ih =>
    simp only [domainFormula, raw, Quantifier.eval, ih, Defined]
    constructor
    · rintro ⟨⟨S, hs⟩, h⟩
      refine ⟨S, hs, ?_⟩
      simpa [PartialObservation.checked, PartialObservation.canonical, PartialObservation.complete, hs] using h
    · rintro ⟨S, hs, h⟩
      refine ⟨⟨S, hs⟩, ?_⟩
      simpa [PartialObservation.checked, PartialObservation.canonical, PartialObservation.complete, hs] using h
  | _ => simp_all [domainFormula, raw, Defined, PartialObservation.checked,
      Lifetime.next, Lifetime.always]

-- [impl->req~behavioral-qualification~1]
/-- Lower the strict source domain and signed truth together. This is a source
translation; executable clients can supply this core with a proved equality. -/
noncomputable def checkedCore {n} (a : Formula A D n) (sign : Bool) : Core (CheckedAtom A D) D n :=
  .and a.domainFormula.lower ((a.normalize sign).lower.mapAtoms CheckedAtom.value)

-- [proof->req~behavioral-qualification~1]
theorem checkedCore_agrees (τ : Trace C U) (O : PartialObservation A D U)
    {n} (a : Formula A D n) (sign : Bool) (ρ : Environment U n) (t : Nat) :
    (a.checkedCore sign).eval τ O.checked ρ t ↔ a.Satisfies τ O sign ρ t := by
  rw [checkedCore, Core.eval, lower_agrees, domainFormula_agrees]
  rw [Core.mapAtoms_agrees τ O.canonical O.checked CheckedAtom.value
    (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => rfl), normalize_lower_agrees]
  rfl

end Formula
end Clafer.Behavioral
