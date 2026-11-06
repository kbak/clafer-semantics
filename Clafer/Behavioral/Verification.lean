module

public import Clafer.Behavioral.FiniteSets

/-! # Exact behavioral candidate API

These outcomes concern one supplied finite lasso. They make no bounded-UNSAT
claim about all infinite traces. Atom adapters carry source-agreement evidence;
missing finite observation/range evidence is unsupported, never false.
-/

@[expose] public section
namespace Clafer.Behavioral

-- [impl->req~behavioral-finite-checker~1]
structure FiniteAdapter {A D : Nat → Type} {C : Type} {size last : Nat}
    (L : Lasso C size last) (O : Observation A D (Fin size)) where
  observations : FiniteObservation A D size last
  agrees : observations.Agrees L O

namespace FiniteAdapter
def sets {k size last : Nat} (m : Semantics.EffectiveCore k) (L : Lasso (Fin k) size last) :
    FiniteAdapter L (Observation.sets m L.unfold) :=
  ⟨FiniteObservation.sets m L, FiniteObservation.sets_agrees m L⟩
end FiniteAdapter

namespace Verification
open Clafer.Verification
variable {A D : Nat → Type} {n size last depth : Nat}

-- [impl->req~behavioral-finite-checker~1]
inductive Result where
  | malformed
  | unsupported
  | violated
  | satisfied
  deriving DecidableEq, Repr

/-- Core ranks/support are checked using the unchanged guarded admission API.
Undefined primitive observations have no total adapter in this contract. -/
def checkAt (m : Semantics.EffectiveCore n) (cert : CoreCertificate n)
    (L : Lasso (Fin n) size last) {O : Observation A D (Fin size)}
    (adapter : Option (FiniteAdapter L O)) (a : Core A D depth)
    (ρ : FiniteEnvironment size depth) (t : Nat) : Result :=
  if ¬ coreChecks m cert then .malformed
  else if ¬ supportChecks m cert then .unsupported
  else if ¬ L.identityChecks m then .malformed
  else match adapter with
    | none => .unsupported
    | some F => if decide (L.checks m) && a.finite L F.observations ρ (L.clock t)
        then .satisfied else .violated

/-- `none` is an empty/malformed decoded trace. `RawLasso.admit` rejects invalid
loop indices and frame metadata changes before any temporal evaluation. -/
def checkRaw (m : Semantics.EffectiveCore n) (cert : CoreCertificate n)
    (r : Option (RawLasso n size last))
    {O : Lasso (Fin n) size last → Observation A D (Fin size)}
    (adapter : (L : Lasso (Fin n) size last) → Option (FiniteAdapter L (O L)))
    (a : Core A D depth) (ρ : FiniteEnvironment size depth) (t : Nat) : Result :=
  match r.bind RawLasso.admit with
  | none => .malformed
  | some L => checkAt m cert L (adapter L) a ρ t

-- [proof->req~behavioral-finite-checker~1]
theorem checkAt_correct (m : Semantics.EffectiveCore n) (cert : CoreCertificate n)
    (hc : coreChecks m cert) (hs : supportChecks m cert)
    (L : Lasso (Fin n) size last) {O : Observation A D (Fin size)}
    (F : FiniteAdapter L O) (a : Core A D depth) (ρ : FiniteEnvironment size depth) (t : Nat) :
    checkAt m cert L (some F) a ρ t = .satisfied ↔
      L.unfold.Valid m ∧ a.eval L.unfold O ρ.realize t := by
  by_cases hi : L.identityChecks m
  · simp [checkAt, hc, hs, hi, Lasso.checks_iff, Lasso.valid_iff_unfold,
      Core.finite_agrees L F.observations O F.agrees]
  · have hv : ¬ L.unfold.Valid m := fun h => hi ((Lasso.identityChecks_iff m L).mpr h.identities)
    simp [checkAt, hc, hs, hi, hv]

-- [proof->req~behavioral-finite-checker~1]
theorem missing_adapter (m : Semantics.EffectiveCore n) (cert : CoreCertificate n)
    (hc : coreChecks m cert) (hs : supportChecks m cert)
    (L : Lasso (Fin n) size last) (hi : L.identityChecks m)
    (O : Observation A D (Fin size)) (a : Core A D depth) (ρ : FiniteEnvironment size depth) (t : Nat) :
    checkAt m cert L (O := O) none a ρ t = .unsupported := by
  simp [checkAt, hc, hs, hi]
end Verification

namespace Core
variable {A D : Nat → Type} {C : Type} {size last : Nat}

-- [impl->req~behavioral-finite-checker~1]
/-- Implicit always over live applicable contexts, with attachment retained by
all inner binders. Context applicability must have its own source agreement. -/
def attachedFinite (L : Lasso C size last) (F : FiniteObservation A D size last)
    (contexts : Lasso.Clock last → Finset (Fin size)) (a : Core A D 0) : Bool :=
  Orbit.every L.step (fun s => decide (∀ c ∈ contexts s, L.live s.1 c = true →
    a.finite L F (.closed c) s = true)) Lasso.start

-- [proof->req~behavioral-finite-checker~1]
theorem attachedFinite_agrees (L : Lasso C size last) (F : FiniteObservation A D size last)
    (O : Observation A D (Fin size)) (h : F.Agrees L O)
    (contexts : Lasso.Clock last → Finset (Fin size)) (a : Core A D 0) :
    a.attachedFinite L F contexts = true ↔ ∀ t c, c ∈ contexts (L.clock t) →
      c ∈ L.unfold.live t → a.eval L.unfold O (.closed c) t := by
  rw [attachedFinite, Orbit.every_iff]
  constructor
  · intro H t c hc hl
    simpa only [FiniteEnvironment.realize_closed] using
      (finite_agrees L F O h a (.closed c) t).mp ((of_decide_eq_true (H t)) c hc hl)
  · intro H t
    apply decide_eq_true_eq.mpr
    intro c hc hl
    apply (finite_agrees L F O h a (.closed c) t).mpr
    simpa only [FiniteEnvironment.realize_closed] using H t c hc hl

-- [proof->req~behavioral-finite-checker~1]
theorem normalized_attached_agrees (L : Lasso C size last) (F : FiniteObservation A D size last)
    (O : Observation A D (Fin size)) (h : F.Agrees L O)
    (contexts : Lasso.Clock last → Finset (Fin size)) (a : Formula A D 0) :
    (a.normalize true).lower.attachedFinite L F contexts = true ↔
      a.Attached L.unfold O (fun t => ↑(contexts (L.clock t))) := by
  rw [attachedFinite_agrees L F O h]
  exact (Formula.attached_lower_agrees _ _ _ _).symm
end Core
end Clafer.Behavioral
