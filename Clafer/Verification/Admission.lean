module

public import Clafer.Verification.Protocol

/-!
# Executable core admission with checked structural certificates

Ranks witness acyclicity without reconstructing source syntax. The unused
abstract certificate is closed under subtypes and contains no concrete class;
it admits empty abstract inheritance chains. Certificates are ordinary input
data checked here, not assumed semantic equivalences or proof certificates
for individual satisfaction verdicts.
-/

@[expose] public section
namespace Clafer.Verification
open Semantics MCS DPGraph.Predicates

deriving instance DecidableEq for ReferenceTo

instance (r : Range) : Decidable (ValidRange r) := by
  unfold ValidRange
  cases r.upper <;> infer_instance

instance (a b : Kind) : Decidable (a.CanExtend b) := by
  unfold Kind.CanExtend
  infer_instance

-- [impl->req~clafer-effective-core~1]
structure CoreCertificate (n : Nat) where
  parentRank : Fin n → Nat
  superRank : Fin n → Nat
  unused : Fin n → Bool

variable {n : Nat}

def coreChecks (m : EffectiveCore n) (k : CoreCertificate n) : Prop :=
  Function.Injective m.id ∧
  (∀ d, m.family.origin d = .syntheticRoot ↔ d = m.family.root) ∧
  (m.family.parent m.family.root = none ∧ m.family.reference m.family.root = .basic ∧
    m.family.super m.family.root = none ∧ m.family.isAbstract m.family.root = false) ∧
  (∀ d p, m.family.parent d = some p → k.parentRank p < k.parentRank d) ∧
  (∀ d p, m.family.super d = some p → k.superRank p < k.superRank d) ∧
  (∀ d, ValidRange (m.family.multiplicity d) ∧ ValidRange (m.group d)) ∧
  (∀ d, m.family.parent d = none → d ≠ m.family.root → m.family.isAbstract d = true)

def supportChecks (m : EffectiveCore n) (k : CoreCertificate n) : Prop :=
  (∀ d, m.family.origin d = .syntheticRoot ∨ m.family.origin d = .user) ∧
  (∀ d, m.family.isAbstract d = true →
    m.family.parent d = none ∧ m.family.reference d = .basic ∧
    (∀ c, m.family.parent c ≠ some d) ∧ m.group d = unrestricted ∧
    (m.family.multiplicity d = unrestricted ∨
      (m.family.multiplicity d = ⟨0, .finite 0⟩ ∧ k.unused d = true))) ∧
  (∀ d s, m.family.super d = some s →
    m.family.isAbstract s = true ∧ m.family.reference d = .basic) ∧
  (∀ d t, (m.family.reference d).target = some t → m.family.origin t = .user) ∧
  (∀ d, 0 < (m.group d).lower → ∃ c, m.family.parent c = some d) ∧
  (∀ d, k.unused d = true → m.family.isAbstract d = true) ∧
  (∀ d s, m.family.super d = some s → k.unused s = true → k.unused d = true)

instance (m : EffectiveCore n) (k : CoreCertificate n) : Decidable (coreChecks m k) := by
  unfold coreChecks Function.Injective
  infer_instance

instance (m : EffectiveCore n) (k : CoreCertificate n) : Decidable (supportChecks m k) := by
  unfold supportChecks
  infer_instance

theorem unused_propagates (m : EffectiveCore n) (k : CoreCertificate n)
    (h : supportChecks m k) {d s : Fin n}
    (path : Relation.TransGen (fun c s => m.family.super c = some s) d s)
    (hs : k.unused s = true) : k.unused d = true := by
  induction path with
  | single edge => exact h.2.2.2.2.2.2 _ _ edge hs
  | tail path edge ih => exact ih (h.2.2.2.2.2.2 _ _ edge hs)

theorem admitted_supported (m : EffectiveCore n) (k : CoreCertificate n)
    (h : supportChecks m k) : m.Supported := by
  refine ⟨h.1, ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  intro d hd
  obtain ⟨hp, hr, hc, hg, hu⟩ := h.2.1 d hd
  refine ⟨hp, hr, hc, hg, ?_⟩
  rcases hu with hu | ⟨hu, hk⟩
  · exact Or.inl hu
  · refine Or.inr ⟨hu, ?_⟩
    intro c hcon path
    have hh := h.2.2.2.2.2.1 c (unused_propagates m k h path hk)
    simp [hcon] at hh

-- [proof->req~clafer-effective-core~1]
theorem admitted_wellFormed (m : EffectiveCore n) (k : CoreCertificate n)
    (h : coreChecks m k) (g : supportChecks m k) : m.WellFormed := by
  refine ⟨?_, h.1, fun d => (h.2.2.2.2.2.1 d).2⟩
  refine {
    root_origin := h.2.1
    root_shape := h.2.2.1
    parent_rank := ⟨k.parentRank, h.2.2.2.1⟩
    super_rank := ⟨k.superRank, h.2.2.2.2.1⟩
    valid_bounds := fun d => (h.2.2.2.2.2.1 d).1
    parentless_abstract := h.2.2.2.2.2.2
    primitive_shape := ?_
    unique_primitive := ?_
    nested_abstract := ?_
    inheritance_kind := ?_
    inheritance_parent := ?_ }
  · intro d dom hd
    rcases g.1 d with he | he <;> rw [he] at hd <;> cases hd
  · intro d e dom hd _
    rcases g.1 d with he | he <;> rw [he] at hd <;> cases hd
  · intro d p hp hd
    rw [(g.2.1 d hd).1] at hp
    cases hp
  · intro d s hs
    obtain ⟨ha, hb⟩ := g.2.2.1 d s hs
    have hsup := (g.2.1 s ha).2.1
    simp [hb, hsup, ReferenceTo.kind, Kind.CanExtend]
  · intro d s hs hp
    exact (hp (g.2.1 s (g.2.2.1 d s hs).1).1).elim

/-- Admission is complete as a checked-certificate interface: every valid
supported core has suitable ranks and an unused-abstract certificate. -/
theorem certificate_exists (m : EffectiveCore n) (wf : m.WellFormed)
    (support : m.Supported) : ∃ k, coreChecks m k ∧ supportChecks m k := by
  classical
  obtain ⟨pr, hp⟩ := wf.1.parent_rank
  obtain ⟨sr, hs⟩ := wf.1.super_rank
  let unused := fun d => m.family.isAbstract d = true ∧
    ∀ c, m.family.isAbstract c = false →
      ¬ Relation.TransGen (fun c s => m.family.super c = some s) c d
  let k : CoreCertificate n := ⟨pr, sr, fun d => decide (unused d)⟩
  refine ⟨k, ⟨wf.2.1, wf.1.root_origin, wf.1.root_shape, hp, hs,
    fun d => ⟨wf.1.valid_bounds d, wf.2.2 d⟩, wf.1.parentless_abstract⟩, ?_⟩
  refine ⟨support.1, ?_, support.2.2.1, support.2.2.2.1, support.2.2.2.2, ?_, ?_⟩
  · intro d hd
    obtain ⟨hp, hr, hc, hg, hm⟩ := support.2.1 d hd
    refine ⟨hp, hr, hc, hg, ?_⟩
    rcases hm with hm | ⟨hm, hu⟩
    · exact Or.inl hm
    · exact Or.inr ⟨hm, by simpa only [k, decide_eq_true_eq] using And.intro hd hu⟩
  · intro d hd
    exact (of_decide_eq_true hd : unused d).1
  · intro d s edge hu
    have hu' : unused s := of_decide_eq_true hu
    apply decide_eq_true
    refine ⟨?_, ?_⟩
    · cases hd : m.family.isAbstract d with
      | true => rfl
      | false => exact (hu'.2 d hd (.single edge)).elim
    · intro c hc path
      exact hu'.2 c hc (path.tail edge)

inductive RunResult where
  | malformedCore
  | unsupportedOrInvalidCertificate
  | candidate (result : Result)
  deriving DecidableEq, Repr

-- [impl->req~clafer-finite-checker~1]
/-- Deterministic entrypoint: check core/rank data, then fragment/unused data,
then candidate tables. No unsupported model receives a satisfaction verdict. -/
def run (m : EffectiveCore n) (k : CoreCertificate n) (c : RawCandidate) : RunResult :=
  if ¬ coreChecks m k then .malformedCore
  else if ¬ supportChecks m k then .unsupportedOrInvalidCertificate
  else .candidate (verify m c)

-- [proof->req~clafer-finite-checker~1]
theorem unsupported_rejected (m : EffectiveCore n) (k : CoreCertificate n)
    (c : RawCandidate) (hc : coreChecks m k) (hs : ¬ m.Supported) :
    run m k c = .unsupportedOrInvalidCertificate := by
  have hn : ¬ supportChecks m k := fun h => hs (admitted_supported m k h)
  simp [run, hc, hn]

end Clafer.Verification
