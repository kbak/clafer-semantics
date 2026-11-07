module

public import Clafer.Behavioral.Denotation

/-!
# Signed normalization before lifetime lowering

Pinned T2 and `AlloyLtl.pushNegations` supply the comparison rules. This
normalizer is independent of that compiler's IR. Classical, temporal-free
subtrees may be distributed as well; no meaning relies on preserving their
surface spelling. one/lone preserve the entire raw counting body as a barrier.
-/

@[expose] public section
namespace Clafer.Behavioral.Formula
variable {A D : Nat → Type}

-- [impl->req~behavioral-signed-normalization~1]
noncomputable def normalize {n} : Formula A D n → Bool → Formula A D n
  | .truth, s => if s then .truth else .not .truth
  | .atom a, s => if s then .atom a else .not (.atom a)
  | .not a, s => a.normalize (!s)
  | .and a b, s => if s then .and (a.normalize true) (b.normalize true)
      else .or (a.normalize false) (b.normalize false)
  | .or a b, s => if s then .or (a.normalize true) (b.normalize true)
      else .and (a.normalize false) (b.normalize false)
  | .implies a b, s => if s then .or (a.normalize false) (b.normalize true)
      else .and (a.normalize true) (b.normalize false)
  | .iff a b, s => if s then
      .and (.or (a.normalize false) (b.normalize true)) (.or (b.normalize false) (a.normalize true))
      else .or (.and (a.normalize true) (b.normalize false)) (.and (b.normalize true) (a.normalize false))
  | .xor a b, s => if s then
      .or (.and (a.normalize true) (b.normalize false)) (.and (a.normalize false) (b.normalize true))
      else .and (.or (a.normalize false) (b.normalize true)) (.or (a.normalize true) (b.normalize false))
  | .ite c a b, s => if s then
      .and (.or (c.normalize false) (a.normalize true)) (.or (c.normalize true) (b.normalize true))
      else .or (.and (c.normalize true) (a.normalize false)) (.and (c.normalize false) (b.normalize false))
  | .next a, s => .next (a.normalize s)
  | .eventually a, s => if s then .eventually (a.normalize true) else .always (a.normalize false)
  | .always a, s => if s then .always (a.normalize true) else .eventually (a.normalize false)
  | .strongUntil a b, s => if s then .strongUntil (a.normalize true) (b.normalize true)
      else .weakUntil (b.normalize false) (.and (a.normalize false) (b.normalize false))
  | .weakUntil a b, s => if s then .weakUntil (a.normalize true) (b.normalize true)
      else .strongUntil (b.normalize false) (.and (a.normalize false) (b.normalize false))
  | .initially a, s => .initially (a.normalize s)
  | .finally a, s => .finally (a.normalize s)
  | .quant .all d a, s => if s then .quant .all d (a.normalize true)
      else .quant .some d (a.normalize false)
  | .quant .some d a, s => if s then .quant .some d (a.normalize true)
      else .quant .all d (a.normalize false)
  | .quant .no d a, s => if s then .quant .all d (a.normalize false)
      else .quant .some d (a.normalize true)
  | .quant .one d a, s => if s then .quant .one d a else .not (.quant .one d a)
  | .quant .lone d a, s => if s then .quant .lone d a else .not (.quant .lone d a)
  | .letSet d a, s => .letSet d (a.normalize s)

-- [proof->req~behavioral-signed-normalization~1]
/-- All constructors, both signs, all environments/times. No compiler/evaluator
agreement premise is assumed: induction checks the actual translation. -/
theorem normalize_agrees {C : Type} {U : Type u} (τ : Trace C U)
    (O : Observation A D U) {n} (a : Formula A D n) (s : Bool)
    (ρ : Environment U n) (t : Nat) :
    (a.normalize s).raw τ O ρ t ↔ a.denote τ O s ρ t := by
  induction a generalizing s t with
  | quant q d a ih => cases q <;> cases s <;> simp [normalize, raw, denote, polarity, Quantifier.eval, ih]
  | _ => cases s <;> simp_all [normalize, raw, denote, polarity, Lifetime.next, Lifetime.eventually,
      Lifetime.always, Lifetime.strongUntil, Lifetime.weakUntil]

-- [impl->req~behavioral-signed-normalization~1]
/-- Normal form outside one/lone barriers; their bodies are deliberately raw. -/
noncomputable def Normal {n} : Formula A D n → Prop
  | .truth | .atom _ | .not .truth | .not (.atom _) => True
  | .quant .one _ _ | .quant .lone _ _ | .not (.quant .one _ _) | .not (.quant .lone _ _) => True
  | .and a b | .or a b | .strongUntil a b | .weakUntil a b => a.Normal ∧ b.Normal
  | .next a | .eventually a | .always a | .initially a | .finally a => a.Normal
  | .quant .all _ a | .quant .some _ a | .letSet _ a => a.Normal
  | _ => False

-- [proof->req~behavioral-signed-normalization~1]
theorem normalize_normal {n} (a : Formula A D n) (s : Bool) : (a.normalize s).Normal := by
  induction a generalizing s with
  | quant q d a ih => cases q <;> cases s <;> simp_all [normalize, Normal]
  | _ => cases s <;> simp_all [normalize, Normal]

/-- No temporal/anchor constructors. Counting barriers can still contain them,
so their bodies must be inspected for this stronger property. -/
noncomputable def TemporalFree {n} : Formula A D n → Prop
  | .truth | .atom _ => True
  | .not a | .quant _ _ a | .letSet _ a => a.TemporalFree
  | .and a b | .or a b | .implies a b | .iff a b | .xor a b => a.TemporalFree ∧ b.TemporalFree
  | .ite c a b => c.TemporalFree ∧ a.TemporalFree ∧ b.TemporalFree
  | _ => False

-- [proof->req~behavioral-signed-normalization~1]
/-- Classical signs on total temporal-free observations justify distributing
these subtrees and retaining classical non-temporal guards. -/
theorem temporalFree_polarity {C : Type} {U : Type u} (τ : Trace C U)
    (O : Observation A D U) {n} (a : Formula A D n) (h : a.TemporalFree)
    (s : Bool) (ρ : Environment U n) (t : Nat) :
    a.denote τ O s ρ t ↔ polarity s (a.raw τ O ρ t) := by
  classical
  induction a generalizing s with
  | quant q d a ih =>
    cases q <;> cases s <;> simp_all [TemporalFree, denote, raw, polarity, Quantifier.eval]
  | _ => cases s <;> simp_all [TemporalFree, denote, raw, polarity] <;> tauto
end Clafer.Behavioral.Formula
