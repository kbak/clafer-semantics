module

public import Clafer.Behavioral.PartialLowering
public import Clafer.Behavioral.Properties
public import Clafer.Behavioral.StructuralCompatibility
public import Clafer.Behavioral.Snapshot

/-! # Full source model composition and the static common fragment

Behavioral §5 Definitions 3–5 and §6.1, with the accepted T1–T11 dispositions.
All structural, effective modifier and attached constraint obligations are kept.
The common-fragment theorem retains the old support and group-agreement guards;
the constant converse additionally retains the explicit identity correspondence.
-/

@[expose] public section
namespace Clafer.Behavioral
universe u

namespace Modifiers
variable {k : Nat} {U : Type u}

-- [impl->req~behavioral-qualification~1]
def CoreHolds (m : Structural.Core k) (τ : Trace (Fin k) U)
    (declared : Fin k → Set Modifier) : Prop :=
  ∀ d modifier, Effective m.family declared d modifier →
    ∀ item ∈ expand d modifier, ∀ t x,
      x ∈ item.1.contexts m τ t → x ∈ τ.live t →
      (item.2.normalize true).lower.eval τ
        (.sets m.toEffectiveCore (Structural.observed m τ)) (.closed x) t

-- [proof->req~behavioral-qualification~1]
theorem core_iff (m : Structural.Core k) (τ : Trace (Fin k) U)
    (h : Structural.Valid m τ) (declared : Fin k → Set Modifier) :
    CoreHolds m τ declared ↔ Holds m τ declared := by
  simp only [CoreHolds, ← lower_agrees m τ h]
  constructor
  · intro hm d
    exact ⟨hm d .initial, hm d .final, hm d .finalref, hm d .finaltarget⟩
  · intro hm d modifier
    cases modifier with
    | initial => exact (hm d).1
    | final => exact (hm d).2.1
    | finalref => exact (hm d).2.2.1
    | finaltarget => exact (hm d).2.2.2

theorem holds_empty (m : Structural.Core k) (τ : Trace (Fin k) U) :
    Holds m τ (fun _ => ∅) := by
  simp [Holds, Effective]

end Modifiers

namespace Properties
variable {A D : Nat → Type} {C : Type} {U : Type u} {k : Nat}

-- [impl->req~behavioral-qualification~1]
def modifierConstraint (m : Structural.Core k)
    (item : Modifiers.Placement (Fin k) × Formula (SetAtom (Fin k)) (SetExpr (Fin k)) 0) :
    Constraint (Fin k) (SetAtom (Fin k)) (SetExpr (Fin k)) U :=
  ⟨fun τ => item.1.contexts m τ, item.2⟩

def modifierConstraints (m : Structural.Core k) (declared : Fin k → Set Modifiers.Modifier) :
    Set (Constraint (Fin k) (SetAtom (Fin k)) (SetExpr (Fin k)) U) :=
  {c | ∃ d modifier, Modifiers.Effective m.family declared d modifier ∧
    ∃ item ∈ Modifiers.expand d modifier, c = modifierConstraint m item}

-- [proof->req~behavioral-qualification~1]
theorem modifierConstraints_iff (m : Structural.Core k) (declared : Fin k → Set Modifiers.Modifier)
    (τ : Trace (Fin k) U) (h : Structural.Valid m τ) :
    (∀ c ∈ modifierConstraints m declared, c.Holds τ
      (.ofTotal (.sets m.toEffectiveCore (Structural.observed m τ)))) ↔ Modifiers.Holds m τ declared := by
  rw [← Modifiers.core_iff m τ h]
  simp only [Modifiers.CoreHolds, ← Formula.attached_lower_agrees]
  constructor
  · intro hc d modifier hd item hi t x hx hl
    exact (Formula.total_agrees _ _ _ _ _ _).mp
      (hc (modifierConstraint m item) ⟨d, modifier, hd, item, hi, rfl⟩ t x hx hl)
  · intro hc c ⟨d, modifier, hd, item, hi, he⟩ t x hx hl
    subst c
    exact (Formula.total_agrees _ _ _ _ _ _).mpr (hc d modifier hd item hi t x hx hl)

-- [impl->req~behavioral-qualification~1]
def Constraint.CoreHolds (c : Constraint C A D U) (τ : Trace C U)
    (O : PartialObservation A D U) : Prop :=
  ∀ t x, x ∈ c.contexts τ t → x ∈ τ.live t →
    (c.body.checkedCore true).eval τ O.checked (.closed x) t

-- [proof->req~behavioral-qualification~1]
theorem Constraint.core_iff (c : Constraint C A D U) (τ : Trace C U)
    (O : PartialObservation A D U) : c.CoreHolds τ O ↔ c.Holds τ O := by
  simp only [Constraint.CoreHolds, Formula.checkedCore_agrees,
    Constraint.Holds, Formula.PartialAttached]

-- [proof->req~behavioral-qualification~1]
/-- A single full-model equivalence: effective inherited modifiers and all
strict partial constraints reduce to core obligations on the same trace. -/
theorem Model.behavioral_core_iff (m : Structural.Core k)
    (modifiers : Fin k → Set Modifiers.Modifier)
    (O : Trace (Fin k) U → PartialObservation A D U)
    (constraints : Set (Constraint (Fin k) A D U)) (τ : Trace (Fin k) U) :
    (Model.behavioral m modifiers O constraints).Satisfies τ ↔
      m.WellFormed ∧ Structural.Valid m τ ∧ Modifiers.CoreHolds m τ modifiers ∧
      ∀ c ∈ constraints, c.CoreHolds τ (O τ) := by
  simp only [Model.Satisfies, Model.behavioral, Constraint.core_iff]
  constructor
  · rintro ⟨⟨hw, hv, hm⟩, hc⟩
    exact ⟨hw, hv, (Modifiers.core_iff m τ hv modifiers).mpr hm, hc⟩
  · rintro ⟨hw, hv, hm, hc⟩
    exact ⟨⟨hw, hv, (Modifiers.core_iff m τ hv modifiers).mp hm⟩, hc⟩

-- [proof->req~behavioral-qualification~1]
theorem Model.common_iff {m : Semantics.EffectiveCore k}
    (wf : m.WellFormed) (support : m.Supported)
    (groups : ∀ d, m.group d = (m.family.group d).effective.range)
    (O : Trace (Fin k) U → PartialObservation A D U) (τ : Trace (Fin k) U) :
    (Model.behavioral (Structural.Core.ofEffective m) (fun _ => ∅) O ∅).Satisfies τ ↔
      τ.Valid m := by
  simp only [Model.Satisfies, Model.behavioral,
    Modifiers.holds_empty, and_true, Set.mem_empty_iff_false, false_implies,
    implies_true, Structural.Core.ofEffective_wellFormed wf support groups,
    true_and, Structural.valid_iff_common wf support groups]
  rfl

-- [proof->req~behavioral-qualification~1]
theorem Model.common_snapshot {m : Semantics.EffectiveCore k}
    (wf : m.WellFormed) (support : m.Supported)
    (groups : ∀ d, m.group d = (m.family.group d).effective.range)
    (O : Trace (Fin k) U → PartialObservation A D U) (τ : Trace (Fin k) U)
    (h : (Model.behavioral (Structural.Core.ofEffective m) (fun _ => ∅) O ∅).Satisfies τ)
    (t : Nat) :
    Semantics.StructuralSatisfies m (τ.snapshot ((Model.common_iff wf support groups O τ).mp h) t) :=
  τ.snapshot_structural _ t

-- [proof->req~behavioral-qualification~1]
/-- Exact converse on the stated stable correspondence, without deriving an
identity witness from arbitrary overlapping extents. -/
theorem Model.constant_iff {m : Semantics.EffectiveCore k}
    (wf : m.WellFormed) (support : m.Supported)
    (groups : ∀ d, m.group d = (m.family.group d).effective.range)
    {s : Semantics.Configuration (Fin k) U} {ids : Identities (Fin k) U}
    (c : StaticCorrespondence m s ids)
    (O : Trace (Fin k) U → PartialObservation A D U) :
    (Model.behavioral (Structural.Core.ofEffective m) (fun _ => ∅) O ∅).Satisfies c.constant ↔
      Semantics.StructuralSatisfies m s := by
  rw [Model.common_iff wf support groups]
  refine ⟨fun h => ?_, c.constant_valid⟩
  have hs := h.states 0
  have he := c.constant_raw 0
  rcases hs with ⟨ht, hr, hsep, hi, ha, hp, href, hk, hm, hg, hd⟩
  rw [he] at ht hr hsep hi ha hp href hk hm hg hd
  refine ⟨ht, ⟨?_, ?_, ?_⟩, hi, ha, hp, href, hk, hm, hg, hd⟩
  · simpa only [StaticCorrespondence.constant, c.root] using hr
  · simpa only [StaticCorrespondence.constant, c.root] using hsep
  · intro x
    by_cases hx : x = s.root
    · exact Or.inl hx
    · refine Or.inr ⟨ids.directType x, ?_, (c.head _ x).mpr .refl⟩
      intro ht
      exact hx ((c.identities.root_only x ht).trans c.root)

end Properties
end Clafer.Behavioral
