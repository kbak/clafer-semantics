module

public import Clafer.Semantics.Interpretation
public import DPGraph.Predicates.Relational

-- [proof->req~clafer-structural-satisfaction~1]

/-!
# Representation lemmas for ordinary maps and occurrence counts

SoSyM B.1 Definitions 1–5, B.2.1 (Q1), Table 3/A.1. The exact-one
predicate is totality and single-valuedness of links, not endpoint reduction.
-/

@[expose] public section
namespace Clafer.Semantics
open DPGraph DPGraph.Predicates

universe u

export DPGraph.Predicates (unique_subtype_iff identity_inclusion_iff compositeFiber
  composite_multiplicity pairSpans two_key_iff pair_key_iff)

theorem inRange_one_iff (A : Type u) :
    InRange Clafer.one A ↔ Nonempty A ∧ Subsingleton A :=
  DPGraph.Predicates.inRange_one_iff A

theorem one_iff_total_single {A B : Type} (q : Span A B) :
    TargetMultiplicity Clafer.one q ↔ Total q ∧ SingleValued q :=
  DPGraph.Predicates.one_iff_total_single q

theorem relation_one_iff {A B : Type} (R : A → B → Prop) :
    TargetMultiplicity Clafer.one (Span.ofRelation R) ↔ ∀ a, ∃! b, R a b :=
  DPGraph.Predicates.relation_one_iff R

theorem setValued_one_iff {A B : Type} (q : Span A B) (hq : SetValued q) :
    TargetMultiplicity Clafer.one q ↔ ∀ a, ∃! b, q.red a b :=
  DPGraph.Predicates.setValued_one_iff q hq

namespace Configuration
variable {n : Nat} {U : Type} (m : EffectiveCore n) (s : Configuration (Fin n) U)

theorem parent_one_iff (typed : s.Typed m) (d p : Fin n)
    (hp : m.family.parent d = some p) :
    TargetMultiplicity Clafer.one (s.headMap m d).inverse ↔
      ∀ x, (x ∈ s.head d) → ∃! y, s.contains d y x := by
  rw [setValued_one_iff _ ((setValued_inverse _).mpr (s.headMap_setValued m d))]
  simp only [Span.red_inverse, headMap, Span.red_ofRelation]
  constructor
  · intro h x hx
    exact (unique_subtype_iff _ _ (fun y hy => by
      obtain ⟨_, c, hc, hcy⟩ := typed.1 d y x hy
      have he := hc.symm.trans hp
      cases he
      simpa [hp] using hcy)).mp (h ⟨x, hx⟩)
  · intro h x
    apply (unique_subtype_iff (s.head ((m.family.parent d).getD d))
      (fun y => s.contains d y x.val) (fun y hy => by
      obtain ⟨_, c, hc, hcy⟩ := typed.1 d y x.val hy
      have he := hc.symm.trans hp
      cases he
      simpa [hp] using hcy)).mpr
    exact h x.val x.property

theorem deref_one_iff (typed : s.Typed m) (d t : Fin n)
    (ht : (m.family.reference d).target = some t) :
    TargetMultiplicity Clafer.one (s.derefMap m d) ↔
      ∀ x, (x ∈ s.head d) → ∃! y, s.deref d x y := by
  unfold derefMap
  rw [relation_one_iff]
  constructor
  · intro h x hx
    exact (unique_subtype_iff _ _ (fun y hy => by
      obtain ⟨_, c, hc, hcy⟩ := typed.2 d x y hy
      have he := hc.symm.trans ht
      cases he
      simpa [ht] using hcy)).mp (h ⟨x, hx⟩)
  · intro h x
    apply (unique_subtype_iff (s.head ((m.family.reference d).target.getD d))
      (fun y => s.deref d x.val y) (fun y hy => by
      obtain ⟨_, c, hc, hcy⟩ := typed.2 d x.val y hy
      have he := hc.symm.trans ht
      cases he
      simpa [ht] using hcy)).mpr
    exact h x.val x.property

end Configuration

end Clafer.Semantics
