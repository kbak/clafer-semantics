module

public import Clafer.Semantics.EffectiveCore
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.Nat.Find

/-!
[impl->req~clafer-structural-satisfaction~1]
[proof->req~clafer-structural-satisfaction~1]
-/

/-!
# Declaration ancestry

SoSyM §5.5 and Appendix 5 supply identity-preserving super edges. The global
disjointness clarification adopted in #87 uses their reflexive transitive
closure, independently of names, containment and reference targets.
-/

@[expose] public section
namespace Clafer.Semantics.EffectiveCore

variable {n : Nat} (m : EffectiveCore n)

def Ancestor (d e : Fin n) : Prop :=
  Relation.ReflTransGen (fun d e => m.family.super d = some e) d e

/-- A missing super is a fixed point, adding no distinct ancestor. -/
def next (d : Fin n) : Fin n := (m.family.super d).getD d

theorem ancestor_iff_iterate (d e : Fin n) :
    m.Ancestor d e ↔ ∃ k : Nat, m.next^[k] d = e := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail path edge ih =>
      obtain ⟨k, rfl⟩ := ih
      exact ⟨k + 1, by rw [Function.iterate_succ_apply']; simp [next, edge]⟩
  · rintro ⟨k, rfl⟩
    induction k with
    | zero => exact .refl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      cases h : m.family.super (m.next^[k] d) with
      | none => simpa [next, h] using ih
      | some e => simpa only [next, h, Option.getD_some, Ancestor] using ih.tail h

/-- A first visit uses fewer steps than there are declarations. This bound
holds even for cyclic raw inputs, so decision does not rely on admission. -/
theorem iterate_bounded (f : Fin n → Fin n) (d e : Fin n)
    (h : ∃ k : Nat, f^[k] d = e) : ∃ k : Fin n, f^[k.val] d = e := by
  classical
  let k := Nat.find h
  have hk : f^[k] d = e := Nat.find_spec h
  have minimal : ∀ j < k, f^[j] d ≠ e := fun _ hj => Nat.find_min h hj
  have inj : Function.Injective (fun i : Fin (k + 1) => f^[i.val] d) := by
    suffices ∀ i j : Fin (k + 1), i.val < j.val → f^[i.val] d ≠ f^[j.val] d by
      intro i j he
      rcases lt_trichotomy i.val j.val with hij | hij | hij
      · exact (this i j hij he).elim
      · exact Fin.ext hij
      · exact (this j i hij he.symm).elim
    intro i j hij he
    have hj : j.val ≤ k := by omega
    have short : k - j.val + i.val < k := by omega
    apply minimal _ short
    rw [Function.iterate_add_apply, he, ← Function.iterate_add_apply,
      Nat.sub_add_cancel hj, hk]
  have bound := Fintype.card_le_of_injective _ inj
  simp only [Fintype.card_fin] at bound
  exact ⟨⟨k, by omega⟩, hk⟩

theorem ancestor_iff_bounded (d e : Fin n) :
    m.Ancestor d e ↔ ∃ k : Fin n, m.next^[k.val] d = e := by
  rw [ancestor_iff_iterate]
  exact ⟨iterate_bounded m.next d e, fun ⟨k, hk⟩ => ⟨k.val, hk⟩⟩

instance (d e : Fin n) : Decidable (m.Ancestor d e) :=
  decidable_of_iff (∃ k : Fin n, m.next^[k.val] d = e) (m.ancestor_iff_bounded d e).symm

end Clafer.Semantics.EffectiveCore
