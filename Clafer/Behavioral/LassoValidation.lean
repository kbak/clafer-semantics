module

public import Clafer.Behavioral.FiniteEvaluation
public import Clafer.Verification.Admission

/-! # Finite lasso admission and structural checks

Reuse the guarded structural model and its finite cardinality bridge, without
requiring absent pool identities to be live snapshot members. Raw frame metadata
is checked against the shared identity inventory; references retain occurrences.
-/

@[expose] public section
namespace Clafer.Behavioral.Lasso
open Semantics Verification
variable {n size last : Nat} (m : EffectiveCore n) (L : Lasso (Fin n) size last)

-- [impl->req~behavioral-lassos~1]
def identityChecks : Prop :=
  L.identities.directType L.identities.root = m.family.root ∧
  (∀ x, L.identities.directType x = m.family.root → x = L.identities.root) ∧
  (∀ x, m.family.isAbstract (L.identities.directType x) = false) ∧
  L.identities.parent L.identities.root = none ∧
  (∀ x, x ≠ L.identities.root → ∃ p, L.identities.parent x = some p) ∧
  (∀ x p, L.identities.parent x = some p → ∃ c,
    m.family.parent (L.identities.directType x) = some c ∧ m.Ancestor (L.identities.directType p) c)

instance : Decidable (identityChecks m L) := by unfold identityChecks; infer_instance

theorem identityChecks_iff : identityChecks m L ↔ L.identities.Valid m := by
  constructor
  · rintro ⟨a, b, c, d, e, f⟩; exact ⟨a, b, c, d, e, f⟩
  · rintro ⟨a, b, c, d, e, f⟩; exact ⟨a, b, c, d, e, f⟩

def candidate (i : Position last) : Verification.Candidate n where
  size := size
  root := L.identities.root
  head d x := L.live i x && decide (m.Ancestor (L.identities.directType x) d)
  contains d p x := L.live i p && L.live i x && decide (L.identities.parent x = some p) &&
    decide (m.Ancestor (L.identities.directType x) d) && decide (m.family.parent d ≠ none)
  deref := L.deref i

theorem candidate_realize (i : Position last) :
    Verification.realize (candidate m L i) = (L.state i).raw m 0 := by
  unfold Verification.realize candidate Trace.raw Trace.ParentAt state
  congr 1
  · funext d; ext x; simp
  · funext d p x; simp [and_assoc]

-- [impl->req~behavioral-lassos~1]
def stateChecks (i : Position last) : Prop :=
  let c := candidate m L i
  (realize c).Typed m ∧
  (∀ x, c.head m.family.root x = true ↔ x = c.root) ∧
  (∀ d, d ≠ m.family.root → c.head d c.root ≠ true) ∧
  (realize c).Inherits m ∧ (realize c).Abstracts m ∧
  (realize c).Parents m ∧ (realize c).References m ∧ (realize c).Keys m ∧
  multiplicityChecks m c ∧ groupChecks m c ∧ (realize c).DeclarationDisjoint m

instance (i : Position last) : Decidable (stateChecks m L i) := by
  unfold stateChecks
  infer_instance

private theorem multiplicity_iff (c : Verification.Candidate n) :
    multiplicityChecks m c ↔ (realize c).Multiplicities m := by
  unfold multiplicityChecks Configuration.Multiplicities realize
  simp only [DPGraph.Predicates.inRange_card, Set.mem_ofPred_eq]

private theorem group_iff (c : Verification.Candidate n) :
    groupChecks m c ↔ (realize c).Groups m := by
  unfold groupChecks Configuration.Groups Configuration.Child realize
  simp only [DPGraph.Predicates.inRange_card, Set.mem_ofPred_eq]

-- [proof->req~behavioral-lassos~1]
theorem stateChecks_iff (i : Position last) :
    stateChecks m L i ↔ (L.state i).StateValid m 0 := by
  have hm : multiplicityChecks m (candidate m L i) ↔
      ((L.state i).raw m 0).Multiplicities m := by
    rw [← candidate_realize]
    exact multiplicity_iff m _
  have hg : groupChecks m (candidate m L i) ↔
      ((L.state i).raw m 0).Groups m := by
    rw [← candidate_realize]
    exact group_iff m _
  dsimp only [stateChecks]
  rw [hm, hg]
  change ((realize (candidate m L i)).Typed m ∧
    (∀ x, x ∈ (realize (candidate m L i)).head m.family.root ↔ x = L.identities.root) ∧
    (∀ d, d ≠ m.family.root → L.identities.root ∉ (realize (candidate m L i)).head d) ∧
    _) ↔ _
  simp only [candidate_realize]
  constructor
  · rintro ⟨a, b, c, d, e, f, g, h, j, k, l⟩; exact ⟨a, b, c, d, e, f, g, h, j, k, l⟩
  · rintro ⟨a, b, c, d, e, f, g, h, j, k, l⟩; exact ⟨a, b, c, d, e, f, g, h, j, k, l⟩

-- [impl->req~behavioral-lassos~1]
def checks : Prop :=
  identityChecks m L ∧ (∀ i, L.live i L.identities.root = true) ∧
  (∀ i x p, L.live i x = true → L.identities.parent x = some p → L.live i p = true) ∧
  ∀ i, stateChecks m L i

instance : Decidable (checks m L) := by unfold checks; infer_instance

-- [proof->req~behavioral-lassos~1]
theorem checks_iff : checks m L ↔ L.Valid m := by
  simp only [checks, Valid, identityChecks_iff, stateChecks_iff]

end Clafer.Behavioral.Lasso

namespace Clafer.Behavioral
-- [impl->req~behavioral-lassos~1]
/-- An exact decoded trace may repeat static metadata in each frame. Those
claims are checked, not used to change identities at a later state. -/
structure RawLasso (n size last : Nat) where
  identities : Identities (Fin n) (Fin size)
  loop : Nat
  directType : Lasso.Position last → Fin size → Fin n
  parent : Lasso.Position last → Fin size → Option (Fin size)
  live : Lasso.Position last → Fin size → Bool
  deref : Lasso.Position last → Fin n → Fin size → Fin size → Bool

namespace RawLasso
variable {n size last : Nat}
def metadata (r : RawLasso n size last) : Prop :=
  (∀ i x, r.directType i x = r.identities.directType x) ∧
  (∀ i x, r.parent i x = r.identities.parent x)
instance (r : RawLasso n size last) : Decidable r.metadata := by unfold metadata; infer_instance

def admit (r : RawLasso n size last) : Option (Lasso (Fin n) size last) :=
  if h : r.loop < last + 1 then
    if r.metadata then some ⟨r.identities, ⟨r.loop, h⟩, r.live, r.deref⟩ else none
  else none

-- [proof->req~behavioral-lassos~1]
theorem admit_none (r : RawLasso n size last) :
    r.admit = none ↔ last + 1 ≤ r.loop ∨ ¬ r.metadata := by
  by_cases h : r.loop < last + 1
  · simp [admit, h, show ¬ last + 1 ≤ r.loop by omega]
  · simp [admit, h, Nat.le_of_not_gt h]
end RawLasso
end Clafer.Behavioral
