module

public import Clafer.MCS.Basic
public import Mathlib.Data.Fintype.Card

-- [impl->req~clafer-effective-core~1]

/-!
# Effective structural input

SoSyM §5.3–5.5, §6.2.2–5 and Appendix 5, restricted to the guarded S
fragment in docs/resolved-ir-comparison.md. No authored/default provenance is
constructed. The finite inventory retains resolved identities separately from names.
-/

@[expose] public section
namespace Clafer.Semantics
open MCS DPGraph.Predicates

structure EffectiveCore (n : Nat) where
  family : Family (Fin n)
  id : Fin n → DeclId
  group : Fin n → Range

namespace EffectiveCore
variable {n : Nat} (m : EffectiveCore n)

def WellFormed : Prop := m.family.WellFormed ∧ Function.Injective m.id ∧
  ∀ d, ValidRange (m.group d)

/-- Version 1 guards. Empty abstract covers are allowed; a zero abstract card
requires no concrete descendant. Raw overlapping class extents remain representable;
satisfaction separately imposes declaration disjointness.
The guard does not assert any property of candidate objects. -/
def Supported : Prop :=
  (∀ d, m.family.origin d = .syntheticRoot ∨ m.family.origin d = .user) ∧
  (∀ d, m.family.isAbstract d = true →
    m.family.parent d = none ∧ m.family.reference d = .basic ∧
    (∀ c, m.family.parent c ≠ some d) ∧ m.group d = unrestricted ∧
    (m.family.multiplicity d = unrestricted ∨
      (m.family.multiplicity d = ⟨0, .finite 0⟩ ∧
        ∀ c, m.family.isAbstract c = false →
          ¬ Relation.TransGen (fun c s => m.family.super c = some s) c d))) ∧
  (∀ d s, m.family.super d = some s →
    m.family.isAbstract s = true ∧ m.family.reference d = .basic) ∧
  (∀ d t, (m.family.reference d).target = some t → m.family.origin t = .user) ∧
  (∀ d, 0 < (m.group d).lower → ∃ c, m.family.parent c = some d)

end EffectiveCore
end Clafer.Semantics
