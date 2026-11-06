module

public import Clafer.Semantics.Structural

/-!
# Abstract coverage in the existing common-target interpretation

SoSyM §5.3.4/§5.5 and Table 3/A.1, using accepted Q8. Non-subtype
positions have empty source subsets; this keeps a fixed finite arity without
inventing inclusion links or imposing unrelated-class disjointness.
-/

@[expose] public section
namespace Clafer.Semantics.Configuration
open DPGraph DPGraph.Predicates

variable {n : Nat} {U : Type} (m : EffectiveCore n) (s : Configuration (Fin n) U)

def subtypeHead (d c : Fin n) : Set U :=
  {x | (x ∈ s.head c) ∧ m.family.super c = some d}

def abstractFan (inh : s.Inherits m) (d c : Fin n) :
    Span (s.subtypeHead m d c) (s.head d) :=
  Span.ofFunction (fun x => ⟨x.val, inh c d x.property.2 x.val x.property.1⟩)

theorem abstract_cover_iff (inh : s.Inherits m) (d : Fin n) :
    Cover (s.abstractFan m inh d) ↔
      ∀ x, (x ∈ s.head d) → ∃ c, m.family.super c = some d ∧ (x ∈ s.head c) := by
  constructor
  · intro h x hx
    obtain ⟨c, l, he⟩ := h ⟨x, hx⟩
    have hx' : l.val = x := congrArg Subtype.val he
    exact ⟨c, l.property.2, hx' ▸ l.property.1⟩
  · intro h x
    obtain ⟨c, hc, hx⟩ := h x.val x.property
    exact ⟨c, ⟨x.val, hx, hc⟩, rfl⟩

theorem abstract_disjoint_iff (inh : s.Inherits m) (d : Fin n) :
    Disjoint (s.abstractFan m inh d) ↔
      ∀ c e, m.family.super c = some d → m.family.super e = some d → c ≠ e →
        ∀ x, ¬ ((x ∈ s.head c) ∧ (x ∈ s.head e)) := by
  constructor
  · intro h c e hc he hce x hx
    exact h c e hce ⟨x, hx.1, hc⟩ ⟨x, hx.2, he⟩ rfl
  · intro h c e hce l k he
    have hx : l.val = k.val := congrArg Subtype.val he
    exact h c e l.property.2 k.property.2 hce l.val
      ⟨l.property.1, hx ▸ k.property.1⟩

-- [proof->req~clafer-structural-satisfaction~1]
theorem abstracts_iff (inh : s.Inherits m) : s.Abstracts m ↔
    ∀ d, m.family.isAbstract d = true →
      Cover (s.abstractFan m inh d) ∧ Disjoint (s.abstractFan m inh d) := by
  simp only [Abstracts, abstract_cover_iff, abstract_disjoint_iff]

end Clafer.Semantics.Configuration
