module

public import Clafer.Semantics.Structural

/-!
# Object renaming

SoSyM B.1/B.5: object identity is preserved by a bijection of the common
ambient carrier. Link renaming for the interpreted maps is separately supplied
by `Span.Iso` and the predicate invariance theorems, including Q1 composition.
-/

@[expose] public section
namespace Clafer.Semantics
open DPGraph.Predicates

variable {n : Nat} {U V : Type}

def Configuration.rename (s : Configuration (Fin n) U) (e : U ≃ V) :
    Configuration (Fin n) V where
  root := e s.root
  head d := {x | e.symm x ∈ s.head d}
  contains d p x := s.contains d (e.symm p) (e.symm x)
  deref d x t := s.deref d (e.symm x) (e.symm t)

def renamedFiber (e : U ≃ V) (P : U → Prop) :
    {x : V // P (e.symm x)} ≃ {x : U // P x} where
  toFun x := ⟨e.symm x.val, x.property⟩
  invFun x := ⟨e x.val, by simpa using x.property⟩
  left_inv x := Subtype.ext (e.apply_symm_apply _)
  right_inv x := Subtype.ext (e.symm_apply_apply _)

theorem inRange_renamed (r : Range) (e : U ≃ V) (P : U → Prop) :
    InRange r {x : V // P (e.symm x)} ↔ InRange r {x : U // P x} :=
  inRange_iff r (renamedFiber e P)

-- [proof->req~clafer-structural-satisfaction~1]
theorem structural_rename (m : EffectiveCore n) (s : Configuration (Fin n) U)
    (e : U ≃ V) : StructuralSatisfies m (s.rename e) ↔ StructuralSatisfies m s := by
  have hg (r : Range) (d : Fin n) (p : U) :
      InRange r {x : V // ∃ c, m.family.parent c = some d ∧ s.contains c p (e.symm x)} ↔
        InRange r {x : U // ∃ c, m.family.parent c = some d ∧ s.contains c p x} :=
    inRange_renamed r e (fun x => ∃ c, m.family.parent c = some d ∧ s.contains c p x)
  unfold StructuralSatisfies Configuration.Typed Configuration.Rooted
    Configuration.Inherits Configuration.Abstracts Configuration.Parents
    Configuration.References Configuration.Keys Configuration.Multiplicities
    Configuration.Groups Configuration.Child Configuration.DeclarationDisjoint Configuration.rename
  simp only [← e.forall_congr_right,
    ← e.existsUnique_congr_right, e.symm_apply_apply, e.injective.eq_iff, inRange_renamed, hg, Set.mem_ofPred_eq]

end Clafer.Semantics
