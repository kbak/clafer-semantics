module

public import Clafer.MCS.Gluing

/-!
[impl->req~clafer-gluing-formalcd~1]
[proof->req~clafer-gluing-formalcd~1]
-/

/-! # Canonical MCS predefined annotations (SoSyM §6.1 and Table 8 (see Appendix 5))

The semantic origins select registry entries. A string is never used to classify
a vertex. MCS naming then proves the registry's canonical naming discipline.
-/

@[expose] public section
namespace Clafer.MCS.Gluing
open CategoryTheory

inductive Predefined where
  | sing | primitive (domain : PrimitiveDomain)
  deriving DecidableEq

def registry : FormalCD.Registry where
  Id := Predefined
  name | .sing => "Sing" | .primitive d => d.name
  kind | .sing => .singleton | .primitive _ => .primitive

def originAnnotation : Origin → Option registry.Id
  | .syntheticRoot => some .sing
  | .primitive d => some (.primitive d)
  | .user => none

/-- The §6.1 / Table 8 annotation retains the semantic origin, including users. -/
private theorem originAnnotation_injective : Function.Injective originAnnotation := by
  intro x y h
  cases x <;> cases y <;> simp_all [originAnnotation, registry]

variable {C V : Type} {f : Family C} {r : Roles C V f} {l : Labels (V := V) f}

/-- Cojoining's head bijection identifies the semantic owner of each class role. -/
noncomputable def annotations (hc : r.Cojoining) (v : V) : Option registry.Id :=
  originAnnotation (f.origin ((Equiv.ofBijective r.head hc.head_bijective).symm v))

@[simp] theorem annotations_head (hc : r.Cojoining) (c : C) :
    annotations hc (r.head c) = originAnnotation (f.origin c) := by
  change originAnnotation (f.origin ((Equiv.ofBijective r.head hc.head_bijective).symm
    ((Equiv.ofBijective r.head hc.head_bijective) c))) = _
  rw [Equiv.symm_apply_apply]

/-- Canonical naming and predefined uniqueness follow from the source disciplines;
default completeness is still a separate hypothesis. -/
theorem naming_of_valid {σ : DPGraph.Signature.{0,0,0}} {d : Formulas r σ}
    (hv : Valid l d) : Naming l (annotations hv.cojoining) where
  predefined_name := by
    intro v i hi
    obtain ⟨c, rfl⟩ := hv.cojoining.head_bijective.2 v
    rw [annotations_head] at hi
    cases i with
    | sing =>
      exact (hv.naming.sing_iff c).mp (originAnnotation_injective hi)
    | primitive dom =>
      exact (hv.naming.primitive_iff c dom).mp (originAnnotation_injective hi)
  user_name := by
    intro v hi
    obtain ⟨c, rfl⟩ := hv.cojoining.head_bijective.2 v
    rw [annotations_head] at hi
    have ho : f.origin c = .user := originAnnotation_injective hi
    rintro ⟨i, he⟩
    cases i with
    | sing => exact (reserved_names_exclude_users hv.naming ho).1 he.symm
    | primitive dom => exact (reserved_names_exclude_users hv.naming ho).2 dom he.symm
  unique_predefined := by
    intro v w i hv' hw'
    obtain ⟨c, rfl⟩ := hv.cojoining.head_bijective.2 v
    obtain ⟨c', rfl⟩ := hv.cojoining.head_bijective.2 w
    rw [annotations_head] at hv' hw'
    have hc : c = c' := by
      cases i with
      | sing =>
        have h₁ : f.origin c = .syntheticRoot := originAnnotation_injective hv'
        have h₂ : f.origin c' = .syntheticRoot := originAnnotation_injective hw'
        exact ((hv.family.root_origin c).mp h₁).trans ((hv.family.root_origin c').mp h₂).symm
      | primitive dom =>
        have h₁ : f.origin c = .primitive dom := originAnnotation_injective hv'
        have h₂ : f.origin c' = .primitive dom := originAnnotation_injective hw'
        exact hv.family.unique_primitive c c' dom h₁ h₂
    subst c'
    rfl
  inclusion_name := by
    intro m hm
    cases m with
    | inclusion i => exact hv.naming.inclusion_name i
    | ordinary c m =>
      simp only [Family.MapId.mode, Clafer.Roles.mode] at hm
      split at hm <;> contradiction

noncomputable def ofValid {W : FormalCD.Vocabulary.{0,0,0}}
    {d : Formulas r W.signature} (hv : Valid l d)
    (h : Compatible r l (annotations hv.cojoining)) (hd : Defaults r d) :
    FormalCD.CDOver W registry := cd h d (naming_of_valid hv) hd

end Clafer.MCS.Gluing
