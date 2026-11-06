module

public import Clafer.MCS.Basic

/-!
[impl->req~clafer-mcs-formulas~1]
[proof->req~clafer-mcs-disciplines~1]
[proof->req~clafer-mcs-formulas~1]
[proof->req~clafer-mcs-metamodel~1]
-/

/-! # Appendix 5 boundary laws and composition of typed local Shapes -/

@[expose] public section
namespace Clafer.MCS
open CategoryTheory Clafer.Roles

variable {C V : Type} {f : Family C}

theorem role_cover (x : Role C V f) :
    (∃ c, x = Sum.inl c) ∨ (∃ m, x = Sum.inr m) := by
  cases x with
  | inl c => exact Or.inl ⟨c, rfl⟩
  | inr m => exact Or.inr ⟨m, rfl⟩

theorem role_disjoint (c : V) (m : f.MapId) : (Sum.inl c : Role C V f) ≠ Sum.inr m := by
  intro h; cases h

theorem reference_target_iff (r : ReferenceTo C) : r.target.isSome = true ↔ r.kind ≠ .basic := by
  cases r <;> simp [ReferenceTo.target, ReferenceTo.kind]

/-- Cojoin at resolved owners, without comparing names or taking a quotient. -/
def Family.canonicalVertex (f : Family C) (c : C) (r : (f.shape c).carrier) : C :=
  match r.val with
  | .head => c
  | .source => (f.parent c).getD c
  | .target => (f.reference c).target.getD c

def Family.canonicalRoles (f : Family C) : Roles C C f := ⟨f.canonicalVertex⟩

theorem Family.canonical_cojoining (f : Family C) : f.canonicalRoles.Cojoining where
  head_bijective := Function.bijective_id
  parent c p hp := by simp [canonicalRoles, canonicalVertex, Roles.head, Clafer.Roles.head, Shape.sourceClass, hp]
  target c t ht _ := by simp [canonicalRoles, canonicalVertex, Roles.head, Clafer.Roles.head, Shape.targetClass, ht]

theorem Roles.incidence (r : Roles C V f) {a b : r.graph} (e : a ⟶ b) :
    r.source e.val = a ∧ r.target e.val = b := e.property

/-- A map-role identity already determines both endpoints. Comparing ArrowData
in the bag key therefore adds no extra discrimination beyond MapRole identity. -/
theorem Roles.arrowData_ext (r : Roles C V f)
    (x y : FormalCD.Metamodel.ArrowData r.graph)
    (h : x.2.2.val = y.2.2.val) : x = y := by
  rcases x with ⟨a, b, m, hs, ht⟩
  rcases y with ⟨a', b', m', hs', ht'⟩
  change m = m' at h
  subst m'
  cases hs
  cases ht
  cases hs'
  cases ht'
  rfl

theorem Formulas.sameBag_iff_map_roles {r : Roles C V f}
    {σ : DPGraph.Signature.{0,0,0}} (d : Formulas r σ) (i j : d.Id) :
    d.SameBag i j ↔ ∃ e : d.Arg i ≃ d.Arg j,
      ∀ a, (d.argument j (e a)).2.2.val = (d.argument i a).2.2.val := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, fun a => congrArg (fun x : FormalCD.Metamodel.ArrowData r.graph => x.2.2.val) (he a)⟩
  · rintro ⟨e, he⟩
    exact ⟨e, fun a => r.arrowData_ext _ _ (he a)⟩

theorem Roles.inclusion_incidence (r : Roles C V f) (i : f.InclusionSlot) :
    r.source (.inclusion i) = r.vertex i.1 i.2.2.val.subClass ∧
    r.target (.inclusion i) = r.vertex i.2.1 i.2.2.val.superClass := ⟨rfl, rfl⟩

/-- Corrected source upper bound, including slots with no owners in their image. -/
theorem ordinary_owner_unique {c c' : C}
    {m : Map (f.shape c).kind (f.shape c).hasParent}
    {m' : Map (f.shape c').kind (f.shape c').hasParent}
    (h : Family.MapId.ordinary c m = .ordinary c' m') : c = c' :=
  congrArg Family.MapId.owner h

theorem inclusion_owner_unique {i j : f.InclusionSlot}
    (h : Family.MapId.inclusion i = .inclusion j) : i.1 = j.1 :=
  congrArg Family.MapId.owner h

theorem no_super_no_inclusion {c : C} (h : f.super c = none)
    (i : f.InclusionSlot) : i.1 ≠ c := by
  rintro rfl
  have hi := i.2.2.property
  have he := h.symm.trans hi
  cases he

theorem super_has_head {c s : C} (h : f.super c = some s) :
    ∃ i : f.InclusionSlot, i.1 = c ∧ i.2.1 = s ∧ i.2.2.val.val = .head :=
  ⟨⟨c, s, Shape.headInclusion _ _, h⟩, rfl, rfl, rfl⟩

theorem missing_super_source (i : f.InclusionSlot) (h : f.parent i.2.1 = none) :
    i.2.2.val.val ≠ .source := by
  intro he
  have hp := i.2.2.val.property.2
  simp [Family.shape, h, he, classPresent] at hp

theorem missing_sub_source (i : f.InclusionSlot) (h : f.parent i.1 = none) :
    i.2.2.val.val ≠ .source :=
  Shape.no_source_inclusion (by simp [Family.shape, h]) i.2.2.val

theorem missing_super_target (i : f.InclusionSlot) (h : f.reference i.2.1 = .basic) :
    i.2.2.val.val ≠ .target := by
  intro he
  have hp := i.2.2.val.property.2
  simp [Family.shape, h, he, classPresent, ReferenceTo.kind] at hp

theorem missing_sub_target (i : f.InclusionSlot) (h : f.reference i.1 = .basic) :
    i.2.2.val.val ≠ .target := by
  intro he
  have hp := i.2.2.val.property.1
  simp [Family.shape, h, he, classPresent, ReferenceTo.kind] at hp

theorem root_no_maps (h : f.WellFormed) :
    IsEmpty (Map (f.shape f.root).kind (f.shape f.root).hasParent) := by
  simpa [Family.shape, h.root_shape.1, h.root_shape.2.1, ReferenceTo.kind]
    using Clafer.Roles.root_no_maps

theorem root_has_head (f : Family C) : Nonempty (f.shape f.root).carrier :=
  ⟨head _ _⟩

theorem primitive_no_target (h : f.WellFormed) {c : C} {d : PrimitiveDomain}
    (hd : f.origin c = .primitive d) (r : (f.shape c).carrier) : r.val ≠ .target := by
  intro he
  have hr := r.property
  simp [Family.shape, (h.primitive_shape c d hd).2.1, ReferenceTo.kind, he, classPresent] at hr

theorem primitive_cojoins_root {r : Roles C V f} (h : f.WellFormed)
    (hc : r.Cojoining) {c : C} {d : PrimitiveDomain} (hd : f.origin c = .primitive d) :
    ∃ hp : (f.shape c).hasParent = true,
      r.vertex c (Shape.sourceClass _ hp) = r.head f.root :=
  ⟨by simp [Family.shape, (h.primitive_shape c d hd).1],
    hc.parent c f.root (h.primitive_shape c d hd).1⟩

theorem Family.WellFormed.no_self_parent (h : f.WellFormed) (c : C) :
    f.parent c ≠ some c := by
  obtain ⟨rank, hr⟩ := h.parent_rank
  intro hc
  exact Nat.lt_irrefl _ (hr c c hc)

theorem Family.WellFormed.no_self_super (h : f.WellFormed) (c : C) :
    f.super c ≠ some c := by
  obtain ⟨rank, hr⟩ := h.super_rank
  intro hc
  exact Nat.lt_irrefl _ (hr c c hc)

theorem target_name_via_head {r : Roles C V f} {l : Labels (V := V) f}
    (h : l.WellFormed r) (c : C) (hp : (f.shape c).hasParent = true)
    (ht : (f.shape c).kind ≠ .basic) :
    l.mapName (.ordinary c ⟨.target, by simp [mapPresent, hp, ht]⟩) =
      l.mapName (.ordinary c ⟨.head, hp⟩) ++ "*" := by
  rw [h.ordinary_name, h.ordinary_name]

theorem reserved_names_exclude_users {r : Roles C V f} {l : Labels (V := V) f}
    (h : l.WellFormed r) {c : C} (hc : f.origin c = .user) :
    l.className (r.head c) ≠ "Sing" ∧
      ∀ d, l.className (r.head c) ≠ PrimitiveDomain.name d := by
  constructor
  · intro hs
    have := (h.sing_iff c).mpr hs
    simp [hc] at this
  · intro d hd
    have := (h.primitive_iff c d).mpr hd
    simp [hc] at this

theorem Formulas.no_zero_arrow {r : Roles C V f} {σ : DPGraph.Signature.{0,0,0}}
    {d : Formulas r σ} (h : d.WellFormed) (i : d.Id) [IsEmpty (d.Arg i)] : False :=
  (h.total_args i).elim isEmptyElim

private theorem formula_bag_of_eq {r : Roles C V f} {σ : DPGraph.Signature.{0,0,0}}
    (x y : DPGraph.Formula σ r.graph) (h : x = y) :
    ∃ e : FormalCD.Metamodel.ArrowData (σ.arity x.symbol) ≃
      FormalCD.Metamodel.ArrowData (σ.arity y.symbol),
      ∀ a, (FormalCD.Metamodel.Candidate.ofFormula y).argument (e a) =
        (FormalCD.Metamodel.Candidate.ofFormula x).argument a := by
  subst y
  exact ⟨Equiv.refl _, fun _ => rfl⟩

theorem Formulas.formula_injective {r : Roles C V f} {σ : DPGraph.Signature.{0,0,0}}
    {d : Formulas r σ} (h : d.WellFormed) : Function.Injective d.formula := by
  intro i j he
  exact h.literal_key i j (congrArg DPGraph.Formula.symbol he)
    (formula_bag_of_eq (d.formula i) (d.formula j) he)

/-- Existing local predicates can be transported without losing any binding data.
Their generation and inclusion in a chosen formula bank are separate from shape validity. -/
def Roles.localDiagram (r : Roles C V f) (c : C) : DPGraph DPGraph.Predicates.signature :=
  ⟨r.graph, {φ | ∃ ψ ∈ Shape.declarations (f.shape c), φ = ψ.translate (r.binding c)}⟩

theorem Roles.local_declared (r : Roles C V f) (c : C)
    (φ : DPGraph.Formula DPGraph.Predicates.signature (f.shape c).carrier)
    (h : φ ∈ Shape.declarations (f.shape c)) :
    φ.translate (r.binding c) ∈ (r.localDiagram c).declarations := ⟨φ, h, rfl⟩

end Clafer.MCS
