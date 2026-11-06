module

public import Clafer.Compile.Structure

/-!
[impl->req~clafer-compile-formulas~1]
[proof->req~clafer-compile-formulas~1]
-/

/-! # Complete constraint bindings into the compiled role graph (§6.2.2–4) -/

@[expose] public section
namespace Clafer.Compile
open CategoryTheory MCS

variable {a : AST} (i : Input a) (q : ConstraintId a)

noncomputable def support := (i.constraint q).support

noncomputable def vertex (v : (support i q).Vertex) : a.Occurrence :=
  resolve a ((support i q).classId v) ((i.typed q).resolved.classes v)

@[simp] theorem vertex_id (v) : sourceId a (vertex i q v) = (support i q).classId v :=
  resolve_id _ _

theorem owner_known (e : (support i q).Edge) : a.Known ((support i q).mapRef e).owner := by
  obtain ⟨d, hd, ho, _⟩ := (i.typed q).resolved.maps e
  exact ⟨d, hd, ho⟩

noncomputable def mapOwner (e : (support i q).Edge) : a.Occurrence :=
  resolve a ((support i q).mapRef e).owner (owner_known i q e)

/-- Recover the incidence of the uniquely declared owner, without choosing an
alias by name or supplying an output binding as an input assumption. -/
theorem map_spec (e : (support i q).Edge) :
    let d := a.at (mapOwner i q e)
    let s := support i q
    match (s.mapRef e).kind with
    | .head => d.parent = some (s.classId (s.mapRef e).source) ∧
        d.declaration.id = s.classId (s.mapRef e).target
    | .parent => d.declaration.id = s.classId (s.mapRef e).source ∧
        d.parent = some (s.classId (s.mapRef e).target)
    | .dereference => d.declaration.id = s.classId (s.mapRef e).source ∧
        d.declaration.reference.target = some (s.classId (s.mapRef e).target)
    | .target => d.parent = some (s.classId (s.mapRef e).source) ∧
        d.declaration.reference.target = some (s.classId (s.mapRef e).target)
    | .inclusion => d.declaration.id = s.classId (s.mapRef e).source ∧
        d.declaration.super = some (s.classId (s.mapRef e).target) := by
  obtain ⟨d, hd, ho, hm⟩ := (i.typed q).resolved.maps e
  have he : a.at (mapOwner i q e) = d :=
    entry_unique i.ast (List.getElem_mem _) hd ((resolve_id _ _).trans ho.symm)
  cases hk : ((i.constraint q).support.mapRef e).kind <;>
    simpa only [support, he, hk] using hm

/-- Deterministic owner/role allocation; only the inclusion of head classes is
addressable by the current constraint MapRef.inclusion interface. All guarded
source/target inclusions are still present in the structural family. -/
noncomputable def boundArrow (e : (support i q).Edge) : (roles i).Arrow
    (vertex i q ((support i q).mapRef e).source)
    (vertex i q ((support i q).mapRef e).target) := by
  let c := mapOwner i q e
  let x := vertex i q ((support i q).mapRef e).source
  let y := vertex i q ((support i q).mapRef e).target
  have hs := map_spec i q e
  change (roles i).Arrow x y
  match hk : ((support i q).mapRef e).kind with
  | .head =>
    simp only [hk] at hs
    have hp : (family i).parent c = some x := (parent_eq i c x).mpr (by simpa [x] using hs.1)
    have hc : c = y := sourceId_injective i.ast (hs.2.trans (vertex_id i q _).symm)
    refine ⟨.ordinary c ⟨.head, by simpa only [Clafer.Roles.mapPresent, Family.shape, Option.isSome_some] using congrArg Option.isSome hp⟩, ?_, ?_⟩
    · simp [roles, MCS.Roles.source, Family.canonicalRoles, Family.canonicalVertex,
        Clafer.Roles.mapSource, Clafer.Roles.source, hp]
    · exact hc
  | .parent =>
    simp only [hk] at hs
    have hc : c = x := sourceId_injective i.ast (hs.1.trans (vertex_id i q _).symm)
    have hp : (family i).parent c = some y := (parent_eq i c y).mpr (by simpa [y] using hs.2)
    refine ⟨.ordinary c ⟨.parent, by simpa only [Clafer.Roles.mapPresent, Family.shape, Option.isSome_some] using congrArg Option.isSome hp⟩, ?_, ?_⟩
    · exact hc
    · simp [roles, MCS.Roles.target, Family.canonicalRoles, Family.canonicalVertex,
        Clafer.Roles.mapTarget, Clafer.Roles.target, hp]
  | .dereference =>
    simp only [hk] at hs
    have hc : c = x := sourceId_injective i.ast (hs.1.trans (vertex_id i q _).symm)
    have ht : ((family i).reference c).target = some y :=
      (target_eq i c y).mpr (by simpa [y] using hs.2)
    have hr : ((family i).shape c).kind ≠ .basic :=
      (reference_target_iff _).mp (by simp [ht])
    refine ⟨.ordinary c ⟨.dereference, by simpa [Clafer.Roles.mapPresent] using hr⟩, ?_, ?_⟩
    · exact hc
    · simp [roles, MCS.Roles.target, Family.canonicalRoles, Family.canonicalVertex,
        Clafer.Roles.mapTarget, Clafer.Roles.target, ht]
  | .target =>
    simp only [hk] at hs
    have hp : (family i).parent c = some x := (parent_eq i c x).mpr (by simpa [x] using hs.1)
    have ht : ((family i).reference c).target = some y :=
      (target_eq i c y).mpr (by simpa [y] using hs.2)
    have hr : ((family i).shape c).kind ≠ .basic :=
      (reference_target_iff _).mp (by simp [ht])
    refine ⟨.ordinary c ⟨.target, by simp only [Clafer.Roles.mapPresent, Bool.and_eq_true, bne_iff_ne]; exact ⟨by simp [Family.shape, hp], hr⟩⟩, ?_, ?_⟩
    · simp [roles, MCS.Roles.source, Family.canonicalRoles, Family.canonicalVertex,
        Clafer.Roles.mapSource, Clafer.Roles.source, hp]
    · simp [roles, MCS.Roles.target, Family.canonicalRoles, Family.canonicalVertex,
        Clafer.Roles.mapTarget, Clafer.Roles.target, ht]
  | .inclusion =>
    simp only [hk] at hs
    have hc : c = x := sourceId_injective i.ast (hs.1.trans (vertex_id i q _).symm)
    have hsup : (family i).super c = some y := (super_eq i c y).mpr (by simpa [y] using hs.2)
    exact ⟨.inclusion ⟨c, y, Shape.headInclusion _ _, hsup⟩, hc, rfl⟩

noncomputable def binding : (support i q).graph ⥤q (roles i).graph where
  obj := vertex i q
  map e := ⟨(boundArrow i q e.val).val, by
    obtain ⟨hs, ht⟩ := (boundArrow i q e.val).property
    exact ⟨hs.trans (congrArg (vertex i q) e.property.1),
      ht.trans (congrArg (vertex i q) e.property.2)⟩⟩

theorem binding_vertices (v) : sourceId a ((binding i q).obj v) =
    (support i q).classId v := vertex_id i q v

theorem binding_maps (e : (support i q).Edge) :
    ((binding i q).map ((support i q).arrow e)).val = (boundArrow i q e).val := rfl

/-- In particular this retains isolated vertices as well as repeated occurrences. -/
theorem binding_context : (binding i q).obj (support i q).context = q.1 := by
  apply sourceId_injective i.ast
  rw [binding_vertices]
  obtain ⟨hb⟩ := (i.typed q).boundary
  exact hb.context_eq.trans
    (i.ast.constraints_resolved _ (List.getElem_mem _) _ (List.getElem_mem _)).1

end Clafer.Compile
