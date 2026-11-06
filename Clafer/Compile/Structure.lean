module

public import Clafer.MCS.Laws
public import Clafer.Constraints.Typing

/-!
# Structural compilation of resolved declarations

SoSyM §6.2.4 and Tables 5–8 (see Appendix 5). Containment is traversed in preorder;
lookup scans that finite traversal and never recursively follows references.
Names are metadata. Generated class IDs are traversal positions and map IDs are
owner/role pairs. This is a kernel-reducible construction, not a choice of an MCS.
-/

@[expose] public section
namespace Clafer.Compile
open CategoryTheory MCS

/-- Total finite search, with existence supplied by resolved-input validation. -/
noncomputable def find (xs : List Located) (id : DeclId)
    (h : ∃ d ∈ xs, d.declaration.id = id) : Fin xs.length :=
  match xs with
  | [] => False.elim (by simp at h)
  | x :: xs =>
    if hx : x.declaration.id = id then ⟨0, by simp⟩
    else (find xs id (by
      obtain ⟨d, hd, he⟩ := h
      rcases List.mem_cons.mp hd with rfl | hd
      · exact (hx he).elim
      · exact ⟨d, hd, he⟩)).succ

theorem find_spec (xs : List Located) (id : DeclId)
    (h : ∃ d ∈ xs, d.declaration.id = id) :
    xs[find xs id h].declaration.id = id := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    unfold find
    split
    · assumption
    · exact ih _

/-- Constraint bodies are indexed by their actual attached occurrence, not by
strings or a possibly repeated boundary number. No attached boundary is omitted. -/
abbrev ConstraintId (a : AST) := Σ c : a.Occurrence,
  Fin (a.at c).declaration.constraints.length

noncomputable def boundary (a : AST) (i : ConstraintId a) : ConstraintBoundary :=
  (a.at i.1).declaration.constraints[i.2]

-- [impl->req~clafer-compile-contract~1]
/-- Prevalidation required in addition to the existing AST and typing contracts.
The positive-support condition is Compile-specific; generic formulas and
Constraint.Input continue to allow zero-map supports. -/
structure Input (a : AST) where
  ast : a.WellFormed
  root_name : ∀ d ∈ a.entries, d.declaration.origin = .syntheticRoot →
    d.declaration.name = "Sing"
  user_names : ∀ d ∈ a.entries, d.declaration.origin = .user →
    d.declaration.name ∉ MCS.predefinedStrings
  constraint : ConstraintId a → Constraints.Constraint
  typed : ∀ i, (constraint i).Input a (boundary a i)
  positive_support : ∀ i, 0 < (constraint i).support.mapCount

variable {a : AST}

noncomputable def resolve (a : AST) (id : DeclId) (h : a.Known id) : a.Occurrence :=
  find a.entries id h

@[simp] theorem resolve_id (id : DeclId) (h : a.Known id) :
    (a.at (resolve a id h)).declaration.id = id := find_spec _ _ _

noncomputable def sourceId (a : AST) (c : a.Occurrence) : DeclId := (a.at c).declaration.id

theorem sourceId_injective (h : a.WellFormed) : Function.Injective (sourceId a) := by
  intro c d he
  have hn := h.unique_ids
  have he' : (a.entries.map (·.declaration.id))[c.val] =
      (a.entries.map (·.declaration.id))[d.val] := by simpa [sourceId, AST.at] using he
  have := (List.Nodup.getElem_inj_iff hn).mp he'
  exact Fin.ext this

@[simp] theorem resolve_sourceId (h : a.WellFormed) (c : a.Occurrence) :
    resolve a (sourceId a c) ⟨a.at c, List.getElem_mem _, rfl⟩ = c :=
  sourceId_injective h (resolve_id _ _)

/-- Lift an optional resolved edge; the proof only certifies the finite lookup. -/
noncomputable def resolveOption (a : AST) (o : Option DeclId)
    (h : ∀ id, o = some id → a.Known id) : Option a.Occurrence :=
  match o with
  | none => none
  | some id => some (resolve a id (h id rfl))

@[simp] theorem resolveOption_ids (o : Option DeclId) (h) :
    (resolveOption a o h).map (sourceId a) = o := by
  cases o <;> simp [resolveOption, sourceId]

theorem resolveOption_eq_some (h : a.WellFormed) (o : Option DeclId) (ho) (c) :
    resolveOption a o ho = some c ↔ o = some (sourceId a c) := by
  constructor
  · intro he; simpa [he] using (resolveOption_ids o ho).symm
  · intro he
    apply Option.map_injective (sourceId_injective h)
    simp [he]

@[simp] theorem resolveOption_eq_none (o : Option DeclId) (h) :
    resolveOption a o h = none ↔ o = none := by
  cases o <;> simp [resolveOption]

noncomputable def reference (a : AST) (r : Reference)
    (h : ∀ id, r.target = some id → a.Known id) : ReferenceTo a.Occurrence :=
  match r with
  | .basic => .basic
  | .set id => .set (resolve a id (h id rfl))
  | .bag id => .bag (resolve a id (h id rfl))

@[simp] theorem reference_kind (r : Reference) (h) :
    (reference a r h).kind = r.kind := by cases r <;> rfl

@[simp] theorem reference_basic (r : Reference) (h) :
    reference a r h = .basic ↔ r = .basic := by cases r <;> simp [reference]

@[simp] theorem reference_target_ids (r : Reference) (h) :
    (reference a r h).target.map (sourceId a) = r.target := by
  cases r <;> simp [reference, ReferenceTo.target, Reference.target, sourceId]

-- [impl->req~clafer-compile-group-data~1]
noncomputable def family (i : Input a) : Family a.Occurrence where
  parent c := resolveOption a (a.at c).parent
    (i.ast.parent_exists _ (List.getElem_mem _))
  reference c := reference a (a.at c).declaration.reference
    (i.ast.targets_resolved _ (List.getElem_mem _))
  super c := resolveOption a (a.at c).declaration.super
    (i.ast.supers_resolved _ (List.getElem_mem _))
  origin c := (a.at c).declaration.origin
  isAbstract c := (a.at c).declaration.isAbstract
  name c := (a.at c).declaration.name
  multiplicity c := (a.at c).declaration.multiplicity.effective
  root := resolve a a.root i.ast.root_exists
  group c := (a.at c).declaration.group

-- [proof->req~clafer-compile-group-data~1]
/-- Appendix 3 provenance and effective bounds are carried without defaulting
again. This is data preservation, not a group satisfaction theorem. -/
@[simp] theorem group_preserved (i : Input a) (c) :
    (family i).group c = (a.at c).declaration.group := rfl

theorem group_bounds_valid (i : Input a) (c) :
    ValidRange ((family i).group c).effective.range :=
  (i.ast.valid_bounds _ (List.getElem_mem _)).2

@[simp] theorem parent_ids (i : Input a) (c) :
    ((family i).parent c).map (sourceId a) = (a.at c).parent := resolveOption_ids _ _
@[simp] theorem super_ids (i : Input a) (c) :
    ((family i).super c).map (sourceId a) = (a.at c).declaration.super := resolveOption_ids _ _
@[simp] theorem target_ids (i : Input a) (c) :
    ((family i).reference c).target.map (sourceId a) = (a.at c).declaration.reference.target :=
  reference_target_ids _ _

@[simp] theorem parent_eq (i : Input a) (c p) :
    (family i).parent c = some p ↔ (a.at c).parent = some (sourceId a p) :=
  resolveOption_eq_some i.ast _ _ _
@[simp] theorem super_eq (i : Input a) (c s) :
    (family i).super c = some s ↔ (a.at c).declaration.super = some (sourceId a s) :=
  resolveOption_eq_some i.ast _ _ _

/-- The direct-child inventory of §6.2.2. Telematics.Structural-family realization is a
separate interface: this type neither copies children nor selects super paths. -/
abbrev DirectChild (i : Input a) (p : a.Occurrence) :=
  {c : a.Occurrence // (family i).parent c = some p}

theorem directChildren_finite (i : Input a) (p : a.Occurrence) :
    Finite (DirectChild i p) := inferInstance

theorem directChild_iff (i : Input a) (p c : a.Occurrence) :
    (family i).parent c = some p ↔ (a.at c).parent = some (sourceId a p) :=
  parent_eq i c p

/-- Each selected child supplies its head map, including reference children.
The target is the child's own head, never its dereference target. -/
noncomputable def directChildHead (i : Input a) (p : a.Occurrence)
    (c : DirectChild i p) : (family i).canonicalRoles.Arrow p c.val := by
  have hp : ((family i).shape c.val).hasParent = true := by
    simp [Family.shape, c.property]
  refine ⟨.ordinary c.val ⟨.head, hp⟩, ?_, rfl⟩
  change ((family i).parent c.val).getD c.val = p
  simp [c.property]

theorem directChildHead_owner (i : Input a) (p : a.Occurrence)
    (c : DirectChild i p) : (directChildHead i p c).val.owner = c.val := rfl

theorem directChildHead_injective (i : Input a) (p : a.Occurrence) :
    Function.Injective (fun c : DirectChild i p => (directChildHead i p c).val) := by
  intro c d h
  exact Subtype.ext (congrArg Family.MapId.owner h)

-- [proof->req~clafer-compile-contract~1]
theorem family_wellFormed (i : Input a) : (family i).WellFormed where
  root_origin c := by
    change (a.at c).declaration.origin = .syntheticRoot ↔ c = resolve a a.root _
    rw [i.ast.root_origin (a.at c) (List.getElem_mem _)]
    constructor
    · intro h; apply sourceId_injective i.ast; simpa [sourceId] using h
    · rintro rfl; exact resolve_id _ _
  root_shape := by
    have h := i.ast.root_shape _ (List.getElem_mem _) (resolve_id a.root i.ast.root_exists)
    exact ⟨(resolveOption_eq_none _ _).mpr h.1, (reference_basic _ _).mpr h.2.1,
      (resolveOption_eq_none _ _).mpr h.2.2.1, h.2.2.2⟩
  primitive_shape c d hd := by
    have h := i.ast.primitive_shape _ (List.getElem_mem _) d hd
    refine ⟨?_, ?_, ?_⟩
    · apply (parent_eq i c _).mpr
      rw [show sourceId a (family i).root = a.root from resolve_id _ _]
      exact h.1
    · exact (reference_basic _ _).mpr h.2.1
    · exact (resolveOption_eq_none _ _).mpr h.2.2.1
  unique_primitive c d p hc hd := by
    apply sourceId_injective i.ast
    exact congrArg (fun x : Located => x.declaration.id)
      (i.ast.unique_domains _ (List.getElem_mem _) _ (List.getElem_mem _) p hc hd)
  parentless_abstract c hp hc := by
    apply i.ast.parentless_abstract _ (List.getElem_mem _)
      ((resolveOption_eq_none _ _).mp hp)
    intro he
    apply hc
    apply sourceId_injective i.ast
    exact he.trans (resolve_id a.root i.ast.root_exists).symm
  nested_abstract c p hp hc :=
    i.ast.nested_abstract _ (List.getElem_mem _) _ (List.getElem_mem _)
      ((parent_eq i c p).mp hp) hc
  inheritance_kind c s hs := by
    simpa [family, AST.at] using i.ast.inheritance_kind _ (List.getElem_mem _) _ (List.getElem_mem _)
      ((super_eq i c s).mp hs)
  inheritance_parent c s hs hp := by
    apply Option.map_injective (sourceId_injective i.ast)
    simp only [parent_ids]
    apply i.ast.inheritance_parent _ (List.getElem_mem _) _ (List.getElem_mem _)
      ((super_eq i c s).mp hs)
    exact fun he => hp ((resolveOption_eq_none _ _).mpr he)
  parent_rank := ⟨fun c => (a.at c).depth, fun c p hp =>
    i.ast.parent_depth _ (List.getElem_mem _) _ (List.getElem_mem _) ((parent_eq i c p).mp hp)⟩
  super_rank := by
    obtain ⟨rank, hr⟩ := i.ast.inheritance_rank
    exact ⟨fun c => rank (sourceId a c), fun c s hs =>
      hr _ (List.getElem_mem _) _ ((super_eq i c s).mp hs)⟩
  valid_bounds c := (i.ast.valid_bounds _ (List.getElem_mem _)).1

-- [impl->req~clafer-compile-structure~1]
noncomputable def roles (i : Input a) := (family i).canonicalRoles

noncomputable def labels (i : Input a) : Labels (V := a.Occurrence) (family i) where
  ClassRef := DeclId
  MapRef := (family i).MapId
  classReferent := sourceId a
  mapReferent := id
  className := (family i).name
  mapName
    | .ordinary c m => match m.val with
      | .head => (family i).name c | .parent => "parent" | .dereference => "dref"
      | .target => (family i).name c ++ "*"
    | .inclusion _ => "isA"

/-- The canonical primitive names in Table 8 (see Appendix 5) distinguish domains. -/
private theorem primitive_name_injective : Function.Injective PrimitiveDomain.name := by
  intro d e h
  cases d <;> cases e <;> simp_all [PrimitiveDomain.name]

private theorem primitive_name_ne_sing (d : PrimitiveDomain) : d.name ≠ "Sing" := by
  cases d <;> decide

theorem naming (i : Input a) : (labels i).WellFormed (roles i) where
  head_name _ := rfl
  ordinary_name _ _ := rfl
  inclusion_name _ := rfl
  sing_iff c := by
    change (a.at c).declaration.origin = .syntheticRoot ↔ (a.at c).declaration.name = "Sing"
    constructor
    · exact i.root_name _ (List.getElem_mem _)
    · intro hn
      cases ho : (a.at c).declaration.origin with
      | syntheticRoot => rfl
      | primitive d =>
        have hp := (i.ast.primitive_shape _ (List.getElem_mem _) d ho).2.2.2
        exact (primitive_name_ne_sing d (hp.symm.trans hn)).elim
      | user => exact (i.user_names _ (List.getElem_mem _) ho (Or.inl hn)).elim
  primitive_iff c d := by
    change (a.at c).declaration.origin = .primitive d ↔ (a.at c).declaration.name = d.name
    constructor
    · exact fun h => (i.ast.primitive_shape _ (List.getElem_mem _) d h).2.2.2
    · intro hn
      cases ho : (a.at c).declaration.origin with
      | syntheticRoot =>
        have hr := i.root_name _ (List.getElem_mem _) ho
        exact (primitive_name_ne_sing d (hn.symm.trans hr)).elim
      | primitive e =>
        have hp := (i.ast.primitive_shape _ (List.getElem_mem _) e ho).2.2.2
        exact congrArg Origin.primitive (primitive_name_injective (hp.symm.trans hn))
      | user => exact (i.user_names _ (List.getElem_mem _) ho (Or.inr ⟨d, hn⟩)).elim

/-- Every accepted declaration occurs exactly once among the generated heads. -/
theorem heads_bijective (i : Input a) : Function.Bijective (roles i).head :=
  (family i).canonical_cojoining.head_bijective

theorem names_preserved (i : Input a) (c) :
    (labels i).className ((roles i).head c) = (a.at c).declaration.name := rfl

theorem referents_preserved (i : Input a) (c) :
    (labels i).classReferent ((roles i).head c) = sourceId a c := rfl

theorem entry_unique (h : a.WellFormed) {d e : Located}
    (hd : d ∈ a.entries) (he : e ∈ a.entries)
    (hid : d.declaration.id = e.declaration.id) : d = e := by
  obtain ⟨c, rfl⟩ := a.every_entry_indexed d hd
  obtain ⟨c', rfl⟩ := a.every_entry_indexed e he
  exact congrArg a.at (sourceId_injective h hid)

@[simp] theorem target_eq (i : Input a) (c t) :
    ((family i).reference c).target = some t ↔
      (a.at c).declaration.reference.target = some (sourceId a t) := by
  constructor
  · intro he; simpa [he] using (target_ids i c).symm
  · intro he
    apply Option.map_injective (sourceId_injective i.ast)
    simp [he]

-- [proof->req~clafer-compile-structure~1]
theorem shape_preserved (i : Input a) (c : a.Occurrence) :
    (family i).shape c = (a.at c).shape := by
  simp only [Family.shape, family, Located.shape, reference_kind]
  congr 1
  simpa only [Option.isSome_map] using
    congrArg Option.isSome (resolveOption_ids (a := a) (a.at c).parent
      (i.ast.parent_exists _ (List.getElem_mem _)))

end Clafer.Compile
