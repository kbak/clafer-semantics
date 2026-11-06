module

public import Clafer.MCS.Gluing.Origins
public import Clafer.MCS.Examples

/-! # Q4 acceptance witnesses for SoSyM §6.2.5

These use actual role graphs and complete formula bindings. The positive family
has two distinct user roles denoting one class; their head maps merge while their
parallel parent maps keep different referents. Structural validity and complete
effective defaults are proved separately.
-/

@[expose] public section
namespace Clafer.MCS.Gluing.Examples
open CategoryTheory Clafer.Roles DPGraph.Predicates

inductive Owner where | root | left | right
  deriving DecidableEq

def family : Family Owner where
  root := .root
  parent | .root => none | _ => some .root
  reference _ := .basic
  super _ := none
  origin | .root => .syntheticRoot | _ => .user
  isAbstract _ := false
  name | .root => "Sing" | _ => "item"
  multiplicity _ := one

def roles := family.canonicalRoles
def leftHead : family.MapId := .ordinary .left ⟨.head, rfl⟩
def rightHead : family.MapId := .ordinary .right ⟨.head, rfl⟩
def leftParent : family.MapId := .ordinary .left ⟨.parent, rfl⟩
def rightParent : family.MapId := .ordinary .right ⟨.parent, rfl⟩

theorem maps_cases (m : family.MapId) :
    m = leftHead ∨ m = rightHead ∨ m = leftParent ∨ m = rightParent := by
  cases m with
  | ordinary c m =>
    rcases m with ⟨slot, hp⟩
    cases c <;> cases slot <;> first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr rfl))
      | exact Bool.noConfusion hp
  | inclusion i => have h := i.2.2.property; simp [family] at h

def labels : Labels (V := Owner) family where
  ClassRef := Bool
  MapRef := Option family.MapId
  classReferent | .root => false | _ => true
  mapReferent | .ordinary _ ⟨.head, _⟩ => none | m => some m
  className := family.name
  mapName | .ordinary _ ⟨.head, _⟩ => "item" | _ => "parent"

def predef (v : Owner) : Option registry.Id := originAnnotation (family.origin v)

theorem compatible : Compatible roles labels predef where
  source m n h := by
    rcases maps_cases m with rfl | rfl | rfl | rfl <;>
      rcases maps_cases n with rfl | rfl | rfl | rfl <;> cases h <;> rfl
  target m n h := by
    rcases maps_cases m with rfl | rfl | rfl | rfl <;>
      rcases maps_cases n with rfl | rfl | rfl | rfl <;> cases h <;> rfl
  class_name v w h := by cases v <;> cases w <;> cases h <;> rfl
  map_name m n h := by
    rcases maps_cases m with rfl | rfl | rfl | rfl <;>
      rcases maps_cases n with rfl | rfl | rfl | rfl <;> cases h <;> rfl
  predefined v w h := by cases v <;> cases w <;> cases h <;> rfl
  mode m n _ := by
    rcases maps_cases m with rfl | rfl | rfl | rfl <;>
      rcases maps_cases n with rfl | rfl | rfl | rfl <;> rfl

theorem family_valid : family.WellFormed := by
  constructor
  · intro c; cases c <;> simp [family]
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · intro c d; cases c <;> simp [family]
  · intro c c' d; cases c <;> simp [family]
  · intro c; cases c <;> simp [family]
  · intro c p; cases c <;> simp [family]
  · intro c s; simp [family]
  · intro c s; simp [family]
  · refine ⟨fun c => if c = .root then 0 else 1, ?_⟩
    intro c p; cases c <;> cases p <;> simp [family]
  · exact ⟨fun _ => 0, by intro c s; simp [family]⟩
  · intro c; simp [family, ValidRange, one, Clafer.one]

theorem labels_valid : labels.WellFormed roles where
  head_name _ := rfl
  ordinary_name c m := by
    rcases m with ⟨slot, hp⟩
    cases c <;> cases slot <;> first | rfl | exact Bool.noConfusion hp
  inclusion_name i := by have h := i.2.2.property; simp [family] at h
  sing_iff c := by cases c <;> decide
  primitive_iff c d := by cases c <;> cases d <;> decide

def formulas : Formulas roles signature where
  Id := family.MapId
  owner := Family.MapId.owner
  formula m := FormalCD.setValuedFormula (G := roles.graph) (roleArrow roles m)

def argument (m : family.MapId) : formulas.Arg m := ⟨.source, .target, .arrow⟩

theorem argument_id (m : family.MapId) (a : formulas.Arg m) :
    (formulas.argument m a).2.2.val = m := by
  rcases a with ⟨a, b, e⟩
  cases e
  rfl

theorem formulas_valid : formulas.WellFormed where
  total_args m := ⟨argument m⟩
  literal_key i j _ h := by
    obtain ⟨e, he⟩ := h
    have hid := congrArg (fun a : FormalCD.Metamodel.ArrowData roles.graph => a.2.2.val)
      (he (argument i))
    exact (argument_id i (argument i)).symm.trans
      (hid.symm.trans (argument_id j (e (argument i))))

theorem valid : Valid labels formulas :=
  ⟨family_valid, family.canonical_cojoining, labels_valid, formulas_valid⟩

theorem naming : Naming labels predef := by
  have he : annotations valid.cojoining = predef := by
    funext c
    exact annotations_head valid.cojoining c
  rw [← he]
  exact naming_of_valid valid

theorem defaults : Defaults (W := FormalCD.Vocabulary.builtins) roles formulas where
  inclusion m h := by
    rcases maps_cases m with rfl | rfl | rfl | rfl <;> cases h
  ordinary m _ := ⟨m, rfl⟩

-- [impl->req~clafer-gluing-examples~1]
noncomputable def glued : FormalCD.CDOver FormalCD.Vocabulary.builtins registry :=
  cd compatible formulas naming defaults

-- [proof->req~clafer-gluing-examples~1]
theorem intentional_class_merge : Owner.left ≠ .right ∧
    (label roles labels compatible.toIncidence).obj .left =
      (label roles labels compatible.toIncidence).obj .right := ⟨by decide, rfl⟩

theorem intentional_map_merge : leftHead ≠ rightHead ∧
    labeledArrow roles labels compatible.toIncidence leftHead =
      labeledArrow roles labels compatible.toIncidence rightHead := by
  constructor
  · intro h; cases h
  · exact (labeledArrow_eq_iff _ _ _ _ _).mpr rfl

theorem parallel_maps_distinct :
    classLabel labels (roles.source leftParent) = classLabel labels (roles.source rightParent) ∧
    classLabel labels (roles.target leftParent) = classLabel labels (roles.target rightParent) ∧
    labels.mapName leftParent = labels.mapName rightParent ∧
    labeledArrow roles labels compatible.toIncidence leftParent ≠
      labeledArrow roles labels compatible.toIncidence rightParent := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro h
  have he := (labeledArrow_eq_iff _ _ _ _ _).mp h
  cases he

/-- The literal source key holds, but distinct formulas can coalesce after gluing. -/
theorem translated_formulas_not_injective : ¬Function.Injective
    (fun m => (formulas.formula m).translate (label roles labels compatible.toIncidence)) := by
  intro hi
  have he : (formulas.formula leftHead).translate (label roles labels compatible.toIncidence) =
      (formulas.formula rightHead).translate (label roles labels compatible.toIncidence) :=
    (FormalCD.setValuedFormula_translate (G := roles.graph) (roleArrow roles leftHead)
      (label roles labels compatible.toIncidence)).trans
    (FormalCD.setValuedFormula_translate (G := roles.graph) (roleArrow roles rightHead)
      (label roles labels compatible.toIncidence)).symm
  exact intentional_map_merge.1 (hi he)

theorem canonical_name_preserved : glued.className (classLabel labels .root) = "Sing" :=
  className_label (W := FormalCD.Vocabulary.builtins) compatible formulas .root

theorem registry_kind_preserved :
    (glued.predefined (classLabel labels .root)).map registry.kind = some .singleton := by
  exact kind_label (W := FormalCD.Vocabulary.builtins) compatible formulas .root

/-- An empty bank satisfies the MCS formula discipline but supplies no default. -/
def emptyBank : Formulas roles signature where
  Id := Empty
  owner := Empty.elim
  formula := Empty.elim

theorem empty_valid : Valid labels emptyBank :=
  ⟨family_valid, family.canonical_cojoining, labels_valid,
    ⟨fun i => Empty.elim i, fun i => Empty.elim i⟩⟩

theorem empty_defaults_rejected : ¬Defaults (W := FormalCD.Vocabulary.builtins) roles emptyBank := by
  intro h
  obtain ⟨i, _⟩ := h.ordinary leftHead rfl
  exact Empty.elim i

noncomputable def emptyDPHom := labelHom roles labels compatible.toIncidence emptyBank

theorem empty_cd_rejected :
    ¬(raw (W := FormalCD.Vocabulary.builtins) roles labels predef compatible emptyBank).WellFormed := by
  intro h
  have hd := h.ordinary_decl ((label roles labels compatible.toIncidence).map (roleArrow roles leftHead))
    (mode_label (W := FormalCD.Vocabulary.builtins) compatible emptyBank (roleArrow roles leftHead))
  obtain ⟨i, _⟩ := hd
  exact Empty.elim i

/-- Identifying every map breaks both endpoint congruences. -/
def badEndpoints : Labels (V := Owner) family := { labels with mapReferent := fun _ => none }

theorem source_conflict_rejected : ¬Incidence roles badEndpoints := by
  intro h
  have he := h.source leftHead leftParent rfl
  cases he

theorem target_conflict_rejected : ¬Incidence roles badEndpoints := by
  intro h
  have he := h.target leftHead leftParent rfl
  cases he

def badClassNames : Labels (V := Owner) family :=
  { labels with className := fun c => if c = .left then "left" else "right" }

theorem class_name_conflict_rejected : ¬Compatible roles badClassNames predef := by
  intro h
  have he := h.class_name .left .right rfl
  exact (by decide : "left" ≠ "right") he

def badMapNames : Labels (V := Owner) family :=
  { labels with mapName := fun m => match m with
      | .ordinary .left _ => "left" | _ => "right" }

theorem map_name_conflict_rejected : ¬Compatible roles badMapNames predef := by
  intro h
  have he := h.map_name leftHead rightHead rfl
  exact (by decide : "left" ≠ "right") he

def badAnnotation : Owner → Option registry.Id
  | .left => some .sing | .right => some (.primitive .int) | .root => none

theorem annotation_and_kind_conflict_rejected : ¬Compatible roles labels badAnnotation := by
  intro h
  have he := h.predefined .left .right rfl
  cases he

end Clafer.MCS.Gluing.Examples
