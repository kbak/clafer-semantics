module

public import Clafer.MCS.Gluing.Examples

/-!
[impl->req~clafer-gluing-examples~1]
[proof->req~clafer-gluing-examples~1]
-/

/-! # Repeated names, bag modes and complete-binding boundaries for Q4 -/

@[expose] public section
namespace Clafer.MCS.Gluing.Boundaries
open CategoryTheory Clafer.Roles DPGraph.Predicates
open Clafer.MCS.Examples

def predef (v : Owner) : Option registry.Id := originAnnotation (family.origin v)

theorem compatible : Compatible roles labels predef where
  source m n h := by have he := MapReferent.resolved.inj h; subst n; rfl
  target m n h := by have he := MapReferent.resolved.inj h; subst n; rfl
  class_name v w h := by have he := ClassReferent.resolved.inj h; subst w; rfl
  map_name m n h := by have he := MapReferent.resolved.inj h; subst n; rfl
  predefined v w h := by have he := ClassReferent.resolved.inj h; subst w; rfl
  mode m n h := by have he := MapReferent.resolved.inj h; subst n; rfl

theorem repeated_parent_not_identified :
    labels.mapName basicParent = labels.mapName setParent ∧
    classLabel labels (roles.source basicParent) ≠
      classLabel labels (roles.source setParent) ∧
    labeledArrow roles labels compatible.toIncidence basicParent ≠
      labeledArrow roles labels compatible.toIncidence setParent := by
  refine ⟨rfl, ?_, ?_⟩
  · intro h; have he := (classLabel_eq_iff _ _ _).mp h; cases he
  · intro h; have he := (labeledArrow_eq_iff _ _ _ _ _).mp h; cases he

theorem repeated_isA_not_identified :
    labels.mapName (.inclusion headIncl) = labels.mapName (.inclusion targetIncl) ∧
    classLabel labels (roles.source (.inclusion headIncl)) ≠
      classLabel labels (roles.source (.inclusion targetIncl)) ∧
    labeledArrow roles labels compatible.toIncidence (.inclusion headIncl) ≠
      labeledArrow roles labels compatible.toIncidence (.inclusion targetIncl) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro h; have he := (classLabel_eq_iff _ _ _).mp h; cases he
  · intro h
    have he := MapReferent.resolved.inj ((labeledArrow_eq_iff _ _ _ _ _).mp h)
    exact repeated_inclusion_names.2 (Family.MapId.inclusion.inj he)

def bagTarget : family.MapId := .ordinary .bag ⟨.target, rfl⟩

theorem bag_mode_preserved :
    (raw (W := FormalCD.Vocabulary.builtins) roles labels predef compatible formulas).mode
      ((label roles labels compatible.toIncidence).map (roleArrow roles bagTarget)) = .bag :=
  mode_label (W := FormalCD.Vocabulary.builtins) compatible formulas (roleArrow roles bagTarget)

/-- A nonempty, structurally valid bank still lacks the ordinary defaults. -/
theorem missing_default_rejected :
    ¬(raw (W := FormalCD.Vocabulary.builtins) roles labels predef compatible formulas).WellFormed := by
  intro h
  have hd := h.ordinary_decl
    ((label roles labels compatible.toIncidence).map (roleArrow roles basicParent))
    (mode_label (W := FormalCD.Vocabulary.builtins) compatible formulas (roleArrow roles basicParent))
  obtain ⟨i, hi⟩ := hd
  have hs := congrArg DPGraph.Formula.symbol hi
  cases i <;> cases hs

theorem bag_has_no_added_setValued :
    FormalCD.setValuedFormula
      ((label roles labels compatible.toIncidence).map (roleArrow roles bagTarget)) ∉
      (diagram roles labels compatible.toIncidence formulas).declarations := by
  rintro ⟨i, hi⟩
  have hs := congrArg DPGraph.Formula.symbol hi
  cases i <;> cases hs

def modeConflict : Labels (V := Owner) family where
  ClassRef := Unit
  MapRef := Unit
  classReferent _ := ()
  mapReferent _ := ()
  className _ := "same"
  mapName _ := "same"

theorem mode_conflict_rejected : ¬Compatible roles modeConflict (fun _ => (none : Option registry.Id)) := by
  intro h
  have he := h.mode bagTarget basicParent rfl
  cases he

/-- Even a reserved spelling cannot assign a predefined identity. This raw
input is rejected by naming, rather than repaired by reclassifying the user. -/
def spellingOnlyLabels : Labels (V := Owner) family :=
  { labels with className := fun _ => "Sing" }

theorem spelling_compatible : Compatible roles spellingOnlyLabels predef :=
  { compatible with class_name := fun _ _ _ => rfl }

theorem spelling_does_not_create_marker :
    (raw (W := FormalCD.Vocabulary.builtins) roles spellingOnlyLabels predef
      spelling_compatible formulas).predefined (classLabel spellingOnlyLabels .basic) = none :=
  predefined_label (W := FormalCD.Vocabulary.builtins) spelling_compatible formulas .basic

theorem reserved_spelling_rejected : ¬Naming spellingOnlyLabels predef := by
  intro h
  exact h.user_name .basic rfl ⟨.sing, rfl⟩

theorem primitive_identity_preserved :
    (raw (W := FormalCD.Vocabulary.builtins) roles labels predef compatible formulas).predefined
      (classLabel labels .int) = some (.primitive .int) :=
  predefined_label (W := FormalCD.Vocabulary.builtins) compatible formulas .int

/-- An explicitly supplied complete bank. Here the author also elects to declare
setValued on the bag target; gluing does not add this declaration. -/
def completeBank : Formulas roles signature where
  Id := family.MapId
  owner := Family.MapId.owner
  formula m := match m with
    | .ordinary _ _ => FormalCD.setValuedFormula (G := roles.graph) (roleArrow roles m)
    | .inclusion _ => FormalCD.inclusionFormula (G := roles.graph) (roleArrow roles m)

def completeArgument (m : family.MapId) : completeBank.Arg m := by
  cases m <;> exact ⟨.source, .target, .arrow⟩

theorem complete_argument_id (m : family.MapId) (a : completeBank.Arg m) :
    (completeBank.argument m a).2.2.val = m := by
  cases m <;> rcases a with ⟨a, b, e⟩ <;> cases e <;> rfl

theorem complete_bank_valid : completeBank.WellFormed where
  total_args m := ⟨completeArgument m⟩
  literal_key i j _ h := by
    obtain ⟨e, he⟩ := h
    have hid := congrArg (fun a : FormalCD.Metamodel.ArrowData roles.graph => a.2.2.val)
      (he (completeArgument i))
    exact (complete_argument_id i (completeArgument i)).symm.trans
      (hid.symm.trans (complete_argument_id j (e (completeArgument i))))

theorem complete_valid : Valid labels completeBank :=
  ⟨family_valid, family.canonical_cojoining, labels_valid, complete_bank_valid⟩

theorem complete_defaults : Defaults (W := FormalCD.Vocabulary.builtins) roles completeBank where
  inclusion m hm := by
    cases m with
    | ordinary c m =>
      simp only [Family.MapId.mode, Clafer.Roles.mode] at hm
      split at hm <;> contradiction
    | inclusion i => exact ⟨.inclusion i, rfl⟩
  ordinary m hm := by
    cases m with
    | ordinary c m => exact ⟨.ordinary c m, rfl⟩
    | inclusion i => cases hm

theorem canonical_naming : Naming labels predef := by
  have he : annotations complete_valid.cojoining = predef := by
    funext c
    exact annotations_head complete_valid.cojoining c
  rw [← he]
  exact naming_of_valid complete_valid

noncomputable def completeCD : FormalCD.CDOver FormalCD.Vocabulary.builtins registry :=
  cd compatible completeBank canonical_naming complete_defaults

theorem inclusion_default_preserved :
    FormalCD.inclusionFormula
      ((label roles labels compatible.toIncidence).map (roleArrow roles (.inclusion headIncl))) ∈
      completeCD.declarations := by
  exact completeCD.wellFormed.inclusion_decl _
    (mode_label (W := FormalCD.Vocabulary.builtins) compatible completeBank
      (roleArrow roles (.inclusion headIncl)))

theorem repeated_arguments_retained : firstArg ≠ secondArg ∧
    ((repeatedArgs.formula ()).translate (label roles labels compatible.toIncidence)).binding.map
      (Arity.OutEdge.edge (0 : Fin 2)) =
    ((repeatedArgs.formula ()).translate (label roles labels compatible.toIncidence)).binding.map
      (Arity.OutEdge.edge (1 : Fin 2)) := ⟨repeated_occurrences_preserved.1, rfl⟩

namespace Isolated
inductive Vertex where | source | target | isolated
inductive Edge : Vertex → Vertex → Type where | arrow : Edge .source .target
instance : Quiver Vertex := ⟨Edge⟩
def signature : DPGraph.Signature := ⟨Unit, fun _ => Quiv.of Vertex⟩

def binding : Quiv.of Vertex ⥤q Examples.roles.graph where
  obj | .source => .root | .target => .left | .isolated => .right
  map | .arrow => roleArrow Examples.roles Examples.leftHead

def bank : Formulas Examples.roles signature where
  Id := Unit
  owner _ := .left
  formula _ := ⟨(), binding⟩

theorem bank_valid : bank.WellFormed where
  total_args _ := ⟨⟨.source, .target, .arrow⟩⟩
  literal_key i j _ _ := by cases i; cases j; rfl

theorem isolated_vertex_retained :
    ((bank.formula ()).translate
      (label Examples.roles Examples.labels Examples.compatible.toIncidence)).binding.obj .isolated =
      classLabel Examples.labels .right := rfl

theorem isolated_declaration_preserved :
    (bank.formula ()).translate
      (label Examples.roles Examples.labels Examples.compatible.toIncidence) ∈
      (diagram Examples.roles Examples.labels Examples.compatible.toIncidence bank).declarations :=
  (labelHom _ _ _ bank).preserves ⟨(), rfl⟩

end Isolated
end Clafer.MCS.Gluing.Boundaries
