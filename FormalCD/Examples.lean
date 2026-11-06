module

public import FormalCD
public import Mathlib.Data.Fintype.EquivFin

/-!
[impl->req~formalcd-examples~1]
[proof->req~formalcd-declarations~1]
[proof->req~formalcd-examples~1]
[proof->req~formalcd-morphisms~1]
[proof->req~formalcd-naming~1]
[proof->req~formalcd-structure~1]
-/

/-!
# Checked boundaries for the first FormalCD increment

Finite syntax inspired by SoSyM §6.1.1–3, without encoding Figure 21c.
Names may repeat; graph identities and predefined identifiers remain distinct.
All failures below concern actual obligations or concrete satisfaction.
-/

@[expose] public section

namespace FormalCD.Examples

open CategoryTheory DPGraph.Predicates

inductive Builtin where
  | one | int | string | bool
  deriving DecidableEq

def registry : Registry where
  Id := Builtin
  name | .one => "*" | .int => "Int" | .string => "String" | .bool => "Bool"
  kind | .one => .singleton | .int | .string | .bool => .primitive

inductive Class where
  | left | right | top | one
  deriving DecidableEq

inductive Arrow : Class → Class → Type where
  | leftIn : Arrow .left .top
  | rightIn : Arrow .right .top
  | values : Arrow .top .one
  | bag : Arrow .top .one

instance : Quiver Class := ⟨Arrow⟩
def graph : Quiv := Quiv.of Class

def totalFormula : DPGraph.Formula signature graph :=
  ⟨.total, arrowBinding Arrow.values⟩

def declarations : Set (DPGraph.Formula signature graph) :=
  {φ | φ = inclusionFormula Arrow.leftIn ∨ φ = inclusionFormula Arrow.rightIn ∨
    φ = setValuedFormula Arrow.values ∨ φ = totalFormula}

def raw : Raw registry where
  carrier := graph
  declarations := declarations
  className | .left | .right => "Node" | .top => "Object" | .one => "*"
  mapName | .leftIn | .rightIn => "isA" | .values => "values" | .bag => "bag"
  predefined | .one => some .one | _ => none
  mode | .leftIn | .rightIn => .inclusion | .values => .ordinary | .bag => .bag

theorem wellFormed : raw.WellFormed where
  predefined_name := by intro c i h; cases c <;> cases h; rfl
  user_name := by
    intro c h ⟨i, hi⟩
    cases c <;> cases i <;> simp_all [raw, registry]
  unique_predefined := by
    intro c d i hc hd
    cases c <;> cases hc
    cases d <;> cases hd
    rfl
  inclusion_name := by intro a b e h; cases e <;> simp_all [raw]
  inclusion_decl := by
    intro a b e h
    cases e with
    | leftIn => exact Or.inl rfl
    | rightIn => exact Or.inr (Or.inl rfl)
    | values => cases h
    | bag => cases h
  ordinary_decl := by
    intro a b e h
    cases e with
    | leftIn => cases h
    | rightIn => cases h
    | values => exact Or.inr (Or.inr (Or.inl rfl))
    | bag => cases h

def diagram : CD registry := ⟨raw, wellFormed⟩

instance : Fintype Class where
  elems := {.left, .right, .top, .one}
  complete c := by cases c <;> simp

theorem finite_vertices : Finite graph := by
  change Finite Class
  infer_instance

theorem finite_arrows : Finite (Σ a b : graph, a ⟶ b) := by
  classical
  let : Fintype (Σ a b : graph, a ⟶ b) :=
    { elems := {⟨.left, .top, Arrow.leftIn⟩, ⟨.right, .top, Arrow.rightIn⟩,
        ⟨.top, .one, Arrow.values⟩, ⟨.top, .one, Arrow.bag⟩}
      complete := by rintro ⟨a, b, e⟩; cases e <;> simp }
  infer_instance

theorem distinct_inclusions :
    (⟨.left, .top, Arrow.leftIn⟩ : Σ a b : graph, a ⟶ b) ≠
      ⟨.right, .top, Arrow.rightIn⟩ := by
  intro h; have he := congrArg Sigma.fst h; cases he

theorem shared_inclusion_name :
    diagram.mapName Arrow.leftIn = "isA" ∧ diagram.mapName Arrow.rightIn = "isA" :=
  ⟨rfl, rfl⟩

theorem inclusion_endpoints :
    (inclusionFormula (G := graph) Arrow.leftIn).binding.obj .source = Class.left ∧
    (inclusionFormula (G := graph) Arrow.rightIn).binding.obj .source = Class.right ∧
    (inclusionFormula (G := graph) Arrow.leftIn).binding.obj .target = Class.top ∧
    (inclusionFormula (G := graph) Arrow.rightIn).binding.obj .target = Class.top :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem required_inclusions :
    inclusionFormula Arrow.leftIn ∈ diagram.declarations ∧
    inclusionFormula Arrow.rightIn ∈ diagram.declarations :=
  ⟨wellFormed.inclusion_decl _ rfl, wellFormed.inclusion_decl _ rfl⟩

theorem ordinary_default : setValuedFormula Arrow.values ∈ diagram.declarations :=
  wellFormed.ordinary_decl _ rfl

/-- Same endpoints do not identify these two arrows or their formulas. -/
theorem no_bag_default : setValuedFormula Arrow.bag ∉ diagram.declarations := by
  rintro (h | h | h | h)
  · have he := congrArg DPGraph.Formula.symbol h; cases he
  · have he := congrArg DPGraph.Formula.symbol h; cases he
  · have hb : arrowBinding (G := graph) Arrow.bag = arrowBinding (G := graph) Arrow.values := by
      injection h
    have he : Arrow.bag = Arrow.values := Prefunctor.congr_hom hb Arity.UnaryEdge.arrow
    cases he
  · have he := congrArg DPGraph.Formula.symbol h; cases he

theorem user_declaration_retained : totalFormula ∈ diagram.declarations :=
  Or.inr (Or.inr (Or.inr rfl))

theorem repeated_class_names : diagram.className .left = diagram.className .right ∧
    (Class.left : diagram.carrier) ≠ .right := ⟨rfl, by decide⟩

theorem optional_primitives : ∀ c, diagram.predefined c ≠ some Builtin.int := by
  intro c h; cases c <;> cases h

def reservedUser : Raw registry := { raw with className := fun _ => "Int" }
theorem reserved_user_invalid : ¬ reservedUser.WellFormed := by
  intro h
  exact h.user_name .left rfl ⟨.int, rfl⟩

def wrongPredefined : Raw registry := { raw with className := fun _ => "Wrong" }
theorem wrong_predefined_invalid : ¬ wrongPredefined.WellFormed := by
  intro h
  have hn := h.predefined_name .one .one rfl
  exact (by decide : "Wrong" ≠ "*") hn

def duplicatePredefined : Raw registry := { raw with
  className := fun _ => "*"
  predefined := fun _ => some .one }
theorem duplicate_predefined_invalid : ¬ duplicatePredefined.WellFormed := by
  intro h
  have he := h.unique_predefined .left .right .one rfl rfl
  cases he

def missingDeclarations : Raw registry := { raw with declarations := ∅ }
theorem missing_inclusion_invalid : ¬ missingDeclarations.WellFormed :=
  fun h => h.inclusion_decl Arrow.leftIn rfl
theorem missing_ordinary_invalid : ¬ missingDeclarations.WellFormed :=
  fun h => h.ordinary_decl Arrow.values rfl

def wrongInclusionName : Raw registry := { raw with mapName := fun _ => "inherits" }
theorem wrong_inclusion_name_invalid : ¬ wrongInclusionName.WellFormed := by
  intro h
  exact (by decide : "inherits" ≠ "isA") (h.inclusion_name Arrow.leftIn rfl)

/-- An author may explicitly constrain a bag; validity does not assert a model. -/
def explicitBagRaw : Raw registry := { raw with
  declarations := raw.declarations ∪ {setValuedFormula Arrow.bag} }
theorem explicit_bag_wellFormed : explicitBagRaw.WellFormed :=
  { wellFormed with
    inclusion_decl := fun e h => Or.inl (wellFormed.inclusion_decl e h)
    ordinary_decl := fun e h => Or.inl (wellFormed.ordinary_decl e h) }
def explicitBag : CD registry := ⟨explicitBagRaw, explicit_bag_wellFormed⟩

def toExplicitBag : Hom diagram explicitBag where
  toDPHom :=
    { toPrefunctor := Prefunctor.id graph
      preserves := by
        intro φ h
        change φ.translate (Prefunctor.id diagram.carrier) ∈ explicitBag.declarations
        rw [DPGraph.Formula.translate_id]
        exact Or.inl h }
  className_eq _ := rfl
  mapName_eq _ := rfl
  predefined_eq _ := rfl
  mode_eq _ := rfl

theorem extra_target_declaration : setValuedFormula Arrow.bag ∈ explicitBag.declarations ∧
    setValuedFormula Arrow.bag ∉ diagram.declarations := ⟨Or.inr rfl, no_bag_default⟩

/-- Noninjective vertex and arrow actions are permitted for user classes. -/
def collapse : graph ⥤q graph where
  obj | .right => .left | c => c
  map | .leftIn => .leftIn | .rightIn => .leftIn | .values => .values | .bag => .bag

def swap : graph ⥤q graph where
  obj | .left => .right | .right => .left | c => c
  map | .leftIn => .rightIn | .rightIn => .leftIn | .values => .values | .bag => .bag

def collapseHom : Hom diagram diagram where
  toDPHom :=
    { toPrefunctor := collapse
      preserves := by
        rintro φ (rfl | rfl | rfl | rfl)
        · exact Or.inl (inclusionFormula_translate _ _)
        · exact Or.inl (inclusionFormula_translate _ _)
        · exact Or.inr (Or.inr (Or.inl (setValuedFormula_translate _ _)))
        · exact Or.inr (Or.inr (Or.inr
            (congrArg (DPGraph.Formula.mk (σ := signature) .total) (arrowBinding_comp _ _)))) }
  className_eq := by intro c; cases c <;> rfl
  mapName_eq := by intro a b e; cases e <;> rfl
  predefined_eq := by intro c; cases c <;> rfl
  mode_eq := by intro a b e; cases e <;> rfl

def swapHom : Hom diagram diagram where
  toDPHom :=
    { toPrefunctor := swap
      preserves := by
        rintro φ (rfl | rfl | rfl | rfl)
        · exact Or.inr (Or.inl (inclusionFormula_translate _ _))
        · exact Or.inl (inclusionFormula_translate _ _)
        · exact Or.inr (Or.inr (Or.inl (setValuedFormula_translate _ _)))
        · exact Or.inr (Or.inr (Or.inr
            (congrArg (DPGraph.Formula.mk (σ := signature) .total) (arrowBinding_comp _ _)))) }
  className_eq := by intro c; cases c <;> rfl
  mapName_eq := by intro a b e; cases e <;> rfl
  predefined_eq := by intro c; cases c <;> rfl
  mode_eq := by intro a b e; cases e <;> rfl

theorem collapse_nonidentity : collapseHom ≠ Hom.id diagram := by
  intro h
  have he := congrArg (fun F => F.toDPHom.toPrefunctor.obj .right) h
  cases he

theorem collapse_identifies : collapse.obj .left = collapse.obj .right := rfl

theorem explicit_composite :
    (collapseHom.comp swapHom).toDPHom.toPrefunctor.obj .right = Class.right := rfl

theorem composition_law :
    (collapseHom.comp swapHom).comp collapseHom =
      collapseHom.comp (swapHom.comp collapseHom) := Hom.comp_assoc _ _ _
theorem unit_laws : (Hom.id diagram).comp collapseHom = collapseHom ∧
    collapseHom.comp (Hom.id diagram) = collapseHom := ⟨Hom.id_comp _, Hom.comp_id _⟩
theorem forget_composite : (collapseHom.comp swapHom).toDPHom =
    collapseHom.toDPHom.comp swapHom.toDPHom := Hom.toDPHom_comp _ _

/-- A well-formed target changes the ordinary arrow to explicit bag mode.
Its effective declarations can still explicitly contain set-valuedness. -/
def bagModeRaw : Raw registry := { raw with
  mode := fun e => match e with
    | .leftIn | .rightIn => .inclusion | .values | .bag => .bag }
theorem bag_mode_wellFormed : bagModeRaw.WellFormed :=
  { wellFormed with
    inclusion_name := by intro a b e h; cases e <;> simp_all [bagModeRaw, raw]
    inclusion_decl := by
      intro a b e h
      cases e with
      | leftIn => exact required_inclusions.1
      | rightIn => exact required_inclusions.2
      | values => cases h
      | bag => cases h
    ordinary_decl := by intro a b e h; cases e <;> cases h }
def bagModeDiagram : CD registry := ⟨bagModeRaw, bag_mode_wellFormed⟩
def modeChangingDP : DPGraph.Hom diagram.toDPGraph bagModeDiagram.toDPGraph :=
  DPGraph.Hom.id diagram.toDPGraph
theorem mode_change_cannot_lift :
    ¬ ∃ F : Hom diagram bagModeDiagram, F.toDPHom = modeChangingDP := by
  rintro ⟨F, h⟩
  have hm := F.mode_eq Arrow.values
  rw [h] at hm
  cases hm

/-- Typed formulas can still repeat arguments and bind isolated arity vertices. -/
def repeatedBinding : Arity.fanIn 2 ⥤q graph where
  obj | .center => .top | .member _ => .left
  map | .edge _ => .leftIn
def repeatedFormula : DPGraph.Formula signature graph := ⟨.disjoint 2, repeatedBinding⟩
def isolatedBinding : Arity.fanOut 0 ⥤q graph where
  obj | .center => .one | .member i => Fin.elim0 i
  map | .edge i => Fin.elim0 i
def isolatedFormula : DPGraph.Formula signature graph := ⟨.key 0, isolatedBinding⟩
theorem repeated_arguments : repeatedBinding.map (.edge 0) = repeatedBinding.map (.edge 1) := rfl
theorem isolated_vertex : isolatedFormula.binding.obj .center = Class.one := rfl

end FormalCD.Examples
