module

public import FormalCD.Metamodel.Shape

/-!
[impl->req~formalcd-metamodel-shape~1]
[proof->req~formalcd-metamodel-shape~1]
-/

/-! # The typed Figure 21c metamodel (SoSyM §6.1.3, PDF pp.19–21)

All arrows and annotations are enumerated. Only the underlined SING metaclass
is marked singleton in this syntax registry; concrete interpretations of String,
PredefStr and Signature are explicit interpretation context, not inferred domains.
-/

@[expose] public section

namespace FormalCD.Metamodel
open CategoryTheory DPGraph.Predicates

inductive MetaPredefined where | sing
  deriving DecidableEq, Inhabited

def registry : Registry where
  Id := MetaPredefined
  name _ := "SING"
  kind _ := .singleton

def nodeName : Node → String
  | .classifier => "Classifier"
  | .class => "Class"
  | .map => "Map"
  | .incl => "Incl"
  | .predef => "Predef"
  | .sing => "SING"
  | .dom => "Dom"
  | .string => "String"
  | .predefStr => "PredefStr"
  | .formula => "Formula"
  | .signature => "Signature"

def edgeName : {a b : Node} → (a ⟶ b) → String
  | _, _, .predefStrIn => "isA"
  | _, _, .classIn => "isA"
  | _, _, .mapIn => "isA"
  | _, _, .predefIn => "isA"
  | _, _, .singIn => "isA"
  | _, _, .domIn => "isA"
  | _, _, .inclIn => "isA"
  | _, _, .name => "name"
  | _, _, .predefName => "name"
  | _, _, .so => "so"
  | _, _, .ta => "ta"
  | _, _, .args => "args"
  | _, _, .pred => "pred"

def edgeMode : {a b : Node} → (a ⟶ b) → MapMode
  | _, _, .predefStrIn => .inclusion
  | _, _, .classIn => .inclusion
  | _, _, .mapIn => .inclusion
  | _, _, .predefIn => .inclusion
  | _, _, .singIn => .inclusion
  | _, _, .domIn => .inclusion
  | _, _, .inclIn => .inclusion
  | _, _, .name => .ordinary
  | _, _, .predefName => .ordinary
  | _, _, .so => .ordinary
  | _, _, .ta => .ordinary
  | _, _, .args => .bag
  | _, _, .pred => .ordinary

def classifiers : Arity.fanIn 2 ⥤q graph where
  obj | .center => .classifier | .member i => if i = 0 then .class else .map
  map
    | .edge i => by
      change Edge (if i = 0 then .class else .map) .classifier
      by_cases h : i = 0
      · rw [ite_eq_left h]; exact Edge.classIn
      · rw [ite_eq_right h]; exact Edge.mapIn

def predefinedKinds : Arity.fanIn 2 ⥤q graph where
  obj | .center => .predef | .member i => if i = 0 then .sing else .dom
  map
    | .edge i => by
      change Edge (if i = 0 then .sing else .dom) .predef
      by_cases h : i = 0
      · rw [ite_eq_left h]; exact Edge.singIn
      · rw [ite_eq_right h]; exact Edge.domIn

/-- Literal Table 3 key: the args BAG and pred fiber, without indexed strengthening. -/
def keyBinding : Arity.fanOut 2 ⥤q graph where
  obj | .center => .formula | .member i => if i = 0 then .map else .signature
  map
    | .edge i => by
      change Edge .formula (if i = 0 then .map else .signature)
      by_cases h : i = 0
      · rw [ite_eq_left h]; exact Edge.args
      · rw [ite_eq_right h]; exact Edge.pred

def literalKey : DPGraph.Formula vocabulary.signature graph :=
  vocabulary.embed ⟨.key 2, keyBinding⟩

inductive Declaration where
  | predefStrIn | classIn | mapIn | predefIn | singIn | domIn | inclIn | nameSet | predefNameSet | soSet | taSet | predSet | nameTotal | nameSingle | predefNameTotal | predefNameSingle | soTotal | soSingle | taTotal | taSingle | argsTotal | predTotal | predSingle | classifiersCover | classifiersDisjoint | predefinedCover | predefinedDisjoint | key | nd | ad
  deriving DecidableEq

def declaration : Declaration → DPGraph.Formula vocabulary.signature graph
  | .predefStrIn => vocabulary.embed (inclusionFormula Edge.predefStrIn)
  | .classIn => vocabulary.embed (inclusionFormula Edge.classIn)
  | .mapIn => vocabulary.embed (inclusionFormula Edge.mapIn)
  | .predefIn => vocabulary.embed (inclusionFormula Edge.predefIn)
  | .singIn => vocabulary.embed (inclusionFormula Edge.singIn)
  | .domIn => vocabulary.embed (inclusionFormula Edge.domIn)
  | .inclIn => vocabulary.embed (inclusionFormula Edge.inclIn)
  | .nameSet => vocabulary.embed (setValuedFormula Edge.name)
  | .predefNameSet => vocabulary.embed (setValuedFormula Edge.predefName)
  | .soSet => vocabulary.embed (setValuedFormula Edge.so)
  | .taSet => vocabulary.embed (setValuedFormula Edge.ta)
  | .predSet => vocabulary.embed (setValuedFormula Edge.pred)
  | .nameTotal => vocabulary.embed ⟨.total, arrowBinding Edge.name⟩
  | .nameSingle => vocabulary.embed ⟨.singleValued, arrowBinding Edge.name⟩
  | .predefNameTotal => vocabulary.embed ⟨.total, arrowBinding Edge.predefName⟩
  | .predefNameSingle => vocabulary.embed ⟨.singleValued, arrowBinding Edge.predefName⟩
  | .soTotal => vocabulary.embed ⟨.total, arrowBinding Edge.so⟩
  | .soSingle => vocabulary.embed ⟨.singleValued, arrowBinding Edge.so⟩
  | .taTotal => vocabulary.embed ⟨.total, arrowBinding Edge.ta⟩
  | .taSingle => vocabulary.embed ⟨.singleValued, arrowBinding Edge.ta⟩
  | .argsTotal => vocabulary.embed ⟨.total, arrowBinding Edge.args⟩
  | .predTotal => vocabulary.embed ⟨.total, arrowBinding Edge.pred⟩
  | .predSingle => vocabulary.embed ⟨.singleValued, arrowBinding Edge.pred⟩
  | .classifiersCover => vocabulary.embed ⟨.cover 2, classifiers⟩
  | .classifiersDisjoint => vocabulary.embed ⟨.disjoint 2, classifiers⟩
  | .predefinedCover => vocabulary.embed ⟨.cover 2, predefinedKinds⟩
  | .predefinedDisjoint => vocabulary.embed ⟨.disjoint 2, predefinedKinds⟩
  | .key => literalKey
  | .nd => nd
  | .ad => ad

def raw : RawOver vocabulary registry where
  carrier := graph
  declarations := Set.range declaration
  className := nodeName
  mapName := edgeName
  predefined | .sing => some .sing | _ => none
  mode := edgeMode

theorem declared (d : Declaration) : declaration d ∈ raw.declarations := ⟨d, rfl⟩

theorem wellFormed : raw.WellFormed where
  predefined_name := by intro c i h; cases c <;> cases h; rfl
  user_name := by
    intro c h ⟨i, hi⟩
    cases c <;> cases i <;> simp_all [raw, registry, nodeName]
  unique_predefined := by
    intro c d i hc hd
    cases c <;> cases hc
    cases d <;> cases hd
    rfl
  inclusion_name := by intro a b e h; cases e <;> simp_all [raw, edgeMode, edgeName]
  inclusion_decl := by
    intro a b e h
    cases e <;> simp only [raw, edgeMode] at h <;> try cases h
    · exact declared .predefStrIn
    · exact declared .classIn
    · exact declared .mapIn
    · exact declared .predefIn
    · exact declared .singIn
    · exact declared .domIn
    · exact declared .inclIn
  ordinary_decl := by
    intro a b e h
    cases e <;> simp only [raw, edgeMode] at h <;> try cases h
    · exact declared .nameSet
    · exact declared .predefNameSet
    · exact declared .soSet
    · exact declared .taSet
    · exact declared .predSet

def diagram : CDOver vocabulary registry := ⟨raw, wellFormed⟩

/-- Detect only a setValued declaration on the Formula-to-Map arrow. -/
def isArgsSet (f : DPGraph.Formula vocabulary.signature graph) : Bool :=
  match f with
  | ⟨.inl .setValued, b⟩ => (match b.obj .source with | .formula => true | _ => false) &&
      (match b.obj .target with | .map => true | _ => false)
  | _ => false

theorem args_no_setValued :
    vocabulary.embed (setValuedFormula Edge.args) ∉ raw.declarations := by
  rintro ⟨d, h⟩
  have hh := congrArg isArgsSet h
  cases d <;> cases hh

theorem args_bag_total : raw.mode Edge.args = .bag ∧
    vocabulary.embed ⟨.total, arrowBinding Edge.args⟩ ∈ raw.declarations :=
  ⟨rfl, declared .argsTotal⟩

theorem discipline_declarations : nd ∈ raw.declarations ∧ ad ∈ raw.declarations ∧
    literalKey ∈ raw.declarations := ⟨declared .nd, declared .ad, declared .key⟩

theorem cover_disjoint_declarations :
    declaration .classifiersCover ∈ raw.declarations ∧
    declaration .classifiersDisjoint ∈ raw.declarations ∧
    declaration .predefinedCover ∈ raw.declarations ∧
    declaration .predefinedDisjoint ∈ raw.declarations :=
  ⟨declared _, declared _, declared _, declared _⟩

instance : Fintype Node where
  elems := {.classifier, .class, .map, .incl, .predef, .sing, .dom, .string, .predefStr, .formula, .signature}
  complete n := by cases n <;> simp

theorem eleven_nodes : Fintype.card Node = 11 := by decide

/-- The entire edge inventory, retaining both distinct name identities. -/
def edges : List (Σ a b : graph, a ⟶ b) := [
  ⟨.predefStr, .string, Edge.predefStrIn⟩,
  ⟨.class, .classifier, Edge.classIn⟩,
  ⟨.map, .classifier, Edge.mapIn⟩,
  ⟨.predef, .class, Edge.predefIn⟩,
  ⟨.sing, .predef, Edge.singIn⟩,
  ⟨.dom, .predef, Edge.domIn⟩,
  ⟨.incl, .map, Edge.inclIn⟩,
  ⟨.classifier, .string, Edge.name⟩,
  ⟨.predef, .predefStr, Edge.predefName⟩,
  ⟨.map, .class, Edge.so⟩,
  ⟨.map, .class, Edge.ta⟩,
  ⟨.formula, .map, Edge.args⟩,
  ⟨.formula, .signature, Edge.pred⟩]

theorem thirteen_arrows : edges.length = 13 := rfl
theorem edges_complete (e : Σ a b : graph, a ⟶ b) : e ∈ edges := by
  rcases e with ⟨a, b, e⟩; cases e <;> simp [edges]

theorem name_identities_distinct :
    (⟨.classifier, .string, Edge.name⟩ : Σ a b : graph, a ⟶ b) ≠
      ⟨.predef, .predefStr, Edge.predefName⟩ := by
  intro h; cases congrArg Sigma.fst h

theorem same_name : raw.mapName Edge.name = raw.mapName Edge.predefName := rfl

def edgeCode : (Σ a b : graph, a ⟶ b) → Nat
  | ⟨_,_,.predefStrIn⟩ => 0
  | ⟨_,_,.classIn⟩ => 1
  | ⟨_,_,.mapIn⟩ => 2
  | ⟨_,_,.predefIn⟩ => 3
  | ⟨_,_,.singIn⟩ => 4
  | ⟨_,_,.domIn⟩ => 5
  | ⟨_,_,.inclIn⟩ => 6
  | ⟨_,_,.name⟩ => 7
  | ⟨_,_,.predefName⟩ => 8
  | ⟨_,_,.so⟩ => 9
  | ⟨_,_,.ta⟩ => 10
  | ⟨_,_,.args⟩ => 11
  | ⟨_,_,.pred⟩ => 12

theorem edges_nodup : edges.Nodup :=
  List.Nodup.of_map (f := edgeCode) (by decide)

theorem sing_metadata : raw.predefined Node.sing = some MetaPredefined.sing ∧
    registry.kind MetaPredefined.sing = .singleton := ⟨rfl,rfl⟩

theorem drawn_totals :
    declaration .nameTotal ∈ raw.declarations ∧ declaration .predefNameTotal ∈ raw.declarations ∧
    declaration .soTotal ∈ raw.declarations ∧ declaration .taTotal ∈ raw.declarations ∧
    declaration .argsTotal ∈ raw.declarations ∧ declaration .predTotal ∈ raw.declarations :=
  ⟨declared _, declared _, declared _, declared _, declared _, declared _⟩

theorem drawn_singleValued :
    declaration .nameSingle ∈ raw.declarations ∧ declaration .predefNameSingle ∈ raw.declarations ∧
    declaration .soSingle ∈ raw.declarations ∧ declaration .taSingle ∈ raw.declarations ∧
    declaration .predSingle ∈ raw.declarations :=
  ⟨declared _, declared _, declared _, declared _, declared _⟩

end FormalCD.Metamodel
