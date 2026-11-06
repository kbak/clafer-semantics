module

public import Clafer.MCS.Laws
public import FormalCD.Metamodel.Shape

/-!
[impl->req~clafer-mcs-metamodel~1]
[proof->req~clafer-mcs-metamodel~1]
-/

/-!
# Figure 23 as a typed formal class diagram

SoSyM §6.2.3, Figure 23. The seven map/inclusion source bounds use the
accepted 0..1 correction. Head-class and formula ownership keep source 1.
The nd/ad attachments are explicit discipline symbols; their structural
contracts are Labels.WellFormed and Formulas.WellFormed plus typed bindings.
-/

@[expose] public section
namespace Clafer.MCS.Metamodel
open CategoryTheory DPGraph.Predicates FormalCD

inductive Node where
  | clafer | role | classRole | mapRole | inclRole | string | predefStr | formula | signature
  deriving DecidableEq

inductive Edge : Node → Node → Type where
  | classIn : Edge .classRole .role
  | mapIn : Edge .mapRole .role
  | inclIn : Edge .inclRole .mapRole
  | predefStrIn : Edge .predefStr .string
  | label : Edge .role .string
  | so : Edge .mapRole .classRole
  | ta : Edge .mapRole .classRole
  | args : Edge .formula .mapRole
  | pred : Edge .formula .signature
  | headClass : Edge .clafer .classRole
  | sourceClass : Edge .clafer .classRole
  | targetClass : Edge .clafer .classRole
  | headMap : Edge .clafer .mapRole
  | parentMap : Edge .clafer .mapRole
  | drefMap : Edge .clafer .mapRole
  | targetMap : Edge .clafer .mapRole
  | superS : Edge .clafer .inclRole
  | superH : Edge .clafer .inclRole
  | superT : Edge .clafer .inclRole
  | formulas : Edge .clafer .formula
instance : Quiver Node := ⟨Edge⟩
abbrev graph : Quiv := Quiv.of Node

inductive Discipline where | nd | ad
  deriving DecidableEq

def extraSignature : DPGraph.Signature where
  Symbol := Discipline
  arity _ := graph

def vocabulary : Vocabulary := Vocabulary.extend extraSignature

def discipline (d : Discipline) : DPGraph.Formula vocabulary.signature graph :=
  ⟨.inr d, Prefunctor.id graph⟩

def nodeName : Node → String
  | .clafer => "Clafer"
  | .role => "Role"
  | .classRole => "ClassRole"
  | .mapRole => "MapRole"
  | .inclRole => "InclRole"
  | .string => "String"
  | .predefStr => "PredefStr"
  | .formula => "Formula"
  | .signature => "Signature"

def edgeName : {a b : Node} → (a ⟶ b) → String
  | _, _, .classIn => "isA"
  | _, _, .mapIn => "isA"
  | _, _, .inclIn => "isA"
  | _, _, .predefStrIn => "isA"
  | _, _, .label => "label"
  | _, _, .so => "so"
  | _, _, .ta => "ta"
  | _, _, .args => "args"
  | _, _, .pred => "pred"
  | _, _, .headClass => "head"
  | _, _, .sourceClass => "source"
  | _, _, .targetClass => "target"
  | _, _, .headMap => "head"
  | _, _, .parentMap => "parent"
  | _, _, .drefMap => "dref"
  | _, _, .targetMap => "target"
  | _, _, .superS => "super_s"
  | _, _, .superH => "super_h"
  | _, _, .superT => "super_t"
  | _, _, .formulas => "formulas"

def edgeMode : {a b : Node} → (a ⟶ b) → MapMode
  | _, _, .classIn => .inclusion
  | _, _, .mapIn => .inclusion
  | _, _, .inclIn => .inclusion
  | _, _, .predefStrIn => .inclusion
  | _, _, .label => .ordinary
  | _, _, .so => .ordinary
  | _, _, .ta => .ordinary
  | _, _, .args => .bag
  | _, _, .pred => .ordinary
  | _, _, .headClass => .ordinary
  | _, _, .sourceClass => .ordinary
  | _, _, .targetClass => .ordinary
  | _, _, .headMap => .ordinary
  | _, _, .parentMap => .ordinary
  | _, _, .drefMap => .ordinary
  | _, _, .targetMap => .ordinary
  | _, _, .superS => .ordinary
  | _, _, .superH => .ordinary
  | _, _, .superT => .ordinary
  | _, _, .formulas => .ordinary

/-- Total labels/endpoints/pred/head; args is total but remains bag valued. -/
def isTotal : {a b : Node} → (a ⟶ b) → Bool
  | _, _, .label | _, _, .so | _, _, .ta | _, _, .pred | _, _, .headClass
  | _, _, .args => true
  | _, _, _ => false

/-- All ordinary arrows except the one-to-many formula association are partial functions. -/
def isSingle : {a b : Node} → (a ⟶ b) → Bool
  | _, _, .classIn | _, _, .mapIn | _, _, .inclIn | _, _, .predefStrIn
  | _, _, .args | _, _, .formulas => false
  | _, _, _ => true

/-- Literal source 1 remains on head-class and formulas. -/
def isOwned : {a b : Node} → (a ⟶ b) → Bool
  | _, _, .headClass | _, _, .formulas => true
  | _, _, _ => false

/-- Corrected source upper bounds on precisely the seven accepted associations. -/
def corrected : {a b : Node} → (a ⟶ b) → Bool
  | _, _, .headMap | _, _, .parentMap | _, _, .drefMap | _, _, .targetMap
  | _, _, .superS | _, _, .superH | _, _, .superT => true
  | _, _, _ => false

def partition : Arity.fanIn 2 ⥤q graph where
  obj | .center => .role | .member i => if i = 0 then .classRole else .mapRole
  map
    | .edge i => by
      change Edge (if i = 0 then .classRole else .mapRole) .role
      by_cases h : i = 0
      · simpa [h] using Edge.classIn
      · simpa [h] using Edge.mapIn

def keyBinding : Arity.fanOut 2 ⥤q graph where
  obj | .center => .formula | .member i => if i = 0 then .mapRole else .signature
  map
    | .edge i => by
      change Edge .formula (if i = 0 then .mapRole else .signature)
      by_cases h : i = 0
      · simpa [h] using Edge.args
      · simpa [h] using Edge.pred

def declarations : Set (DPGraph.Formula vocabulary.signature graph) :=
  {φ | (∃ (a b : graph) (e : a ⟶ b), edgeMode e = .inclusion ∧
        φ = vocabulary.embed (inclusionFormula e)) ∨
    (∃ (a b : graph) (e : a ⟶ b), edgeMode e = .ordinary ∧
        φ = vocabulary.embed (setValuedFormula e)) ∨
    (∃ (a b : graph) (e : a ⟶ b), isTotal e = true ∧
        φ = vocabulary.embed ⟨.total, arrowBinding e⟩) ∨
    (∃ (a b : graph) (e : a ⟶ b), isSingle e = true ∧
        φ = vocabulary.embed ⟨.singleValued, arrowBinding e⟩) ∨
    (∃ (a b : graph) (e : a ⟶ b), isOwned e = true ∧
        φ = vocabulary.embed ⟨.sourceMultiplicity one, arrowBinding e⟩) ∨
    (∃ (a b : graph) (e : a ⟶ b), corrected e = true ∧
        φ = vocabulary.embed ⟨.sourceMultiplicity optional, arrowBinding e⟩) ∨
    φ = vocabulary.embed ⟨.cover 2, partition⟩ ∨
    φ = vocabulary.embed ⟨.disjoint 2, partition⟩ ∨
    φ = vocabulary.embed ⟨.key 2, keyBinding⟩ ∨
    φ = discipline .nd ∨ φ = discipline .ad}

def raw : RawOver vocabulary Shape.roleRegistry where
  carrier := graph
  declarations := declarations
  className := nodeName
  mapName := edgeName
  mode := edgeMode
  predefined _ := none

theorem wellFormed : raw.WellFormed where
  predefined_name := by intro c i; exact Empty.elim i
  user_name := by intro c _ ⟨i, _⟩; exact Empty.elim i
  unique_predefined := by intro c d i; exact Empty.elim i
  inclusion_name := by intro a b e h; cases e <;> simp_all [raw, edgeMode, edgeName]
  inclusion_decl e h := Or.inl ⟨_, _, e, h, rfl⟩
  ordinary_decl e h := Or.inr (Or.inl ⟨_, _, e, h, rfl⟩)

def diagram : CDOver vocabulary Shape.roleRegistry := ⟨raw, wellFormed⟩

theorem corrected_declared {a b : graph} (e : a ⟶ b) (h : corrected e = true) :
    vocabulary.embed ⟨.sourceMultiplicity optional, arrowBinding e⟩ ∈ raw.declarations :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, e, h, rfl⟩)))))

theorem ownership_declared {a b : graph} (e : a ⟶ b) (h : isOwned e = true) :
    vocabulary.embed ⟨.sourceMultiplicity one, arrowBinding e⟩ ∈ raw.declarations :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, e, h, rfl⟩))))

theorem args_total_declared : vocabulary.embed ⟨.total, arrowBinding Edge.args⟩ ∈ raw.declarations :=
  Or.inr (Or.inr (Or.inl ⟨_, _, Edge.args, rfl, rfl⟩))

theorem literal_key_declared : vocabulary.embed ⟨.key 2, keyBinding⟩ ∈ raw.declarations := by
  right; right; right; right; right; right; right; right; left; rfl

/-- Only the seven agreed sources change; neither totality nor ownership of head changes. -/
theorem correction_boundary : corrected Edge.headClass = false ∧
    corrected Edge.formulas = false ∧ corrected Edge.parentMap = true ∧
    corrected Edge.superH = true ∧ isTotal Edge.headClass = true := by decide

def edges : List (Σ a b : graph, a ⟶ b) := [
  ⟨.classRole, .role, Edge.classIn⟩,
  ⟨.mapRole, .role, Edge.mapIn⟩,
  ⟨.inclRole, .mapRole, Edge.inclIn⟩,
  ⟨.predefStr, .string, Edge.predefStrIn⟩,
  ⟨.role, .string, Edge.label⟩,
  ⟨.mapRole, .classRole, Edge.so⟩,
  ⟨.mapRole, .classRole, Edge.ta⟩,
  ⟨.formula, .mapRole, Edge.args⟩,
  ⟨.formula, .signature, Edge.pred⟩,
  ⟨.clafer, .classRole, Edge.headClass⟩,
  ⟨.clafer, .classRole, Edge.sourceClass⟩,
  ⟨.clafer, .classRole, Edge.targetClass⟩,
  ⟨.clafer, .mapRole, Edge.headMap⟩,
  ⟨.clafer, .mapRole, Edge.parentMap⟩,
  ⟨.clafer, .mapRole, Edge.drefMap⟩,
  ⟨.clafer, .mapRole, Edge.targetMap⟩,
  ⟨.clafer, .inclRole, Edge.superS⟩,
  ⟨.clafer, .inclRole, Edge.superH⟩,
  ⟨.clafer, .inclRole, Edge.superT⟩,
  ⟨.clafer, .formula, Edge.formulas⟩]

theorem twenty_edges : edges.length = 20 := rfl

theorem edges_complete (e : Σ a b : graph, a ⟶ b) : e ∈ edges := by
  rcases e with ⟨a, b, e⟩
  cases e <;> simp [edges]

end Clafer.MCS.Metamodel
