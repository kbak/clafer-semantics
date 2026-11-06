module

public import FormalCD.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.FinCases

/-!
[impl->req~formalcd-figure21-example~1]
[proof->req~formalcd-figure21-example~1]
-/

/-!
# Telematics formal class diagram

SoSyM §2 (telematics example), §6.1.1–3, Figure 21a–b (PDF p.19),
twelve effective formulas (PDF p.21),
and B.4 Definitions 7–9. Arrow identities and full typed bindings are retained.
The two isA names do not identify their arrows. This module asserts syntax only.
-/

@[expose] public section

namespace FormalCD.Telematics
open CategoryTheory DPGraph.Predicates

inductive Node where | comp | ecu | display | int
  deriving DecidableEq
inductive Edge : Node → Node → Type where
  | i1 : Edge .ecu .comp
  | i2 : Edge .display .comp
  | server : Edge .display .ecu
  | display : Edge .ecu .display
  | version : Edge .comp .int
instance : Quiver Node := ⟨Edge⟩
abbrev graph : Quiv := Quiv.of Node

/-- VC uses exactly server, i1, i2, version and their four endpoints. -/
inductive VCEdge : Node → Node → Type where
  | server : VCEdge .display .ecu
  | i1 : VCEdge .ecu .comp
  | i2 : VCEdge .display .comp
  | version : VCEdge .comp .int
abbrev vcShape : Quiv := @Quiv.of Node ⟨VCEdge⟩

def vcBinding : vcShape ⥤q graph where
  obj := id
  map | .server => .server | .i1 => .i1 | .i2 => .i2 | .version => .version

inductive Extra where | vc
  deriving DecidableEq

def extraSignature : DPGraph.Signature := ⟨Extra, fun _ => vcShape⟩
def vocabulary : Vocabulary := Vocabulary.extend extraSignature

def vc : DPGraph.Formula vocabulary.signature graph := ⟨.inr .vc, vcBinding⟩

/-- Only Int is selected by this example. Registry entries are never mandatory. -/
inductive Predefined where | int
  deriving DecidableEq

def registry : Registry where
  Id := Predefined
  name _ := "Int"
  kind _ := .primitive

def nodeName : Node → String
  | .comp => "Comp" | .ecu => "ECU" | .display => "Display" | .int => "Int"
def edgeName : {a b : Node} → (a ⟶ b) → String
  | _, _, .i1 | _, _, .i2 => "isA"
  | _, _, .server => "server"
  | _, _, .display => "display"
  | _, _, .version => "version"
def edgeMode : {a b : Node} → (a ⟶ b) → MapMode
  | _, _, .i1 | _, _, .i2 => .inclusion
  | _, _, .server | _, _, .display | _, _, .version => .ordinary

def inclusions : Arity.fanIn 2 ⥤q graph where
  obj | .center => .comp | .member i => if i = 0 then .ecu else .display
  map
    | .edge i => by
      change Edge (if i = 0 then .ecu else .display) .comp
      split
      · exact .i1
      · exact .i2

def opposite : Arity.opposite ⥤q graph where
  obj | .left => .display | .right => .ecu
  map | .forward => .server | .backward => .display

inductive Declaration where
  | disjoint | cover | inverse | i1 | i2 | displayMult | versionMult | serverMult | vc
  | versionSet | serverSet | displaySet
  deriving DecidableEq

def declaration : Declaration → DPGraph.Formula vocabulary.signature graph
  | .disjoint => vocabulary.embed ⟨.disjoint 2, inclusions⟩
  | .cover => vocabulary.embed ⟨.cover 2, inclusions⟩
  | .inverse => vocabulary.embed ⟨.inverse, opposite⟩
  | .i1 => vocabulary.embed (inclusionFormula Edge.i1)
  | .i2 => vocabulary.embed (inclusionFormula Edge.i2)
  | .displayMult => vocabulary.embed ⟨.targetMultiplicity ⟨0, .finite 5⟩, arrowBinding Edge.display⟩
  | .versionMult => vocabulary.embed ⟨.targetMultiplicity ⟨1, .finite 1⟩, arrowBinding Edge.version⟩
  | .serverMult => vocabulary.embed ⟨.targetMultiplicity ⟨0, .finite 1⟩, arrowBinding Edge.server⟩
  | .vc => vc
  | .versionSet => vocabulary.embed (setValuedFormula Edge.version)
  | .serverSet => vocabulary.embed (setValuedFormula Edge.server)
  | .displaySet => vocabulary.embed (setValuedFormula Edge.display)

def raw : RawOver vocabulary registry where
  carrier := graph
  declarations := Set.range declaration
  className := nodeName
  mapName := edgeName
  predefined | .int => some .int | _ => none
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
    · exact declared .i1
    · exact declared .i2
  ordinary_decl := by
    intro a b e h
    cases e <;> simp only [raw, edgeMode] at h <;> try cases h
    · exact declared .serverSet
    · exact declared .displaySet
    · exact declared .versionSet

def diagram : CDOver vocabulary registry := ⟨raw, wellFormed⟩

instance : Fintype Node where
  elems := {.comp, .ecu, .display, .int}
  complete n := by cases n <;> simp
instance : Fintype Declaration where
  elems := {.disjoint, .cover, .inverse, .i1, .i2, .displayMult, .versionMult,
    .serverMult, .vc, .versionSet, .serverSet, .displaySet}
  complete d := by cases d <;> simp

theorem four_classes : Fintype.card Node = 4 := by decide
theorem twelve_declarations : Fintype.card Declaration = 12 := by decide

def edges : List (Σ a b : graph, a ⟶ b) := [⟨.ecu, .comp, .i1⟩,
  ⟨.display, .comp, .i2⟩, ⟨.display, .ecu, .server⟩,
  ⟨.ecu, .display, .display⟩, ⟨.comp, .int, .version⟩]

def edgeCode : (Σ a b : graph, a ⟶ b) → Nat
  | ⟨_, _, .i1⟩ => 0 | ⟨_, _, .i2⟩ => 1 | ⟨_, _, .server⟩ => 2
  | ⟨_, _, .display⟩ => 3 | ⟨_, _, .version⟩ => 4

theorem five_arrows : edges.length = 5 := rfl
theorem edges_complete (e : Σ a b : graph, a ⟶ b) : e ∈ edges := by
  rcases e with ⟨a,b,e⟩; cases e <;> simp [edges]
theorem edges_nodup : edges.Nodup :=
  List.Nodup.of_map (f := edgeCode) (by decide)
theorem inclusion_identities_distinct :
    (⟨.ecu, .comp, Edge.i1⟩ : Σ a b : graph, a ⟶ b) ≠ ⟨.display, .comp, Edge.i2⟩ := by
  intro h; cases congrArg Sigma.fst h
theorem inclusion_names : raw.mapName Edge.i1 = "isA" ∧ raw.mapName Edge.i2 = "isA" := ⟨rfl,rfl⟩
theorem int_metadata : raw.predefined Node.int = some Predefined.int ∧
    registry.name Predefined.int = "Int" ∧ registry.kind Predefined.int = .primitive :=
  ⟨rfl,rfl,rfl⟩
theorem no_singleton_required (i : registry.Id) : registry.kind i ≠ .singleton := by cases i; decide

/-- A discriminator proves the twelve effective formulas, not just labels, distinct. -/
def formulaCode (f : DPGraph.Formula vocabulary.signature graph) : Nat :=
  match f with
  | ⟨.inl (.disjoint _), _⟩ => 0
  | ⟨.inl (.cover _), _⟩ => 1
  | ⟨.inl .inverse, _⟩ => 2
  | ⟨.inl .inclusion, b⟩ => match b.obj .source with | .ecu => 3 | _ => 4
  | ⟨.inl (.targetMultiplicity _), b⟩ =>
      match b.obj .source with | .ecu => 5 | .comp => 6 | _ => 7
  | ⟨.inr .vc, _⟩ => 8
  | ⟨.inl .setValued, b⟩ =>
      match b.obj .source with | .comp => 9 | .display => 10 | _ => 11
  | _ => 12

theorem declaration_injective : Function.Injective declaration := by
  intro a b h
  have hc := congrArg formulaCode h
  cases a <;> cases b <;> first | rfl | cases hc

noncomputable def effectiveFormulasEquiv : Declaration ≃ {f // f ∈ raw.declarations} :=
  Equiv.ofBijective (fun d => ⟨declaration d, declared d⟩)
    ⟨fun _ _ h => declaration_injective (congrArg Subtype.val h), by
      rintro ⟨f,d,rfl⟩; exact ⟨d,rfl⟩⟩

noncomputable instance : Fintype {f // f ∈ raw.declarations} :=
  Fintype.ofEquiv Declaration effectiveFormulasEquiv

theorem twelve_effective_formulas : Fintype.card {f // f ∈ raw.declarations} = 12 :=
  (Fintype.card_congr effectiveFormulasEquiv).symm.trans twelve_declarations

def vcEdges : List (Σ a b : vcShape, a ⟶ b) := [
  ⟨.display, .ecu, .server⟩, ⟨.ecu, .comp, .i1⟩,
  ⟨.display, .comp, .i2⟩, ⟨.comp, .int, .version⟩]

theorem four_vc_arrows : vcEdges.length = 4 := rfl
theorem vc_edges_complete (e : Σ a b : vcShape, a ⟶ b) : e ∈ vcEdges := by
  rcases e with ⟨a,b,e⟩; cases e <;> simp [vcEdges]
theorem vc_edges_nodup : vcEdges.Nodup :=
  List.Nodup.of_map (f := fun e => edgeCode
    ⟨vcBinding.obj e.1, vcBinding.obj e.2.1, vcBinding.map e.2.2⟩) (by decide)

end FormalCD.Telematics
