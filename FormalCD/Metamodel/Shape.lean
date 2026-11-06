module

public import FormalCD.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.FinCases

/-!
# Figure 21c carrier and the inferred discipline arities

SoSyM §6.1.1–3, Figure 21c (PDF p.19), explanation PDF p.21. The dashed attachments
of nd/ad are omitted in print. The name arity uses the naming/inclusion subgraph;
the arity-discipline arity uses args, pred, so and ta. These are explicit inferred
bindings justified by the constraints, not additional arrows in the figure.
-/

@[expose] public section

namespace FormalCD.Metamodel
open CategoryTheory DPGraph.Predicates

-- [impl->req~formalcd-metamodel-shape~1]
inductive Node where
  | classifier | class | map | incl | predef | sing | dom | string | predefStr | formula | signature
  deriving DecidableEq

inductive Edge : Node → Node → Type where
  | predefStrIn : Edge .predefStr .string
  | classIn : Edge .class .classifier
  | mapIn : Edge .map .classifier
  | predefIn : Edge .predef .class
  | singIn : Edge .sing .predef
  | domIn : Edge .dom .predef
  | inclIn : Edge .incl .map
  | name : Edge .classifier .string
  | predefName : Edge .predef .predefStr
  | so : Edge .map .class
  | ta : Edge .map .class
  | args : Edge .formula .map
  | pred : Edge .formula .signature
instance : Quiver Node := ⟨Edge⟩
abbrev graph : Quiv := Quiv.of Node

inductive NameNode where
  | classifier | class | map | incl | predef | sing | dom | string | predefStr
  deriving DecidableEq

inductive NameEdge : NameNode → NameNode → Type where
  | predefStrIn : NameEdge .predefStr .string
  | classIn : NameEdge .class .classifier
  | mapIn : NameEdge .map .classifier
  | predefIn : NameEdge .predef .class
  | singIn : NameEdge .sing .predef
  | domIn : NameEdge .dom .predef
  | inclIn : NameEdge .incl .map
  | name : NameEdge .classifier .string
  | predefName : NameEdge .predef .predefStr
instance : Quiver NameNode := ⟨NameEdge⟩
abbrev nameShape : Quiv := Quiv.of NameNode

def nameBinding : nameShape ⥤q graph where
  obj
    | .classifier => .classifier
    | .class => .class
    | .map => .map
    | .incl => .incl
    | .predef => .predef
    | .sing => .sing
    | .dom => .dom
    | .string => .string
    | .predefStr => .predefStr
  map
    | .predefStrIn => .predefStrIn
    | .classIn => .classIn
    | .mapIn => .mapIn
    | .predefIn => .predefIn
    | .singIn => .singIn
    | .domIn => .domIn
    | .inclIn => .inclIn
    | .name => .name
    | .predefName => .predefName

inductive ArityNode where
  | formula | signature | map | class
  deriving DecidableEq

inductive ArityEdge : ArityNode → ArityNode → Type where
  | so : ArityEdge .map .class
  | ta : ArityEdge .map .class
  | args : ArityEdge .formula .map
  | pred : ArityEdge .formula .signature
instance : Quiver ArityNode := ⟨ArityEdge⟩
abbrev arityShape : Quiv := Quiv.of ArityNode

def arityBinding : arityShape ⥤q graph where
  obj
    | .formula => .formula
    | .signature => .signature
    | .map => .map
    | .class => .class
  map
    | .so => .so
    | .ta => .ta
    | .args => .args
    | .pred => .pred

inductive Discipline where | nd | ad
  deriving DecidableEq

def extraSignature : DPGraph.Signature where
  Symbol := Discipline
  arity | .nd => nameShape | .ad => arityShape

def vocabulary : Vocabulary := Vocabulary.extend extraSignature

def nd : DPGraph.Formula vocabulary.signature graph := ⟨.inr .nd, nameBinding⟩
def ad : DPGraph.Formula vocabulary.signature graph := ⟨.inr .ad, arityBinding⟩

/-- SING, its modeled class Sing, and an object of Sing inhabit different data types. -/
inductive SingletonClass where | sing
inductive SingletonObject where | star

def singMetaclass : Node := .sing
def modeledSing : SingletonClass := .sing
def singObject : SingletonObject := .star
def objectClass : SingletonObject → SingletonClass := fun _ => .sing

-- [proof->req~formalcd-metamodel-shape~1]
theorem star_has_sing_class : objectClass singObject = modeledSing := rfl

end FormalCD.Metamodel
