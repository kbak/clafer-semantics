module

public import FormalCD.Signature

/-!
# Formal class diagrams

SoSyM §6.1.1–3 and Figure 21b–c, over B.4 Definitions 6–9.
Names annotate existing graph identities. The registry records identity and
naming, not concrete primitive domains. Well-formedness is syntactic validity;
model satisfaction still requires an explicit DPGraph interpretation.
-/

@[expose] public section

universe s va ua p v u v' u'

namespace FormalCD

open CategoryTheory DPGraph.Predicates

/-- Distinguish the singleton vocabulary from primitive-domain vocabulary. -/
inductive PredefinedKind where
  | singleton | primitive
  deriving DecidableEq

/-- Shared vocabulary with stable keys. Diagrams may select any subset of it. -/
structure Registry where
  Id : Type p
  name : Id → String
  kind : Id → PredefinedKind

def Registry.Reserved (R : Registry) (name : String) : Prop :=
  ∃ i, R.name i = name

/-- Inclusion is a separate mode; bag mode carries no implicit declaration. -/
inductive MapMode where
  | ordinary | bag | inclusion
  deriving DecidableEq

/-- Bind the existing unary arity to an arrow, retaining both endpoints. -/
def arrowBinding {G : Quiv.{v,u}} {a b : G} (e : a ⟶ b) : Arity.unary ⥤q G where
  obj | .source => a | .target => b
  map | .arrow => e

-- [impl->req~formalcd-declarations~1]
def inclusionFormula {G : Quiv.{v,u}} {a b : G} (e : a ⟶ b) :
    DPGraph.Formula signature G := ⟨.inclusion, arrowBinding e⟩

def setValuedFormula {G : Quiv.{v,u}} {a b : G} (e : a ⟶ b) :
    DPGraph.Formula signature G := ⟨.setValued, arrowBinding e⟩

theorem arrowBinding_comp {G : Quiv.{v,u}} {H : Quiv.{v',u'}}
    {a b : G} (e : a ⟶ b) (F : G ⥤q H) :
    (arrowBinding e).comp F = arrowBinding (F.map e) := by
  exact Prefunctor.ext (by intro x; cases x <;> rfl)
    (by intro x y f; cases f; rfl)

-- [proof->req~formalcd-declarations~1]
@[simp] theorem inclusionFormula_translate {G : Quiv.{v,u}} {H : Quiv.{v',u'}}
    {a b : G} (e : a ⟶ b) (F : G ⥤q H) :
    (inclusionFormula e).translate F = inclusionFormula (F.map e) :=
  congrArg (DPGraph.Formula.mk (σ := signature) .inclusion) (arrowBinding_comp e F)

@[simp] theorem setValuedFormula_translate {G : Quiv.{v,u}} {H : Quiv.{v',u'}}
    {a b : G} (e : a ⟶ b) (F : G ⥤q H) :
    (setValuedFormula e).translate F = setValuedFormula (F.map e) :=
  congrArg (DPGraph.Formula.mk (σ := signature) .setValued) (arrowBinding_comp e F)

-- [impl->req~formalcd-signature-extension~1]
/-- Inspectable raw data, including invalid diagrams. `declarations` is the
single effective set: authored formulas and required defaults live together. -/
structure RawOver (V : Vocabulary.{s,va,ua}) (R : Registry.{p})
    extends DPGraph.{s,va,ua,v,u} V.signature where
  className : carrier → String
  mapName : ∀ {a b : carrier}, (a ⟶ b) → String
  predefined : carrier → Option R.Id
  mode : ∀ {a b : carrier}, (a ⟶ b) → MapMode

-- [impl->req~formalcd-naming~1]
/-- §6.1 naming/default disciplines. Typed Formula bindings already enforce
arity and incidence. No global name injectivity or inheritance acyclicity. -/
structure RawOver.WellFormed {V : Vocabulary.{s,va,ua}} {R : Registry.{p}}
    (D : RawOver.{s,va,ua,p,v,u} V R) : Prop where
  predefined_name : ∀ c i, D.predefined c = some i → D.className c = R.name i
  user_name : ∀ c, D.predefined c = none → ¬ R.Reserved (D.className c)
  unique_predefined : ∀ c d i,
    D.predefined c = some i → D.predefined d = some i → c = d
  inclusion_name : ∀ {a b} (e : a ⟶ b), D.mode e = .inclusion → D.mapName e = "isA"
  inclusion_decl : ∀ {a b} (e : a ⟶ b), D.mode e = .inclusion →
    V.embed (inclusionFormula e) ∈ D.declarations
  ordinary_decl : ∀ {a b} (e : a ⟶ b), D.mode e = .ordinary →
    V.embed (setValuedFormula e) ∈ D.declarations

-- [impl->req~formalcd-structure~1]
/-- A syntactically valid CD. This proof asserts no existence of a model. -/
structure CDOver (V : Vocabulary.{s,va,ua}) (R : Registry.{p})
    extends RawOver.{s,va,ua,p,v,u} V R where
  wellFormed : toRawOver.WellFormed

/-- The original small-signature API wraps the general data without copying it. -/
structure Raw (R : Registry.{p}) extends RawOver.{0,0,0,p,v,u} Vocabulary.builtins R

abbrev Raw.WellFormed {R : Registry.{p}} (D : Raw.{p,v,u} R) := D.toRawOver.WellFormed

namespace Raw.WellFormed
variable {R : Registry.{p}} {D : Raw.{p,v,u} R}
abbrev predefined_name (h : D.WellFormed) :
    ∀ c i, D.predefined c = some i → D.className c = R.name i := RawOver.WellFormed.predefined_name h
abbrev user_name (h : D.WellFormed) :
    ∀ c, D.predefined c = none → ¬ R.Reserved (D.className c) := RawOver.WellFormed.user_name h
abbrev unique_predefined (h : D.WellFormed) : ∀ c d i,
    D.predefined c = some i → D.predefined d = some i → c = d := RawOver.WellFormed.unique_predefined h
abbrev inclusion_name (h : D.WellFormed) :
    ∀ {a b} (e : a ⟶ b), D.mode e = .inclusion → D.mapName e = "isA" := RawOver.WellFormed.inclusion_name h
abbrev inclusion_decl (h : D.WellFormed) :
    ∀ {a b} (e : a ⟶ b), D.mode e = .inclusion → inclusionFormula e ∈ D.declarations := RawOver.WellFormed.inclusion_decl h
abbrev ordinary_decl (h : D.WellFormed) :
    ∀ {a b} (e : a ⟶ b), D.mode e = .ordinary → setValuedFormula e ∈ D.declarations := RawOver.WellFormed.ordinary_decl h
end Raw.WellFormed

structure CD (R : Registry.{p}) extends Raw.{p,v,u} R where
  wellFormed : toRaw.WellFormed

abbrev CD.generalize {R : Registry.{p}} (D : CD.{p,v,u} R) :
    CDOver Vocabulary.builtins R := ⟨D.toRaw.toRawOver, D.wellFormed⟩

end FormalCD
