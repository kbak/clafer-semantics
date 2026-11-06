module

public import FormalCD.Metamodel.Interpretation

/-!
# Canonical reification of a CD's syntax

SoSyM §6.1.3 Figure 21c and B.4 Definition 8. Full bindings remain in the
explicit descriptor; argument links retain occurrence identity. No satisfaction
or nonempty-support hypothesis is used to construct this encoding.
-/

@[expose] public section

universe p s va ua v u

namespace FormalCD.Metamodel.Realization
open CategoryTheory DPGraph DPGraph.Predicates

variable {V : Vocabulary.{s,va,ua}} {R : Registry.{p}}
variable (D : CDOver.{s,va,ua,p,v,u} V R)

abbrev Declared := {φ : Formula V.signature D.carrier // φ ∈ D.declarations}

/-- One bounded universe, with disjoint syntax tags. Subclasses reuse tags. -/
inductive Ambient : Type (max p s va ua v u)
  | vertex : D.carrier → Ambient
  | arrow : ArrowData D.carrier → Ambient
  | formula : Declared D → Ambient
  | symbol : V.signature.Symbol → Ambient
  | text : String → Ambient

abbrev vertex : D.carrier ↪ Ambient D := ⟨Ambient.vertex, fun _ _ h => Ambient.vertex.inj h⟩
abbrev arrow : ArrowData D.carrier ↪ Ambient D := ⟨Ambient.arrow, fun _ _ h => Ambient.arrow.inj h⟩
abbrev formula : Declared D ↪ Ambient D := ⟨Ambient.formula, fun _ _ h => Ambient.formula.inj h⟩
abbrev symbol : V.signature.Symbol ↪ Ambient D := ⟨Ambient.symbol, fun _ _ h => Ambient.symbol.inj h⟩
abbrev text : String ↪ Ambient D := ⟨Ambient.text, fun _ _ h => Ambient.text.inj h⟩

def names : NameContext R (Ambient D) where
  text := text D
  name
    | .vertex c => D.className c
    | .arrow e => D.mapName e.2.2
    | _ => ""
  identifier
    | .vertex c => D.predefined c
    | _ => none

/-- Extents use all registry names, including identifiers not realized in D. -/
def extent : Node → Set (Ambient D)
  | .class => Set.range (vertex D)
  | .map => Set.range (arrow D)
  | .classifier => Set.range (vertex D) ∪ Set.range (arrow D)
  | .formula => Set.range (formula D)
  | .signature => Set.range (symbol D)
  | .string => Set.range (text D)
  | .predefStr => {x | ∃ i, text D (R.name i) = x}
  | .predef => {x | x ∈ Set.range (vertex D) ∧ ∃ i, (names D).identifier x = some i}
  | .sing => {x | x ∈ Set.range (vertex D) ∧
      ∃ i, (names D).identifier x = some i ∧ R.kind i = .singleton}
  | .dom => {x | x ∈ Set.range (vertex D) ∧
      ∃ i, (names D).identifier x = some i ∧ R.kind i = .primitive}
  | .incl => {x | ∃ e : ArrowData D.carrier, D.mode e.2.2 = .inclusion ∧ arrow D e = x}

noncomputable def vertices : D.carrier ≃ extent D .class :=
  Equiv.ofInjective (vertex D) (vertex D).injective
noncomputable def arrows : ArrowData D.carrier ≃ extent D .map :=
  Equiv.ofInjective (arrow D) (arrow D).injective
noncomputable def formulas : Declared D ≃ extent D .formula :=
  Equiv.ofInjective (formula D) (formula D).injective
noncomputable def symbols : V.signature.Symbol ≃ extent D .signature :=
  Equiv.ofInjective (symbol D) (symbol D).injective
noncomputable def strings : String ≃ extent D .string :=
  Equiv.ofInjective (text D) (text D).injective

/-- The exact indexed arrow family; equal images are not deduplicated. -/
noncomputable def arguments : IndexedFamily (extent D .formula) (extent D .map) where
  Index f := ArrowData (V.signature.arity ((formulas D).symm f).val.symbol)
  eval f a := arrows D ((Candidate.ofFormula ((formulas D).symm f).val).argument a)

/-- Identity-valued inclusions retain the ambient object. -/
def inclusion {A B : Set (Ambient D)} (h : A ⊆ B) : Span A B :=
  Span.ofFunction (fun x => ⟨x.val, h x.property⟩)

noncomputable def nameMap (x : extent D .classifier) : extent D .string :=
  strings D ((names D).name x.val)

noncomputable def predefNameMap (x : extent D .predef) : extent D .predefStr :=
  ⟨text D ((names D).name x.val), by
    rcases x.property with ⟨⟨c, hc⟩, i, hi⟩
    refine ⟨i, ?_⟩
    rw [← hc] at hi ⊢
    exact congrArg (text D) (D.wellFormed.predefined_name c i hi).symm⟩

-- [impl->req~formalcd-metamodel-realization~1]
noncomputable def encode : graph ⥤q semanticGraph.{max p s va ua v u,0} (Ambient D) where
  obj := extent D
  map
    | .classIn => inclusion D (fun _ h => Or.inl h)
    | .mapIn => inclusion D (fun _ h => Or.inr h)
    | .predefIn => inclusion D (fun _ h => h.1)
    | .singIn => inclusion D (fun _ h => ⟨h.1, h.2.imp (fun _ hi => hi.1)⟩)
    | .domIn => inclusion D (fun _ h => ⟨h.1, h.2.imp (fun _ hi => hi.1)⟩)
    | .inclIn => inclusion D (fun _ ⟨e, _, h⟩ => ⟨e, h⟩)
    | .predefStrIn => inclusion D (fun _ ⟨i, h⟩ => ⟨R.name i, h⟩)
    | .name => Span.ofFunction (nameMap D)
    | .predefName => Span.ofFunction (predefNameMap D)
    | .so => Span.ofFunction (fun e => vertices D ((arrows D).symm e).1)
    | .ta => Span.ofFunction (fun e => vertices D ((arrows D).symm e).2.1)
    | .pred => Span.ofFunction (fun f => symbols D ((formulas D).symm f).val.symbol)
    | .args => (arguments D).toSpan

/-- Only effective declarations, rather than all vocabulary symbols, need support. -/
def Supported : Prop := ∀ f : Declared D,
  Nonempty (ArrowData (V.signature.arity f.val.symbol))

/-- Equality of argument bags, retaining repeated occurrences. -/
def SameArguments (f g : Declared D) : Prop :=
  ∃ e : ArrowData (V.signature.arity f.val.symbol) ≃
      ArrowData (V.signature.arity g.val.symbol),
    ∀ a, (Candidate.ofFormula f.val).argument a =
      (Candidate.ofFormula g.val).argument (e a)

/-- The literal bag key must separate complete formulas, including vertex data. -/
def Separated : Prop := ∀ f g : Declared D, f.val.symbol = g.val.symbol →
  SameArguments D f g → f = g

end FormalCD.Metamodel.Realization
