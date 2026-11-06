module

public import FormalCD.Metamodel.Basic
public import FormalCD.Metamodel.Binding

/-!
[impl->req~formalcd-formula-identity~1]
[impl->req~formalcd-metamodel-disciplines~1]
[proof->req~formalcd-formula-identity~1]
[proof->req~formalcd-metamodel-disciplines~1]
-/

/-!
# Name and arity discipline meanings

SoSyM §6.1.3 PDF p.21 and B.4 Definition 8 PDF p.31. The context explicitly supplies
registry/name decoding, the represented signature and graph, object encodings,
and candidate vertex/occurrence data absent from the drawing. Context contains
no validity proof. The predicates check that data against the actual spans.
-/

@[expose] public section

universe p s va ua v u z w

namespace FormalCD.Metamodel
open CategoryTheory DPGraph DPGraph.Predicates

/-- Expose the subset carried by a vertex of a bounded interpretation. -/
def objects {U : Type z} {G : Quiv.{v,u}}
    (d : G ⥤q semanticGraph.{z,w} U) (n : G) : Set U := d.obj n

structure NameContext (R : Registry.{p}) (U : Type z) where
  text : String ↪ U
  name : U → String
  identifier : U → Option R.Id

/-- Optional predefined entries retain canonical names and identity. The square
compares actual name restrictions as spans, so multiplicity is also preserved. -/
structure NameDiscipline {R : Registry.{p}} {U : Type z} (C : NameContext R U)
    (d : nameShape ⥤q semanticGraph.{z,w} U) : Prop where
  names : ∀ l : (d.map NameEdge.name).Link,
    ((d.map NameEdge.name).target l).val = C.text (C.name ((d.map NameEdge.name).source l).val)
  predefined_names : ∀ c ∈ (objects d .class), ∀ i,
    C.identifier c = some i → C.name c = R.name i
  user_names : ∀ c ∈ (objects d .class), C.identifier c = none → ¬ R.Reserved (C.name c)
  unique_identifier : ∀ c ∈ (objects d .class), ∀ c' ∈ (objects d .class), ∀ i,
    C.identifier c = some i → C.identifier c' = some i → c = c'
  realized : ∀ c, c ∈ (objects d .predef) ↔ c ∈ (objects d .class) ∧ ∃ i, C.identifier c = some i
  reserved : ∀ t, t ∈ (objects d .predefStr) ↔ ∃ i, C.text (R.name i) = t
  singleton_kind : ∀ c, c ∈ (objects d .sing) ↔
    c ∈ (objects d .class) ∧ ∃ i, C.identifier c = some i ∧ R.kind i = .singleton
  primitive_kind : ∀ c, c ∈ (objects d .dom) ↔
    c ∈ (objects d .class) ∧ ∃ i, C.identifier c = some i ∧ R.kind i = .primitive
  inclusion_names : ∀ c ∈ (objects d .incl), C.name c = "isA"
  restriction : Nonempty (Span.Iso
    (((d.map NameEdge.predefIn).comp (d.map NameEdge.classIn)).comp (d.map NameEdge.name))
    ((d.map NameEdge.predefName).comp (d.map NameEdge.predefStrIn)))

/-- Explicit encodings into one bounded ambient type, not an all-types SetMap.
The domain graph/signature can occupy independent universes. Embeddings into U
are ordinary supplied functions, never casts identifying syntax with types. -/
structure ArityContext (σ : Signature.{s,va,ua}) (G : Quiv.{v,u}) (U : Type z) where
  symbol : σ.Symbol ↪ U
  vertex : G ↪ U
  arrow : ArrowData G ↪ U

/-- Data may be missing or malformed, including missing/duplicate occurrence
indices. Optional values make this meaningful even for an empty signature or
zero-arrow arities and arbitrary candidate span diagrams. -/
structure ArityDescriptor {σ : Signature.{s,va,ua}} {G : Quiv.{v,u}} {U : Type z}
    (d : arityShape ⥤q semanticGraph.{z,w} U) where
  candidate : (objects d .formula) → Option (Candidate σ G)
  index : ∀ f (c : Candidate σ G),
    (d.map ArityEdge.args).toFamily.Index f → Option (ArrowData (σ.arity c.symbol))

namespace ArityDescriptor
variable {σ : Signature.{s,va,ua}} {G : Quiv.{v,u}} {U : Type z}

def missing (d : arityShape ⥤q semanticGraph.{z,w} U) :
    ArityDescriptor (σ := σ) (G := G) d := ⟨fun _ => none, fun _ _ _ => none⟩

/-- Each formula selects a symbol and a complete indexed binding. The bijection
checks all occurrences, while Candidate.Valid checks both endpoints and retains
all vertex images, including isolated vertices. No total-args assumption here. -/
def ValidAt {d : arityShape ⥤q semanticGraph.{z,w} U}
    (C : ArityContext σ G U) (D : ArityDescriptor (σ := σ) (G := G) d)
    (f : (objects d .formula)) : Prop :=
  ∃ c, D.candidate f = some c ∧ c.Valid ∧
    (∃ e : (d.map ArityEdge.args).toFamily.Index f ≃ ArrowData (σ.arity c.symbol),
      (∀ l, D.index f c l = some (e l)) ∧
      (∀ l, ((d.map ArityEdge.args).target l.val).val = C.arrow (c.argument (e l)))) ∧
    Nonempty ((d.map ArityEdge.pred).toFamily.Index f) ∧
    (∀ l : (d.map ArityEdge.pred).toFamily.Index f,
      ((d.map ArityEdge.pred).target l.val).val = C.symbol c.symbol)

end ArityDescriptor

structure ArityDiscipline {σ : Signature.{s,va,ua}} {G : Quiv.{v,u}} {U : Type z}
    (C : ArityContext σ G U) (d : arityShape ⥤q semanticGraph.{z,w} U)
    (D : ArityDescriptor (σ := σ) (G := G) d) : Prop where
  classes : (objects d .class) = Set.range C.vertex
  maps : (objects d .map) = Set.range C.arrow
  symbols : (objects d .signature) = Set.range C.symbol
  sources : ∀ e (l : (d.map ArityEdge.so).Link),
    ((d.map ArityEdge.so).source l).val = C.arrow e →
    ((d.map ArityEdge.so).target l).val = C.vertex e.1
  targets : ∀ e (l : (d.map ArityEdge.ta).Link),
    ((d.map ArityEdge.ta).source l).val = C.arrow e →
    ((d.map ArityEdge.ta).target l).val = C.vertex e.2.1
  formulas : ∀ f, D.ValidAt C f

/-- Any accepted descriptor yields the existing typed Formula, by validation. -/
theorem represented_formula {σ : Signature.{s,va,ua}} {G : Quiv.{v,u}} {U : Type z}
    {C : ArityContext σ G U} {d : arityShape ⥤q semanticGraph.{z,w} U}
    {D : ArityDescriptor (σ := σ) (G := G) d} {f : (objects d .formula)}
    (h : D.ValidAt C f) : ∃ φ : Formula σ G, D.candidate f = some (Candidate.ofFormula φ) := by
  rcases h with ⟨c, hc, hv, _⟩
  exact ⟨c.toFormula hv, by simpa using hc⟩

/-- The empty-arity boundary follows from complete indexing; generic formulas
remain legal, but the printed total args declaration rules out such a fiber. -/
theorem zero_arrow_not_total {σ : Signature.{s,va,ua}} {G : Quiv.{v,u}} {U : Type z}
    {d : arityShape ⥤q semanticGraph.{z,w} U} (f : (objects d .formula))
    (c : Candidate σ G) [IsEmpty (ArrowData (σ.arity c.symbol))]
    (e : (d.map ArityEdge.args).toFamily.Index f ≃ ArrowData (σ.arity c.symbol)) :
    ¬ Total (d.map ArityEdge.args) := by
  intro h
  obtain ⟨l, hl⟩ := h f
  exact isEmptyElim (e ⟨l, hl⟩)

end FormalCD.Metamodel
