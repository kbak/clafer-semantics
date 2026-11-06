module

public import DPGraph.Predicates.SemanticGraph
public import DPGraph.Predicates.Meaning
public import DPGraph.Semantics

-- [impl->req~predicate-interpretation~1]

/-!
# The concrete interpretation

Table 3/A.1/§6.1.1–2 meanings applied to actual arity graph maps. B.4/B.5
formula satisfaction, translation and model restriction use the generic API.
No implicit predicate declarations or whole-model reflection are added.
-/

@[expose] public section

universe u w

namespace DPGraph.Predicates

open CategoryTheory Arity

/-- All symbols have explicit meanings in the bounded graph. -/
def interpretation (U : Type u) : Interpretation signature (semanticGraph.{u,w} U) where
  meaning
    | .inverse => fun d => Inverse (d.map OppositeEdge.forward) (d.map OppositeEdge.backward)
    | .commutation => fun d => Commutation (d.map TriangleEdge.first)
        (d.map TriangleEdge.second) (d.map TriangleEdge.direct)
    | .key _ => fun d => Key (fun i => d.map (OutEdge.edge i))
    | .cover _ => fun d => Cover (fun i => d.map (InEdge.edge i))
    | .disjoint _ => fun d => Disjoint (fun i => d.map (InEdge.edge i))
    | .setValued => fun d => SetValued (d.map UnaryEdge.arrow)
    | .total => fun d => Total (d.map UnaryEdge.arrow)
    | .singleValued => fun d => SingleValued (d.map UnaryEdge.arrow)
    | .inclusion => fun d => Inclusion (d.map UnaryEdge.arrow)
    | .targetMultiplicity range => fun d => TargetMultiplicity range (d.map UnaryEdge.arrow)
    | .sourceMultiplicity range => fun d => SourceMultiplicity range (d.map UnaryEdge.arrow)

/-- A convenient binding for any unary predicate; endpoints remain subsets. -/
def unaryDiagram {U : Type u} {A B : Set U} (q : Span.{u,u,max u w} A B) :
    unary ⥤q semanticGraph.{u,w} U where
  obj | .source => A | .target => B
  map | .arrow => q

def outDiagram {U : Type u} {n : Nat} {A : Set U} {B : Fin n → Set U}
    (q : ∀ i, Span.{u,u,max u w} A (B i)) : fanOut n ⥤q semanticGraph.{u,w} U where
  obj | .center => A | .member i => B i
  map | .edge i => q i

def inDiagram {U : Type u} {n : Nat} {A : Fin n → Set U} {B : Set U}
    (q : ∀ i, Span.{u,u,max u w} (A i) B) : fanIn n ⥤q semanticGraph.{u,w} U where
  obj | .center => B | .member i => A i
  map | .edge i => q i

end DPGraph.Predicates
