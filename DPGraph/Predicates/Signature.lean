module

public import DPGraph.Signature

/-!
# Typed predicate vocabulary

SoSyM Table 3 (PDF p.13), A.1 (PDF p.28), §6.1.1–2/Figure 21 (PDF pp.18–20).
Disjointness uses the accepted Q8 common-target correction. These declarations
carry no meanings or implicit set-valuedness constraints. Finite family arities
retain their central vertex at n = 0; graph-map bindings may repeat arguments.
-/

@[expose] public section

namespace DPGraph.Predicates

inductive Upper where
  | finite (n : Nat)
  | unbounded
  deriving DecidableEq

structure Range where
  lower : Nat
  upper : Upper
  deriving DecidableEq

namespace Arity

inductive Unary where | source | target
inductive UnaryEdge : Unary → Unary → Type where
  | arrow : UnaryEdge .source .target
instance : Quiver Unary := ⟨UnaryEdge⟩
def unary : CategoryTheory.Quiv := CategoryTheory.Quiv.of Unary

inductive Opposite where | left | right
inductive OppositeEdge : Opposite → Opposite → Type where
  | forward : OppositeEdge .left .right
  | backward : OppositeEdge .right .left
instance : Quiver Opposite := ⟨OppositeEdge⟩
def opposite : CategoryTheory.Quiv := CategoryTheory.Quiv.of Opposite

inductive Triangle where | first | middle | last
inductive TriangleEdge : Triangle → Triangle → Type where
  | first : TriangleEdge .first .middle
  | second : TriangleEdge .middle .last
  | direct : TriangleEdge .first .last
instance : Quiver Triangle := ⟨TriangleEdge⟩
def triangle : CategoryTheory.Quiv := CategoryTheory.Quiv.of Triangle

inductive FanOut (n : Nat) where | center | member (i : Fin n)
inductive OutEdge (n : Nat) : FanOut n → FanOut n → Type where
  | edge (i : Fin n) : OutEdge n .center (.member i)
instance (n : Nat) : Quiver (FanOut n) := ⟨OutEdge n⟩
def fanOut (n : Nat) : CategoryTheory.Quiv := CategoryTheory.Quiv.of (FanOut n)

inductive FanIn (n : Nat) where | center | member (i : Fin n)
inductive InEdge (n : Nat) : FanIn n → FanIn n → Type where
  | edge (i : Fin n) : InEdge n (.member i) .center
instance (n : Nat) : Quiver (FanIn n) := ⟨InEdge n⟩
def fanIn (n : Nat) : CategoryTheory.Quiv := CategoryTheory.Quiv.of (FanIn n)

-- [proof->req~predicate-arities~1]
/-- Even an empty family has a central vertex. -/
theorem fanOut_zero_nonempty : Nonempty (fanOut 0) := ⟨.center⟩
theorem fanIn_zero_nonempty : Nonempty (fanIn 0) := ⟨.center⟩
theorem fanOut_zero_isolated (x y : FanOut 0) : IsEmpty (x ⟶ y) :=
  ⟨fun e => by cases e with | edge i => exact Fin.elim0 i⟩
theorem fanIn_zero_isolated (x y : FanIn 0) : IsEmpty (x ⟶ y) :=
  ⟨fun e => by cases e with | edge i => exact Fin.elim0 i⟩

end Arity

inductive Symbol where
  | inverse | commutation
  | key (n : Nat) | cover (n : Nat) | disjoint (n : Nat)
  | setValued | total | singleValued | inclusion
  | targetMultiplicity (range : Range) | sourceMultiplicity (range : Range)

-- [impl->req~predicate-arities~1]
def signature : DPGraph.Signature where
  Symbol := Symbol
  arity
    | .inverse => Arity.opposite
    | .commutation => Arity.triangle
    | .key n => Arity.fanOut n
    | .cover n | .disjoint n => Arity.fanIn n
    | .setValued | .total | .singleValued | .inclusion
    | .targetMultiplicity _ | .sourceMultiplicity _ => Arity.unary

end DPGraph.Predicates
