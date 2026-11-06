module

public import DPGraph
public import Mathlib.Data.Fintype.Basic

/-!
# Finite witnesses for the generic DP-graph definitions

SoSyM B.4, Definitions 6–10: a syntax-only predicate with parallel arrows and
an isolated vertex. `mark` has no asserted predicate semantics.
-/

@[expose] public section

namespace DPGraph.Examples

open CategoryTheory

inductive Vertex
  | source | target | isolated
  deriving DecidableEq

instance : Fintype Vertex where
  elems := {.source, .target, .isolated}
  complete x := by cases x <;> simp

/-- Exactly two parallel arrows; all other endpoint pairs have no arrows. -/
instance vertexQuiver : Quiver Vertex where
  Hom
    | .source, .target => Bool
    | _, _ => PEmpty

instance (x y : Vertex) : Fintype (x ⟶ y) := by
  cases x <;> cases y
  all_goals first
    | exact (inferInstance : Fintype Bool)
    | exact (inferInstance : Fintype PEmpty)

def arity : Quiv.{0, 0} := Quiv.of Vertex

def firstArrow : Vertex.source ⟶ Vertex.target := false

def secondArrow : Vertex.source ⟶ Vertex.target := true

theorem parallel_distinct : firstArrow ≠ secondArrow := by
  change (false : Bool) ≠ true
  decide

theorem isolated_no_out (x : Vertex) (a : Vertex.isolated ⟶ x) : False := by
  cases x <;> exact PEmpty.elim a

theorem isolated_no_in (x : Vertex) (a : x ⟶ Vertex.isolated) : False := by
  cases x <;> exact PEmpty.elim a

inductive Symbol
  | mark

/-- A syntactic symbol, deliberately without an interpretation. -/
def signature : Signature.{0, 0, 0} where
  Symbol := Symbol
  arity _ := arity

/-- Binding the whole arity includes its isolated vertex. -/
def sourceFormula : Formula signature arity := ⟨.mark, Prefunctor.id arity⟩

/-- Keeps vertices fixed and identifies both parallel arrows with `firstArrow`. -/
def collapse : arity ⥤q arity where
  obj x := x
  map {x y} a := match x, y with
    | .source, .target => false
    | _, _ => a

/-- Explicit target binding: both arguments are the first arrow. -/
def targetFormula : Formula signature arity := ⟨.mark, collapse⟩

-- [impl->req~dpgraph-examples~1]
def sourceGraph : DPGraph signature where
  carrier := arity
  declarations := {sourceFormula}

def targetGraph : DPGraph signature where
  carrier := arity
  declarations := {targetFormula}

theorem source_declared : sourceFormula ∈ sourceGraph.declarations := rfl

theorem source_nonempty : sourceGraph.declarations.Nonempty := ⟨sourceFormula, source_declared⟩

theorem translated_declaration : sourceFormula.translate collapse = targetFormula := by
  exact congrArg (Formula.mk (σ := signature) (G := arity) Symbol.mark)
    (Prefunctor.id_comp collapse)

def collapseHom : Hom sourceGraph targetGraph where
  toPrefunctor := collapse
  preserves := by
    intro f hf
    change f = sourceFormula at hf
    subst f
    exact translated_declaration

theorem images_equal : collapse.map firstArrow = collapse.map secondArrow := rfl

/-- The collapse really differs from the identity graph map. -/
theorem collapse_ne_id : collapse ≠ Prefunctor.id arity := by
  intro h
  have hm := Prefunctor.congr_hom h secondArrow
  exact parallel_distinct hm

-- [proof->req~dpgraph-examples~1]
theorem collapse_preserves : sourceFormula.translate collapse ∈ targetGraph.declarations :=
  collapseHom.preserves source_declared

theorem isolated_binding : sourceFormula.binding.obj Vertex.isolated = Vertex.isolated := rfl

theorem isolated_translation : targetFormula.binding.obj Vertex.isolated = Vertex.isolated := rfl

/-- A second explicit nonidentity map swaps the two parallel arrows. -/
def swap : arity ⥤q arity where
  obj x := x
  map {x y} a := match x, y with
    | .source, .target => !a
    | _, _ => a

def finalFormula : Formula signature arity := ⟨.mark, collapse.comp swap⟩

def finalGraph : DPGraph signature where
  carrier := arity
  declarations := {finalFormula}

def swapHom : Hom targetGraph finalGraph where
  toPrefunctor := swap
  preserves := by
    intro f hf
    change f = targetFormula at hf
    subst f
    rfl

/-- Exercise the general composition law on two concrete, composable maps. -/
theorem explicit_translation_comp :
    (sourceFormula.translate collapse).translate swap =
      sourceFormula.translate (collapse.comp swap) :=
  Formula.translate_comp sourceFormula collapse swap

theorem composed_preserves :
    sourceFormula.translate (collapse.comp swap) ∈ finalGraph.declarations :=
  Hom.comp_preserves collapseHom swapHom source_declared

/-- Same graph, but the required declaration is absent. -/
def undeclaredGraph : DPGraph signature where
  carrier := arity
  declarations := ∅

/-- `collapse` remains a graph map to this carrier. -/
def unpreservedMap : sourceGraph.carrier ⥤q undeclaredGraph.carrier := collapse

theorem declaration_absent :
    sourceFormula.translate unpreservedMap ∉ undeclaredGraph.declarations := by
  intro h
  exact h

/-- No preservation proof can equip this specific underlying graph map. -/
theorem no_preservation : ¬ (∀ {f}, f ∈ sourceGraph.declarations →
    f.translate unpreservedMap ∈ undeclaredGraph.declarations) := by
  intro h
  exact declaration_absent (h source_declared)

theorem no_dp_lift : ¬ ∃ F : Hom sourceGraph undeclaredGraph,
    F.toPrefunctor = unpreservedMap := by
  rintro ⟨F, hF⟩
  apply declaration_absent
  rw [← hF]
  exact F.preserves source_declared

end DPGraph.Examples
