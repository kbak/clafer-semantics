module

public import DPGraph.Examples

/-!
[impl->req~dpgraph-semantics-examples~1]
[proof->req~dpgraph-category~1]
[proof->req~dpgraph-declaration-image~1]
[proof->req~dpgraph-semantics-examples~1]
-/

/-!
# Nonvacuous examples of abstract satisfaction

These give `Examples.signature` an illustrative equality-of-parallel-arrows
interpretation. They do not assign any of the paper's concrete span predicates.
Both satisfying and failing diagrams exist; the declaration set is nonempty.
-/

@[expose] public section

namespace DPGraph.SemanticsExamples

open CategoryTheory Examples

/-- The two parallel arrows of an arity diagram must have equal images. -/
def equalArrows : Interpretation signature arity where
  meaning _ := {d | d.map firstArrow = d.map secondArrow}

theorem collapse_satisfies : equalArrows.Satisfies collapse sourceFormula := rfl

theorem identity_fails : ¬ equalArrows.Satisfies (Prefunctor.id arity) sourceFormula :=
  parallel_distinct

/-- Identity satisfies the target's collapsed declaration. -/
def targetModel : equalArrows.Model targetGraph :=
  ⟨Prefunctor.id arity, by
    intro φ hφ
    change φ = targetFormula at hφ
    subst φ
    rfl⟩

def restrictedModel : equalArrows.Model sourceGraph :=
  equalArrows.reduct collapseHom targetModel

theorem restricted_map : restrictedModel.val = collapse :=
  Prefunctor.comp_id collapse

theorem restricted_is_model : equalArrows.IsModel sourceGraph restrictedModel.val :=
  restrictedModel.property

/-- Bare graph maps need not restrict models: identity fails at the source. -/
theorem identity_not_source_model :
    ¬ equalArrows.IsModel sourceGraph (Prefunctor.id arity) := by
  intro h
  exact identity_fails (h sourceFormula source_declared)

def finalModel : equalArrows.Model finalGraph :=
  ⟨Prefunctor.id arity, by
    intro φ hφ
    change φ = finalFormula at hφ
    subst φ
    rfl⟩

/-- Category notation uses the original morphisms, and reduct reverses order. -/
theorem category_reduct_comp :
    equalArrows.reduct (show sourceGraph ⟶ finalGraph from collapseHom ≫ swapHom) finalModel =
      equalArrows.reduct collapseHom (equalArrows.reduct swapHom finalModel) :=
  equalArrows.reduct_comp collapseHom swapHom finalModel

theorem category_reduct_id :
    equalArrows.reduct (𝟙 targetGraph) targetModel = targetModel :=
  equalArrows.reduct_id targetModel

theorem category_units :
    (𝟙 sourceGraph) ≫ collapseHom = collapseHom ∧
      collapseHom ≫ (𝟙 targetGraph) = collapseHom :=
  ⟨Category.id_comp (X := sourceGraph) (Y := targetGraph) collapseHom,
    Category.comp_id (X := sourceGraph) (Y := targetGraph) collapseHom⟩

theorem category_assoc :
    (collapseHom ≫ swapHom) ≫ (𝟙 finalGraph) =
      collapseHom ≫ (swapHom ≫ (𝟙 finalGraph)) :=
  Category.assoc collapseHom swapHom (𝟙 finalGraph)

theorem category_ext {F J : sourceGraph ⟶ targetGraph}
    (h : F.toPrefunctor = J.toPrefunctor) : F = J := Hom.ext h

/-- Empty declarations are satisfied, but this does not reflect satisfaction
of the extra declaration in `sourceGraph`. -/
def inclusion : Hom undeclaredGraph sourceGraph where
  toPrefunctor := Prefunctor.id arity
  preserves h := False.elim h

theorem model_not_reflected :
    equalArrows.IsModel undeclaredGraph
        (inclusion.toPrefunctor.comp (Prefunctor.id arity)) ∧
      ¬ equalArrows.IsModel sourceGraph (Prefunctor.id arity) :=
  ⟨by intro _ h; exact False.elim h, identity_not_source_model⟩

/-- The noninjective collapse has exactly the translated source declaration. -/
theorem collapsed_declaration_image :
    targetGraph.declarations = (fun φ => φ.translate collapse) '' sourceGraph.declarations := by
  ext φ
  constructor
  · intro h
    change φ = targetFormula at h
    subst φ
    exact ⟨sourceFormula, source_declared, rfl⟩
  · rintro ⟨ψ, hψ, rfl⟩
    change ψ = sourceFormula at hψ
    subst ψ
    exact collapse_preserves

theorem collapse_model_iff (m : arity ⥤q arity) :
    equalArrows.IsModel targetGraph m ↔ equalArrows.IsModel sourceGraph (collapse.comp m) :=
  equalArrows.isModel_iff_of_declarations_image
    (S := sourceGraph) (T := targetGraph) collapse collapsed_declaration_image m

def collidingBank : Bool → Formula signature arity
  | false => sourceFormula
  | true => targetFormula

/-- Two distinct source bindings may become one target declaration. -/
theorem colliding_translations :
    (collidingBank false).translate collapse = (collidingBank true).translate collapse := by
  have hc : collapse.comp collapse = collapse := by
    apply Prefunctor.ext (by intro x; rfl)
    intro x y a
    cases x <;> cases y <;> rfl
  change sourceFormula.translate collapse = targetFormula.translate collapse
  rw [translated_declaration]
  exact congrArg (Formula.mk (σ := signature) (G := arity) .mark) hc.symm

theorem colliding_bank_model_iff (m : arity ⥤q arity) :
    equalArrows.IsModel ⟨arity, Set.range (fun i => (collidingBank i).translate collapse)⟩ m ↔
      equalArrows.IsModel ⟨arity, Set.range collidingBank⟩ (collapse.comp m) :=
  equalArrows.isModel_range_translate collidingBank collapse m

/-- Explicitly larger semantic vertices; only a universe lift of this example. -/
structure LargeVertex : Type 1 where
  down : Vertex

instance largeQuiver : Quiver.{1} LargeVertex where
  Hom x y := ULift.{1} (x.down ⟶ y.down)

def largeGraph : Quiv.{1, 1} := Quiv.of LargeVertex

def liftDiagram : arity ⥤q largeGraph where
  obj x := ⟨x⟩
  map a := ⟨a⟩

def largeEqualArrows : Interpretation signature largeGraph where
  meaning _ := {d | d.map firstArrow = d.map secondArrow}

/-- The same small signature and carrier can be interpreted in larger vertex
and arrow universes without lifting the syntax or using a resizing axiom. -/
def largeTargetModel : largeEqualArrows.Model targetGraph :=
  ⟨liftDiagram, by
    intro φ hφ
    change φ = targetFormula at hφ
    subst φ
    rfl⟩

theorem large_reduct_map :
    (largeEqualArrows.reduct collapseHom largeTargetModel).val =
      collapse.comp liftDiagram := rfl

theorem large_identity_fails : ¬ largeEqualArrows.Satisfies liftDiagram sourceFormula := by
  intro h
  exact parallel_distinct (congrArg ULift.down h)

end DPGraph.SemanticsExamples
