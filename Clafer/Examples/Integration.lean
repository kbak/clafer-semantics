module

public import Clafer.Compile.Examples
public import Clafer.Compile.GroupExamples
public import Clafer.Examples.Telematics.Structural

/-!
# Representative compilation/gluing integration

SoSyM §6.2.4–5, Figures 16, 22–23 and Appendix 6. These witnesses apply the
Compile and gluing contracts to concrete inputs. The Appendix 6 configuration
is the inherited structural projection, without the twelve printed constraints.
-/

@[expose] public section
namespace Clafer.Examples.Integration
open CategoryTheory MCS Compile DPGraph DPGraph.Predicates

namespace Small
open Clafer.Compile.Examples

-- [impl->req~clafer-representative-integration~1]
noncomputable def glued := gluedGroups input
noncomputable def label := groupLabel input

-- [proof->req~clafer-representative-integration~1]
/-- The concrete source bank supplies both the original MCS discipline and all
FormalCD defaults; these are distinct obligations. -/
theorem compilation_gluing_valid :
    Valid result.labels result.formulas ∧ glued.toRawOver.WellFormed :=
  ⟨output_valid, glued.wellFormed⟩

/-- Exact translated declarations, including the added group component. -/
theorem exact_declarations (φ) : φ ∈ glued.declarations ↔
    (∃ q, (promote input (formula input q)).translate label = φ) ∨
    (∃ p, (generatedGroup input p).translate label = φ) :=
  glued_declarations input φ

theorem nested_names_and_identity :
    glued.className (label.obj basic) = "same" ∧
    glued.className (label.obj nested) = "same" ∧
    label.obj basic ≠ label.obj nested := by
  refine ⟨Gluing.className_label (groupCompatible input) (completeBank input) basic,
    Gluing.className_label (groupCompatible input) (completeBank input) nested, ?_⟩
  intro h
  have he := (Gluing.classLabel_eq_iff (labels input) basic nested).mp h
  exact (by decide : basic ≠ nested) (sourceId_injective input.ast he)

/-- The nested head's endpoints remain the resolved parent and child. -/
theorem nesting_incidence :
    (Gluing.labeledArrow (roles input) (labels input)
      (groupCompatible input).toIncidence (directChildHead input basic nestedChild).val).1 =
      label.obj basic ∧
    (Gluing.labeledArrow (roles input) (labels input)
      (groupCompatible input).toIncidence (directChildHead input basic nestedChild).val).2.1 =
      label.obj nested := ⟨rfl, rfl⟩

theorem shared_target_distinct_maps :
    label.obj (result.roles.target derivedDref) =
      label.obj (result.roles.target abstractDref) ∧
    Gluing.labeledArrow (roles input) (labels input)
      (groupCompatible input).toIncidence derivedDref ≠
    Gluing.labeledArrow (roles input) (labels input)
      (groupCompatible input).toIncidence abstractDref := by
  refine ⟨rfl, ?_⟩
  intro h
  exact shared_target_distinct_dereferences.2.2
    ((Gluing.labeledArrow_eq_iff _ _ _ _ _).mp h)

noncomputable def inheritedHead : (family input).InclusionSlot :=
  ⟨derived, abstractRef, Shape.headInclusion _ _, rfl⟩

theorem inheritance_declared :
    (promote input (formula input (.inl (.inclusion inheritedHead)))).translate label ∈
      glued.declarations := ⟨.inl (.inl (.inclusion inheritedHead)), rfl⟩

/-- Both repeated source occurrences survive with their complete binding and
owner, despite equal boundary numbers. This asserts attachment, not denotation. -/
theorem typed_attachments (q : ConstraintId ast) :
    (input.constraint q).Input ast (boundary ast q) ∧
    (compile input).formulas.owner (.inr q) = q.1 ∧
    (promote input (formula input (.inr q))).translate label ∈ glued.declarations :=
  ⟨input.typed q, rfl, .inl (.inr q), rfl⟩

theorem repeated_binding_after_gluing :
    ((binding input q0).comp label).obj ⟨3, by decide⟩ =
      ((binding input q0).comp label).obj ⟨4, by decide⟩ ∧
    (promote input (formula input (.inr q0))).translate label ≠
      (promote input (formula input (.inr q1))).translate label := by
  refine ⟨rfl, ?_⟩
  intro h
  have hs := congrArg Formula.symbol h
  exact (by decide : q0 ≠ q1) (Sum.inl.inj (Sum.inr.inj hs))

end Small

namespace Xor
open Clafer.Compile.GroupExamples

theorem declarations :
    generatedGroup (input none (by decide)) (parentId none (by decide)) ∈
      (compileAugmented (input none (by decide))).complete.diagram.declarations ∧
    (generatedGroup (input none (by decide)) (parentId none (by decide))).translate
      (groupLabel (input none (by decide))) ∈ (gluedGroups (input none (by decide))).declarations :=
  ⟨emitted none (by decide), glued_emitted none (by decide)⟩

/-- Check the actual optional-head formulas emitted by Compile, at both sides
of gluing, for all zero/one/two child cases. -/
theorem optional_declarations (k : Fin 3) (c : Fin 7)
    (hc : c = 2 ∨ c = 3 ∨ c = 6) :
    ∃ l : LocalId (family (input none (by decide))),
      l.owner = c ∧
      (promote (input none (by decide)) (formula (input none (by decide)) (.inl l))).translate
        (groupLabel (input none (by decide))) ∈ (gluedGroups (input none (by decide))).declarations ∧
      (groupInterpretation (input none (by decide)) (Objects k.val) (authored none (by decide) _)).Satisfies
        ((config (@spread k.val)).interpret (core none (by decide)))
        (promote (input none (by decide)) (formula (input none (by decide)) (.inl l))) ∧
      (groupInterpretation (input none (by decide)) (Objects k.val) (authored none (by decide) _)).Satisfies
        (descendGroups (input none (by decide)) (config (@spread k.val)))
        ((promote (input none (by decide)) (formula (input none (by decide)) (.inl l))).translate
          (groupLabel (input none (by decide)))) := by
  have present : Clafer.Roles.mapPresent ((family (input none (by decide))).shape c).kind
      ((family (input none (by decide))).shape c).hasParent .head = true := by
    rcases hc with rfl | rfl | rfl <;> rfl
  let l : LocalId (family (input none (by decide))) := .multiplicity c ⟨.head, present⟩
  refine ⟨l, rfl, ⟨.inl (.inl l), rfl⟩, ?_, ?_⟩
  · have h := xor_optional_head_maps k c hc
    rcases hc with rfl | rfl | rfl <;> exact h
  · erw [Interpretation.satisfies_translate, descendGroups_reduct]
    have h := xor_optional_head_maps k c hc
    rcases hc with rfl | rfl | rfl <;> exact h

/-- Explicit rejection on each side, stronger than negating a conjunction. -/
theorem boundaries :
    Accepted none (by decide) 1 ∧
    (∀ k : Fin 3, k.val ≠ 1 →
      ¬ (groupInterpretation (input none (by decide)) (Objects k.val) (authored none (by decide) _)).Satisfies
        ((config (@spread k.val)).interpret (core none (by decide)))
        (generatedGroup (input none (by decide)) (parentId none (by decide)))) ∧
    (∀ k : Fin 3, k.val ≠ 1 →
      ¬ (groupInterpretation (input none (by decide)) (Objects k.val) (authored none (by decide) _)).Satisfies
        (descendGroups (input none (by decide)) (config (@spread k.val)))
        ((generatedGroup (input none (by decide)) (parentId none (by decide))).translate
          (groupLabel (input none (by decide))))) := by
  refine ⟨xor_compiled_glued.1, ?_, ?_⟩
  · intro k hk
    rw [compiled_count]
    fin_cases k <;> first | contradiction | decide
  · intro k hk
    rw [glued_count]
    fin_cases k <;> first | contradiction | decide

end Xor

namespace TelematicsStructural
open Clafer.Examples.Telematics.Structural

/-- All 26 printed declaration IDs, plus root/int, survive the compiled label.
This does not claim that the printed constraint bodies occur in this fixture. -/
theorem source_ids (c : ast.Occurrence) :
    ((groupLabel input).obj c).val = sourceId ast c := rfl

theorem exact_declarations (φ) : φ ∈ (Compile.Realization.glued input).declarations ↔
    ∃ q, ((Compile.Realization.bank input).formula q).translate (groupLabel input) = φ :=
  Compile.Realization.glued_declarations input φ

/-- A nonempty model of the generated structural bank, reusing the delivered
inherited realization and its explicit abstract-family obligations. -/
theorem structural_model :
    (Compile.Realization.interpretation input (Fin 25) authored).IsModel
      (Compile.Realization.glued input).toDPGraph (Compile.Realization.descend input config) ∧
    (2 : Fin 25) ∈ config.head 1 ∧ (4 : Fin 25) ∈ config.head 27 :=
  ⟨compiled_glued_model, by decide, by decide⟩

/-- Parentless abstract comp retains its corrected head, and the inherited
version head and server dereference both keep the expected endpoints. -/
theorem version_and_server :
    core.family.parent 20 = none ∧ core.explicitAbstract 20 = true ∧
    core.family.parent 21 = some 20 ∧ core.family.multiplicity 21 = one ∧
    core.family.parent 24 = some 23 ∧ core.family.multiplicity 24 = one ∧
    core.family.reference 24 = .set 22 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end TelematicsStructural
end Clafer.Examples.Integration
