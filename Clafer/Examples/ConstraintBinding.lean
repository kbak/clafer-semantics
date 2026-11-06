module

public import Clafer.Compile.ConstraintMeaning
public import Clafer.Compile.Examples

/-!
# Full binding and isolated-vertex acceptance boundary

SoSyM §6.2.2 and B.4–B.5. The existing resolved support has an isolated
occurrence of the same class as vertex 3. Changing only its interpretation
preserves every map argument and nevertheless invalidates the source meaning.
-/

@[expose] public section
namespace Clafer.Examples.ConstraintBinding
open CategoryTheory DPGraph DPGraph.Predicates Clafer.Constraints

abbrev s := Constraints.Examples.support

def integers : IntegerRealization Int where
  encode := Function.Embedding.refl _
  decode := id
  decode_encode _ := rfl

def emptyModel : IntegerBinding s Int where
  realization := integers
  model := {
    obj := fun _ => (∅ : Set Int)
    map := fun _ => Span.ofRelation (fun a b => a.val = b.val) }
  same_id _ _ _ := rfl
  inclusion _ _ := by
    apply (Semantics.identity_inclusion_iff _ _).mpr
    exact Set.Subset.refl _
  integer_domain v h := by cases h

theorem empty_coherent : emptyModel.Coherent := by
  intro e f _ _
  exact ⟨⟨Equiv.refl _, fun _ => rfl, fun _ => rfl⟩⟩

def badObjects (v : s.Vertex) : Set Int := if v = 4 then {0} else ∅

def wrongBinding : s.graph ⥤q semanticGraph Int where
  obj := badObjects
  map := fun _ => Span.ofRelation (fun a b => a.val = b.val)

/-- Every mapped arrow is unchanged, including its original links. -/
theorem identical_arrow_arguments (e : s.Edge) :
    HEq (emptyModel.model.map (s.arrow e)) (wrongBinding.map (s.arrow e)) := by
  fin_cases e <;> rfl

noncomputable def meaning := predicateInterpretation
  (fun _ : Unit => Constraints.Examples.constraint) (fun _ => .nil) integers

theorem complete_binding_accepted : emptyModel.model ∈ meaning.meaning () := by
  refine ⟨emptyModel, rfl, rfl, empty_coherent, ?_⟩
  intro x hx
  exact False.elim hx

-- [proof->req~clafer-constraint-preservation-witnesses~1]
/-- Full support admissibility rejects a changed isolated occurrence even
though no argument arrow, body, occurrence symbol or context was changed. -/
theorem wrong_binding_rejected : wrongBinding ∉ meaning.meaning () := by
  rintro ⟨m, _, hm, _, _⟩
  have he := m.same_id (3 : s.Vertex) (4 : s.Vertex) rfl
  rw [hm] at he
  have h0 : (wrongBinding.obj (4 : s.Vertex) : Set Int) 0 := by
    change (0 : Int) = 0
    rfl
  rw [← he] at h0
  exact h0

/-- The actual compiler retains that isolated occurrence and maps it to the
same class as its repeated resolved ID. No bag-key surrogate is used. -/
theorem compiled_isolated_identity :
    (Compile.binding Compile.Examples.input Compile.Examples.q0).obj (3 : s.Vertex) =
      (Compile.binding Compile.Examples.input Compile.Examples.q0).obj (4 : s.Vertex) :=
  Compile.ConstraintMeaning.vertex_same_id _ _ _ _ rfl

end Clafer.Examples.ConstraintBinding
