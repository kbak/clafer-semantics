module

public import Clafer.Examples.Telematics.Satisfaction

/-!
[impl->req~clafer-appendix-f-complete~1]
[proof->req~clafer-appendix-f-complete~1]
-/

/-!
# The actual compiled and glued telematics model

SoSyM Appendix 6 (PDF p.34).

Apply the selected §6.2.4–5 semantic bridge to the exact resolved fixture and
canonical descent of the same concrete configuration. The theorem discharges
all structural, integer-domain and attached-body assumptions of that bridge.
-/

@[expose] public section
namespace Clafer.Examples.Telematics
open CategoryTheory MCS Compile DPGraph DPGraph.Predicates Constraints

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def inventoryDomains (c : Fin 12) :
    Domains (Telematics.Expressions.inventory c).support (Telematics.Expressions.inventory c).locals :=
  match c with
  | 0 => .nil
  | 1 => .nil
  | 2 => .nil
  | 3 => .nil
  | 4 => .nil
  | 5 => .nil
  | 6 => .nil
  | 7 => .nil
  | 8 => .nil
  | 9 => .nil
  | 10 => .nil
  | 11 => .nil

noncomputable def domains (q : ConstraintId ast) :
    Domains (input.constraint q).support (input.constraint q).locals :=
  inventoryDomains (sourceIndex q)

theorem admissible : ConstraintMeaning.Admissible input integers
    (config.interpret (Semantics.EffectiveCore.erase input)) := by
  apply ConstraintMeaning.admissible_of_local
  · exact Semantics.Realization.local_model core config selected typed
      ⟨inherits, parents_hold, references_hold, keys, multiplicities⟩
  · intro c hc
    change Fin 28 at c
    fin_cases c <;> try { cases hc }
    exact integer_extent

/-- This is the actual arity reduct of the configuration, not an independently
chosen support interpretation. -/
noncomputable def compiledSupport (q : ConstraintId ast) :=
  ConstraintMeaning.supportModel input integers
    (config.interpret (Semantics.EffectiveCore.erase input)) admissible q

/-- Compare every full arity vertex, including the primitive vertex. -/
theorem compiled_objects (q : ConstraintId ast) (v : (input.constraint q).support.Vertex) :
    (compiledSupport q).model.obj v =
      Meaning.objects ⟨((input.constraint q).support.classId v).value, by
        rcases q with ⟨c,k⟩
        change Fin 28 at c
        fin_cases c <;> fin_cases k <;> exact v.isLt⟩ := by
  rcases q with ⟨c,k⟩
  change Fin 28 at c
  fin_cases c <;> fin_cases k <;> fin_cases v <;> rfl

/-- Every attached body retains its complete resolved map support. Parent maps
reverse the same containment relation; other ordinary roles retain their tuple
links and inclusion fixes the shared ambient object. -/
theorem compiled_relations (q : ConstraintId ast) (e : (input.constraint q).support.Edge) :
    ambientRelation ((compiledSupport q).model.map ((input.constraint q).support.arrow e)) =
      ambientRelation (Meaning.span ⟨e.val, by
        rcases q with ⟨c,k⟩
        change Fin 28 at c
        fin_cases c <;> fin_cases k <;> exact e.isLt⟩) := by
  rcases q with ⟨c,k⟩
  change Fin 28 at c
  fin_cases c <;> fin_cases k <;> fin_cases e <;> try rfl
  all_goals
    ext p
    constructor
    · rintro ⟨⟨⟨x,y⟩,h⟩,hs,ht⟩
      exact ⟨⟨(y,x),h⟩,hs,ht⟩
    · rintro ⟨⟨⟨x,y⟩,h⟩,hs,ht⟩
      exact ⟨⟨(y,x),h⟩,hs,ht⟩

/-- Simultaneous source truth at every applicable owner object. -/
theorem source_holds : ConstraintMeaning.SourceHolds input domains integers
    (config.interpret (Semantics.EffectiveCore.erase input)) admissible := by
  intro q
  have hq := occurrence_sourceIndex q
  rw [← hq]
  generalize sourceIndex q = c
  fin_cases c
  · intro x hx
    unfold Expr.Holds
    erw [Expr.denote_congr _ (compiledSupport (occurrence 0)) (Meaning.model 1) rfl
      (compiled_objects (occurrence 0)) (compiled_relations (occurrence 0))]
    exact Meaning.c01_all x
  · intro x hx
    unfold Expr.Holds
    erw [Expr.denote_congr _ (compiledSupport (occurrence 1)) (Meaning.model 11) rfl
      (compiled_objects (occurrence 1)) (compiled_relations (occurrence 1))]
    exact Meaning.c02_all x hx
  · intro x hx
    unfold Expr.Holds
    erw [Expr.denote_congr _ (compiledSupport (occurrence 2)) (Meaning.model 15) rfl
      (compiled_objects (occurrence 2)) (compiled_relations (occurrence 2))]
    exact Meaning.c03_all x
  · intro x hx
    unfold Expr.Holds
    erw [Expr.denote_congr _ (compiledSupport (occurrence 3)) (Meaning.model 15) rfl
      (compiled_objects (occurrence 3)) (compiled_relations (occurrence 3))]
    exact Meaning.c04_all x hx
  · intro x hx
    unfold Expr.Holds
    erw [Expr.denote_congr _ (compiledSupport (occurrence 4)) (Meaning.model 19) rfl
      (compiled_objects (occurrence 4)) (compiled_relations (occurrence 4))]
    have he : x = atom 30 := by
      change x ∈ Meaning.objects 19 at hx
      cases x <;> simp_all [Meaning.objects,Meaning.position,config,heads]
    subst x
    exact Meaning.c05_holds
  · intro x hx
    unfold Expr.Holds
    erw [Expr.denote_congr _ (compiledSupport (occurrence 5)) (Meaning.model 19) rfl
      (compiled_objects (occurrence 5)) (compiled_relations (occurrence 5))]
    have he : x = atom 30 := by
      change x ∈ Meaning.objects 19 at hx
      cases x <;> simp_all [Meaning.objects,Meaning.position,config,heads]
    subst x
    exact Meaning.c06_holds
  · intro x hx
    unfold Expr.Holds
    erw [Expr.denote_congr _ (compiledSupport (occurrence 6)) (Meaning.model 19) rfl
      (compiled_objects (occurrence 6)) (compiled_relations (occurrence 6))]
    have he : x = atom 30 := by
      change x ∈ Meaning.objects 19 at hx
      cases x <;> simp_all [Meaning.objects,Meaning.position,config,heads]
    subst x
    exact Meaning.c07_holds
  · intro x hx
    unfold Expr.Holds
    erw [Expr.denote_congr _ (compiledSupport (occurrence 7)) (Meaning.model 19) rfl
      (compiled_objects (occurrence 7)) (compiled_relations (occurrence 7))]
    have he : x = atom 30 := by
      change x ∈ Meaning.objects 19 at hx
      cases x <;> simp_all [Meaning.objects,Meaning.position,config,heads]
    subst x
    exact Meaning.c08_holds
  · intro x hx
    unfold Expr.Holds
    erw [Expr.denote_congr _ (compiledSupport (occurrence 8)) (Meaning.model 19) rfl
      (compiled_objects (occurrence 8)) (compiled_relations (occurrence 8))]
    have he : x = atom 30 := by
      change x ∈ Meaning.objects 19 at hx
      cases x <;> simp_all [Meaning.objects,Meaning.position,config,heads]
    subst x
    exact Meaning.c09_holds
  · intro x hx
    unfold Expr.Holds
    erw [Expr.denote_congr _ (compiledSupport (occurrence 9)) (Meaning.model 0) rfl
      (compiled_objects (occurrence 9)) (compiled_relations (occurrence 9))]
    have he : x = atom 0 := (rooted.1 x).mp hx
    subst x
    exact Meaning.c10_holds
  · intro x hx
    unfold Expr.Holds
    erw [Expr.denote_congr _ (compiledSupport (occurrence 10)) (Meaning.model 0) rfl
      (compiled_objects (occurrence 10)) (compiled_relations (occurrence 10))]
    have he : x = atom 0 := (rooted.1 x).mp hx
    subst x
    exact Meaning.c11_holds
  · intro x hx
    unfold Expr.Holds
    erw [Expr.denote_congr _ (compiledSupport (occurrence 11)) (Meaning.model 0) rfl
      (compiled_objects (occurrence 11)) (compiled_relations (occurrence 11))]
    have he : x = atom 0 := (rooted.1 x).mp hx
    subst x
    exact Meaning.c12_holds

noncomputable def interpretation := Compile.Realization.interpretation input U
  (ConstraintMeaning.authored input domains integers)

/-- The full generated/glued bank is satisfied by this same nonempty
configuration, with the authored meanings derived from all twelve bodies. -/
theorem compiled_glued_model : interpretation.IsModel
    (Compile.Realization.glued input).toDPGraph (Compile.Realization.descend input config) :=
  ((ConstraintMeaning.whole_model input domains integers selected config admissible).mpr
    ⟨structural_satisfaction, source_holds⟩).2.2.2

theorem nonempty_configuration : (config.head 0).Nonempty := ⟨atom 0, by simp [config,heads]⟩

end Clafer.Examples.Telematics
