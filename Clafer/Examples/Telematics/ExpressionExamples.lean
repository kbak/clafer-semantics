module

public import Clafer.Examples.Telematics.ExpressionEnvironment
public import Clafer.Constraints.DenotationDefined
public import Clafer.Constraints.CollectionMeaning

/-! # Telematics operator-combination witnesses

SoSyM Appendix 6 (PDF p.34).

These check the actual c01–c12 bodies on the inherited fixture. The supplied
structural projection has one display per ECU and extraDisplay present, so its
c06/c07 results are deliberately false. Complete selected model satisfaction
is a separate #64 integration obligation.
-/

@[expose] public section
namespace Clafer.Examples.Telematics.ExpressionExamples
open Clafer.Constraints Telematics.Expressions Telematics.ExpressionEnvironment

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

-- The ordinary head maps reuse precisely #66's shared containment tuples.
-- [proof->req~clafer-constraint-semantic-laws~1]
theorem image_reduced (c : Fin 28) (e d : Int) (i : Fin 34) (S : Set U) :
    relationalImage S (ambientRelation ((model c e d).model.map ((support c).arrow i))) =
      {y | ∃ x, x ∈ S ∧ x ∈ objects (maps i).source ∧
        y ∈ objects (maps i).target ∧ links e d i x y} := by
  rw [reduced_map]
  rfl

/-- Both plaDisplays inherit the same empty cache class through their own
options objects; no disjoint clone is introduced for the inherited view. -/
theorem inherited_cache_empty :
    (inheritedCache : Expr (support 15) [] _).denote (model 15 2 3)
      (.closed (atom 4)) = some ∅ := by
  simp only [inheritedCache,head5,head13,Expr.denote,lift₂,Option.bind_some,Option.map_some,
    Environment.closed]
  rw [image_reduced, image_reduced]
  simp [objects,maps,position,links,Telematics.Structural.config,Telematics.Structural.heads,Telematics.Structural.ownership]

theorem no_cache : c03.Holds (model 15 2 3) (.closed (atom 4)) := by
  unfold c03 Expr.Holds
  rw [denotes_no _ _ _ ∅ inherited_cache_empty Set.finite_empty]
  simp


theorem displays1_value (c : Fin 28) (e d : Int) (ρ : Environment (support c) U []) :
    displays1.denote (model c e d) ρ = some {atom 4} := by
  simp only [displays1,head15,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  rw [image_reduced, model_objects]
  simp [objects,maps,position,links,Telematics.Structural.config,Telematics.Structural.heads,Telematics.Structural.ownership,
    Set.ext_iff]

theorem displays2_value (c : Fin 28) (e d : Int) (ρ : Environment (support c) U []) :
    displays2.denote (model c e d) ρ = some {atom 5} := by
  simp only [displays2,head15,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  rw [image_reduced, model_objects]
  simp [objects,maps,position,links,Telematics.Structural.config,Telematics.Structural.heads,Telematics.Structural.ownership,
    Set.ext_iff]

theorem extra_value (e d : Int) :
    (head23 (.this : Expr (support 19) [] _)).denote (model 19 e d)
      (.closed (atom 19)) = some {atom 22} := by
  simp only [head23,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  rw [image_reduced]
  simp [objects,maps,position,links,Telematics.Structural.config,Telematics.Structural.heads,Telematics.Structural.ownership,
    Environment.closed]

theorem dual_value (e d : Int) :
    (head22 (head20 (.this : Expr (support 19) [] _))).denote (model 19 e d)
      (.closed (atom 19)) = some {atom 21} := by
  simp only [head22,head20,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  simp only [image_reduced]
  simp [objects,maps,position,links,Telematics.Structural.config,Telematics.Structural.heads,Telematics.Structural.ownership,
    Environment.closed]

theorem ecu2_value (c : Fin 28) (e d : Int) (ρ : Environment (support c) U []) :
    (Expr.extent 17).denote (model c e d) ρ = some {atom 3} := by
  simp [Expr.denote,objects,position,Telematics.Structural.config,Telematics.Structural.heads]

-- [proof->req~clafer-appendix-f-expressions~1]
theorem actual_c05 : c05.Holds (model 19 2 3) (.closed (atom 19)) := by
  unfold c05 Expr.Holds
  rw [denotes_iff _ _ _ _ _ _
    (denotes_some _ _ _ _ (dual_value 2 3) (Set.finite_singleton _))
    (denotes_some _ _ _ _ (ecu2_value 19 2 3 _) (Set.finite_singleton _))]
  simp

theorem actual_c06_rejects_one_display :
    ¬ c06.Holds (model 19 2 3) (.closed (atom 19)) := by
  have he := denotes_some _ _ _ _ (extra_value 2 3) (Set.finite_singleton _)
  have hc : (exactlyTwo displays1).denote (model 19 2 3) (.closed (atom 19)) = some ⟨False⟩ := by
    simp [exactlyTwo,Expr.denote,displays1_value,lift₂,finiteCard]
  have h := denotes_iff _ _ _ _ _ _ he hc
  simp [Expr.Holds,c06,h]

/-- c07 includes the implication inside the equivalence. With ECU2 present
and one display, its right side is false despite extraDisplay being present. -/
theorem actual_c07_rejects_one_display :
    ¬ c07.Holds (model 19 2 3) (.closed (atom 19)) := by
  have he := denotes_some _ _ _ _ (extra_value 2 3) (Set.finite_singleton _)
  have hp := denotes_some _ _ _ _ (ecu2_value 19 2 3 (.closed (atom 19))) (Set.finite_singleton _)
  have hc : (exactlyTwo displays2).denote (model 19 2 3) (.closed (atom 19)) = some ⟨False⟩ := by
    simp [exactlyTwo,Expr.denote,displays2_value,lift₂,finiteCard]
  have hi := denotes_implies _ _ _ _ _ _ hp hc
  have h := denotes_iff _ _ _ _ _ _ he hi
  simp [Expr.Holds,c07,h]


theorem small_options_empty :
    (head3 (head2 (.this : Expr (support 1) [] _))).denote (model 1 2 3)
      (.closed (atom 12)) = some ∅ := by
  simp only [head3,head2,Expr.denote,lift₂,Option.bind_some,Option.map_some,image_reduced]
  simp [objects,maps,position,links,Telematics.Structural.config,Telematics.Structural.heads,Telematics.Structural.ownership]

theorem cache_empty :
    (head5 (.this : Expr (support 1) [] _)).denote (model 1 2 3)
      (.closed (atom 12)) = some ∅ := by
  simp only [head5,Expr.denote,lift₂,Option.bind_some,Option.map_some,image_reduced]
  simp [objects,maps,position,links,Telematics.Structural.config,Telematics.Structural.heads,Telematics.Structural.ownership]

theorem fixed_empty :
    (head7 (head6 (head5 (.this : Expr (support 1) [] _)))).denote (model 1 2 3)
      (.closed (atom 12)) = some ∅ := by
  simp only [head7,head6,head5,Expr.denote,lift₂,Option.bind_some,Option.map_some,image_reduced]
  simp [objects,maps,position,links,Telematics.Structural.config,Telematics.Structural.heads,Telematics.Structural.ownership]

theorem actual_c01 : c01.Holds (model 1 2 3) (.closed (atom 12)) := by
  have hs := denotes_some _ _ _ _ small_options_empty Set.finite_empty
  have hc := denotes_some _ _ _ _ cache_empty Set.finite_empty
  have hf := denotes_some _ _ _ _ fixed_empty Set.finite_empty
  have ha : (Expr.and (head3 (head2 Expr.this)).some (head5 Expr.this).some).denote
      (model 1 2 3) (.closed (atom 12)) = some ⟨False⟩ := by
    simp only [denote_and,hs,hc,lift₂,Option.bind_some,Option.map_some]
    simp
  have h := denotes_implies _ _ _ _ _ _ ha hf
  simpa [Expr.Holds,c01] using h

theorem server_value :
    (dereference12 (head12 (.widenObjects inclusion15 (Expr.this : Expr (support 15) [] _)))).denote
      (model 15 2 3) (.closed (atom 4)) = some {atom 2} := by
  simp only [dereference12,head12,Expr.denote,lift₂,Option.bind_some,Option.map_some,image_reduced]
  simp [objects,maps,position,links,Telematics.Structural.config,Telematics.Structural.heads,Telematics.Structural.ownership,
    Telematics.Structural.targets,Environment.closed,Set.ext_iff]

theorem parent_value :
    (Expr.widenObjects inclusion14 (parent15 (Expr.this : Expr (support 15) [] _))).denote
      (model 15 2 3) (.closed (atom 4)) = some {atom 2} := by
  simp only [parent15,Expr.denote,lift₂,Option.bind_some,Option.map_some,image_reduced]
  simp [objects,maps,position,links,Telematics.Structural.config,Telematics.Structural.heads,Telematics.Structural.ownership,
    Environment.closed,Set.ext_iff]

theorem actual_c04 : c04.Holds (model 15 2 3) (.closed (atom 4)) := by
  change lift₂ (fun (S T : Set U) => ULift.up (S = T))
    ((dereference12 (head12 (.widenObjects inclusion15 Expr.this))).denote
      (model 15 2 3) (.closed (atom 4)))
    ((Expr.widenObjects inclusion14 (parent15 Expr.this)).denote
      (model 15 2 3) (.closed (atom 4))) = some ⟨True⟩
  rw [server_value,parent_value]
  simp [lift₂]

theorem large_local :
    (head26 (head24 (Expr.this : Expr (support 19) [] _))).denote
      (model 19 2 3) (.closed (atom 19)) = some {atom 24} := by
  simp only [head26,head24,Expr.denote,lift₂,Option.bind_some,Option.map_some,image_reduced]
  simp [objects,maps,position,links,Telematics.Structural.config,Telematics.Structural.heads,Telematics.Structural.ownership,
    Environment.closed]

theorem small_local :
    (head25 (head24 (Expr.this : Expr (support 19) [] _))).denote
      (model 19 2 3) (.closed (atom 19)) = some ∅ := by
  simp only [head25,head24,Expr.denote,lift₂,Option.bind_some,Option.map_some,image_reduced]
  simp [objects,maps,position,links,Telematics.Structural.config,Telematics.Structural.heads,Telematics.Structural.ownership]

theorem all_small :
    (head3 (allSizes : Expr (support 19) [] _)).denote
      (model 19 2 3) (.closed (atom 19)) = some ∅ := by
  simp only [allSizes,head3,head2,head13,head15,Expr.denote,lift₂,
    Option.bind_some,Option.map_some,image_reduced]
  simp [objects,maps,position,links,Telematics.Structural.config,Telematics.Structural.heads,Telematics.Structural.ownership]

theorem all_large :
    (head4 (allSizes : Expr (support 19) [] _)).denote
      (model 19 2 3) (.closed (atom 19)) = some {atom 16,atom 17} := by
  simp only [allSizes,head4,head2,head13,head15,Expr.denote,lift₂,
    Option.bind_some,Option.map_some]
  rw [image_reduced, image_reduced, image_reduced, image_reduced, model_objects]
  simp [objects,maps,position,links,Telematics.Structural.config,Telematics.Structural.heads,Telematics.Structural.ownership,
    Set.ext_iff]
  aesop

theorem actual_c08 : c08.Holds (model 19 2 3) (.closed (atom 19)) := by
  have hl := denotes_some _ _ _ _ large_local (Set.finite_singleton _)
  have hs := denotes_some _ _ _ _ all_small Set.finite_empty
  have hn : (Expr.not (head3 allSizes).some).denote (model 19 2 3) (.closed (atom 19)) =
      some ⟨True⟩ := by simp only [denote_not,hs,Option.map_some]; simp
  have h := denotes_iff _ _ _ _ _ _ hl hn
  simpa [Expr.Holds,c08] using h

theorem actual_c09 : c09.Holds (model 19 2 3) (.closed (atom 19)) := by
  have hs := denotes_some _ _ _ _ small_local Set.finite_empty
  have hl := denotes_some _ _ _ _ all_large (by simp)
  have hn : (Expr.not (head4 allSizes).some).denote (model 19 2 3) (.closed (atom 19)) =
      some ⟨False⟩ := by simp only [denote_not,hl,Option.map_some]; simp
  have h := denotes_iff _ _ _ _ _ _ hs hn
  simpa [Expr.Holds,c09] using h


theorem global_dual :
    (head22 (head20 (Expr.extent 19 : Expr (support 0) [] _))).denote
      (model 0 2 3) (.closed (atom 0)) = some {atom 21} := by
  simp only [head22,head20,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  rw [image_reduced]
  rw [image_reduced]
  rw [model_objects]
  simp [objects,maps,position,links,Telematics.Structural.config,Telematics.Structural.heads,Telematics.Structural.ownership]

theorem global_extra :
    (head23 (Expr.extent 19 : Expr (support 0) [] _)).denote
      (model 0 2 3) (.closed (atom 0)) = some {atom 22} := by
  simp only [head23,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  rw [image_reduced]
  rw [model_objects]
  simp [objects,maps,position,links,Telematics.Structural.config,Telematics.Structural.heads,Telematics.Structural.ownership]

theorem global_large :
    (head26 (head24 (Expr.extent 19 : Expr (support 0) [] _))).denote
      (model 0 2 3) (.closed (atom 0)) = some {atom 24} := by
  simp only [head26,head24,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  rw [image_reduced]
  rw [image_reduced]
  rw [model_objects]
  simp [objects,maps,position,links,Telematics.Structural.config,Telematics.Structural.heads,Telematics.Structural.ownership]

theorem actual_c10 : c10.Holds (model 0 2 3) (.closed (atom 0)) := by
  have h := denotes_some _ _ _ _ global_dual (Set.finite_singleton _)
  simpa [Expr.Holds,c10] using h

theorem actual_c11 : c11.Holds (model 0 2 3) (.closed (atom 0)) := by
  have h := denotes_some _ _ _ _ global_extra (Set.finite_singleton _)
  simpa [Expr.Holds,c11] using h

theorem actual_c12 : c12.Holds (model 0 2 3) (.closed (atom 0)) := by
  have h := denotes_some _ _ _ _ global_large (Set.finite_singleton _)
  simpa [Expr.Holds,c12] using h

theorem display_values (e d : Int) :
    (dereference9 (head9 (.widenObjects inclusion11 (Expr.this : Expr (support 11) [] _)))).denote
      (model 11 e d) (.closed (atom 4)) = some {integers.encode d} := by
  simp only [dereference9,head9,Expr.denote,lift₂,Option.bind_some,Option.map_some,image_reduced]
  simp [objects,maps,position,links,Telematics.Structural.config,Telematics.Structural.heads,Telematics.Structural.ownership,
    Environment.closed,FormalCD.IntegerRealization.domain,integers,Set.ext_iff]

theorem server_version_values (e d : Int) :
    (dereference9 (head9 (.widenObjects inclusion10 (dereference12 (head12
      (Expr.this : Expr (support 11) [] _)))))).denote
      (model 11 e d) (.closed (atom 4)) = some {integers.encode e} := by
  simp only [dereference9,head9,dereference12,head12,Expr.denote,lift₂,
    Option.bind_some,Option.map_some,image_reduced]
  simp [objects,maps,position,links,Telematics.Structural.config,Telematics.Structural.heads,Telematics.Structural.ownership,
    Telematics.Structural.targets,Environment.closed,FormalCD.IntegerRealization.domain,
    integers,Set.ext_iff]

theorem actual_c02_value (e d : Int) :
    c02.denote (model 11 e d) (.closed (atom 4)) = some ⟨e ≤ d⟩ := by
  apply denotes_ge
  · simp only [version,denote_integerOf,display_values,Option.bind_some]
    exact congrArg (Option.map ULift.up) (integers.extract_encoded d)
  · simp only [version,denote_integerOf,server_version_values,Option.bind_some]
    exact congrArg (Option.map ULift.up) (integers.extract_encoded e)

theorem actual_c02_greater : c02.Holds (model 11 2 3) (.closed (atom 4)) := by
  simp [Expr.Holds,actual_c02_value]

theorem actual_c02_equal : c02.Holds (model 11 2 2) (.closed (atom 4)) := by
  simp [Expr.Holds,actual_c02_value]

theorem actual_c02_lower : ¬ c02.Holds (model 11 3 2) (.closed (atom 4)) := by
  simp [Expr.Holds,actual_c02_value]

end Clafer.Examples.Telematics.ExpressionExamples
