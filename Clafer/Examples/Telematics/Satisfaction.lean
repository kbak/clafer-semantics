module

public import Clafer.Examples.Telematics.Configuration
public import Clafer.Examples.Telematics.Definedness
public import Clafer.Constraints.DenotationInvariance

-- [proof->req~clafer-appendix-f-complete~1]

/-! # Satisfaction of all twelve telematics conjuncts

SoSyM Appendix 6 (PDF p.34).

The support environment below is derived from the same shared configuration
used for structural satisfaction. All numeric counts are on finite nonprimitive
heads. The primitive extent is the complete integer domain.
-/

@[expose] public section
namespace Clafer.Examples.Telematics.Meaning
open CategoryTheory DPGraph DPGraph.Predicates Constraints Telematics.Expressions

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def position : Fin 28 → Fin 28 :=
  ![0,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,1,2,3,4,5,6,7,8,9,10,11,12]

def objects (d : Fin 28) : Set U := config.head (position d)

def owner (i : Fin 34) : Fin 28 :=
  position ⟨(maps i).owner.value, by fin_cases i <;> decide⟩

def links (i : Fin 34) (x y : U) : Prop :=
  match (maps i).kind with
  | .inclusion => x = y
  | .head => config.contains (owner i) x y
  | .parent => config.contains (owner i) y x
  | .dereference => config.deref (owner i) x y
  | .target => False

def span (i : Fin 34) : Span (objects (maps i).source) (objects (maps i).target) :=
  .ofRelation (fun x y => links i x.val y.val)

def graphMap (c : Fin 28) : (support c).graph ⥤q semanticGraph U where
  obj := objects
  map := by
    rintro x y ⟨i,hs,ht⟩
    subst x; subst y
    exact span i

theorem inclusion_subset (i : Fin 34) (h : (maps i).kind = .inclusion) :
    objects (maps i).source ⊆ objects (maps i).target := by
  fin_cases i <;> try { cases h }
  all_goals intro x hx; cases x <;> simp_all [objects,maps,position,config,heads]
  all_goals aesop

def model (c : Fin 28) : IntegerBinding (support c) U where
  realization := integers
  model := graphMap c
  same_id := by
    intro x y h
    have he : x = y := Fin.ext (congrArg DeclId.value h)
    subst y; rfl
  inclusion := by
    intro i hi
    change Inclusion (span i)
    unfold span
    have he : (fun (x : objects (maps i).source) (y : objects (maps i).target) =>
        links i x.val y.val) = (fun x y => x.val = y.val) := by
      funext x y
      simp [links, show (maps i).kind = .inclusion from hi]
    rw [he]
    exact (Semantics.identity_inclusion_iff _ _).mpr (inclusion_subset i hi)
  integer_domain := by
    intro x hx
    have he : x = 27 := by simpa [support] using hx
    subst x
    exact integer_extent

@[simp] theorem model_objects (c : Fin 28) (x : Fin 28) :
    (model c).model.obj x = objects x := rfl

theorem image_reduced (c : Fin 28) (i : Fin 34) (S : Set U) :
    relationalImage S (ambientRelation ((model c).model.map ((support c).arrow i))) =
      {y | ∃ x, x ∈ S ∧ x ∈ objects (maps i).source ∧
        y ∈ objects (maps i).target ∧ links i x y} := by
  ext y
  constructor
  · rintro ⟨x,hx,⟨⟨a,b⟩,h⟩,hs,ht⟩
    change a.val = x at hs
    change b.val = y at ht
    exact ⟨x,hx,hs ▸ a.property,ht ▸ b.property,hs ▸ ht ▸ h⟩
  · rintro ⟨x,hx,ha,hb,h⟩
    exact ⟨x,hx,⟨(⟨x,ha⟩,⟨y,hb⟩),h⟩,rfl,rfl⟩

theorem nonprimitive (c : Fin 28) : Telematics.Definedness.FiniteStructural (model c) := by
  intro x hx
  apply nonprimitive_finite
  fin_cases x <;> simp_all [position]



theorem small_options_value (x : U) :
    (head3 (head2 Expr.this) : Expr (support 1) [] _).denote (model 1)
      (.closed (x)) = some ∅ := by
  simp only [head2,head3,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  simp [objects,maps,position,links,owner,config,heads,ownership,
    Environment.closed,Set.ext_iff,Sum.exists,Sum.forall]

theorem cache_value (x : U) :
    (head5 Expr.this : Expr (support 1) [] _).denote (model 1)
      (.closed (x)) = some ∅ := by
  simp only [head5,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  simp [objects,maps,position,links,owner,config,heads,ownership,
    Environment.closed,Set.ext_iff,Sum.forall]

theorem fixed_value (x : U) :
    (head7 (head6 (head5 Expr.this)) : Expr (support 1) [] _).denote (model 1)
      (.closed (x)) = some ∅ := by
  simp only [head5,head6,head7,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  simp [objects,maps,position,links,owner,config,heads,ownership,
    Environment.closed,Sum.exists]

theorem inherited_cache_value (x : U) :
    (inheritedCache : Expr (support 15) [] _).denote (model 15)
      (.closed (x)) = some ∅ := by
  simp only [inheritedCache,head5,head13,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  simp [objects,maps,position,links,owner,config,heads,ownership,
    Environment.closed,Set.ext_iff,Sum.exists,Sum.forall]

theorem displays1_value  :
    (displays1 : Expr (support 19) [] _).denote (model 19)
      (.closed (atom 30)) = some {atom 3, atom 4} := by
  simp only [displays1,head15,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  simp [objects,maps,position,links,owner,config,heads,ownership,
    Set.ext_iff,Sum.exists,Sum.forall]

theorem displays2_value  :
    (displays2 : Expr (support 19) [] _).denote (model 19)
      (.closed (atom 30)) = some {atom 5, atom 6} := by
  simp only [displays2,head15,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  simp [objects,maps,position,links,owner,config,heads,ownership,
    Set.ext_iff,Sum.exists,Sum.forall]

theorem extra_value  :
    (head23 Expr.this : Expr (support 19) [] _).denote (model 19)
      (.closed (atom 30)) = some {atom 33} := by
  simp only [head23,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  simp [objects,maps,position,links,owner,config,heads,ownership,
    Environment.closed,Set.ext_iff,Sum.forall]

theorem dual_value  :
    (head22 (head20 Expr.this) : Expr (support 19) [] _).denote (model 19)
      (.closed (atom 30)) = some {atom 32} := by
  simp only [head20,head22,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  simp [objects,maps,position,links,owner,config,heads,ownership,
    Environment.closed,Set.ext_iff,Sum.exists,Sum.forall]

theorem ecu2_value  :
    (Expr.extent 17 : Expr (support 19) [] _).denote (model 19)
      (.closed (atom 30)) = some {atom 2} := by
  simp only [Expr.denote]
  simp [objects,position,config,heads,ownership,
    Set.ext_iff,Sum.forall]

theorem large_local_value  :
    (head26 (head24 Expr.this) : Expr (support 19) [] _).denote (model 19)
      (.closed (atom 30)) = some {atom 35} := by
  simp only [head24,head26,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  simp [objects,maps,position,links,owner,config,heads,ownership,
    Environment.closed,Set.ext_iff,Sum.exists,Sum.forall]

theorem small_local_value  :
    (head25 (head24 Expr.this) : Expr (support 19) [] _).denote (model 19)
      (.closed (atom 30)) = some ∅ := by
  simp only [head24,head25,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  simp [objects,maps,position,links,owner,config,heads,ownership,
    Environment.closed,Set.ext_iff,Sum.exists,Sum.forall]

theorem all_small_value  :
    (head3 allSizes : Expr (support 19) [] _).denote (model 19)
      (.closed (atom 30)) = some ∅ := by
  simp only [allSizes,head3,head2,head13,head15,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  simp [objects,maps,position,links,owner,config,heads,ownership,
    Set.ext_iff,Sum.exists,Sum.forall]

theorem all_large_value  :
    (head4 allSizes : Expr (support 19) [] _).denote (model 19)
      (.closed (atom 30)) = some {atom 25, atom 26, atom 27, atom 28} := by
  simp only [allSizes,head4,head2,head13,head15,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  simp [objects,maps,position,links,owner,config,heads,ownership,
    Set.ext_iff,Sum.exists,Sum.forall]
  aesop

theorem global_dual_value  :
    (head22 (head20 (Expr.extent 19)) : Expr (support 0) [] _).denote (model 0)
      (.closed (atom 0)) = some {atom 32} := by
  simp only [head20,head22,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  simp [objects,maps,position,links,owner,config,heads,ownership,
    Set.ext_iff,Sum.exists,Sum.forall]

theorem global_extra_value  :
    (head23 (Expr.extent 19) : Expr (support 0) [] _).denote (model 0)
      (.closed (atom 0)) = some {atom 33} := by
  simp only [head23,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  simp [objects,maps,position,links,owner,config,heads,ownership,
    Set.ext_iff,Sum.exists,Sum.forall]

theorem global_large_value  :
    (head26 (head24 (Expr.extent 19)) : Expr (support 0) [] _).denote (model 0)
      (.closed (atom 0)) = some {atom 35} := by
  simp only [head24,head26,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  simp [objects,maps,position,links,owner,config,heads,ownership,
    Set.ext_iff,Sum.exists,Sum.forall]

theorem c01_all (x : U) : c01.Holds (model 1) (.closed x) := by
  have hs := denotes_some _ _ _ _ (small_options_value x) Set.finite_empty
  have hc := denotes_some _ _ _ _ (cache_value x) Set.finite_empty
  have hf := denotes_some _ _ _ _ (fixed_value x) Set.finite_empty
  simp [Expr.Holds,c01,Expr.implies,denote_and,denote_not,hs,hc,hf,lift₂]

theorem c03_all (x : U) : c03.Holds (model 15) (.closed x) := by
  unfold c03 Expr.Holds
  rw [denotes_no _ _ _ ∅ (inherited_cache_value x) Set.finite_empty]
  simp

theorem c05_holds : c05.Holds (model 19) (.closed (atom 30)) := by
  have hd := denotes_some _ _ _ _ dual_value (Set.finite_singleton _)
  have he := denotes_some _ _ _ _ ecu2_value (Set.finite_singleton _)
  simpa [Expr.Holds,c05] using denotes_iff _ _ _ _ _ _ hd he

theorem c06_holds : c06.Holds (model 19) (.closed (atom 30)) := by
  have he := denotes_some _ _ _ _ extra_value (Set.finite_singleton _)
  have hc : (exactlyTwo displays1).denote (model 19) (.closed (atom 30)) = some ⟨True⟩ := by
    simp [exactlyTwo,Expr.denote,displays1_value,lift₂,finiteCard]
  simpa [Expr.Holds,c06] using denotes_iff _ _ _ _ _ _ he hc

theorem c07_holds : c07.Holds (model 19) (.closed (atom 30)) := by
  have he := denotes_some _ _ _ _ extra_value (Set.finite_singleton _)
  have hp := denotes_some _ _ _ _ ecu2_value (Set.finite_singleton _)
  have hc : (exactlyTwo displays2).denote (model 19) (.closed (atom 30)) = some ⟨True⟩ := by
    simp [exactlyTwo,Expr.denote,displays2_value,lift₂,finiteCard]
  simpa [Expr.Holds,c07] using denotes_iff _ _ _ _ _ _ he (denotes_implies _ _ _ _ _ _ hp hc)

theorem c08_holds : c08.Holds (model 19) (.closed (atom 30)) := by
  have hl := denotes_some _ _ _ _ large_local_value (Set.finite_singleton _)
  have hs := denotes_some _ _ _ _ all_small_value Set.finite_empty
  have hn : (Expr.not (head3 allSizes).some).denote (model 19) (.closed (atom 30)) =
      some ⟨True⟩ := by simp only [denote_not,hs,Option.map_some]; simp
  simpa [Expr.Holds,c08] using denotes_iff _ _ _ _ _ _ hl hn

theorem c09_holds : c09.Holds (model 19) (.closed (atom 30)) := by
  have hs := denotes_some _ _ _ _ small_local_value Set.finite_empty
  have hl := denotes_some _ _ _ _ all_large_value (by simp)
  have hn : (Expr.not (head4 allSizes).some).denote (model 19) (.closed (atom 30)) =
      some ⟨False⟩ := by simp only [denote_not,hl,Option.map_some]; simp
  simpa [Expr.Holds,c09] using denotes_iff _ _ _ _ _ _ hs hn

theorem c10_holds : c10.Holds (model 0) (.closed (atom 0)) := by
  simpa [Expr.Holds,c10] using denotes_some _ _ _ _ global_dual_value (Set.finite_singleton _)
theorem c11_holds : c11.Holds (model 0) (.closed (atom 0)) := by
  simpa [Expr.Holds,c11] using denotes_some _ _ _ _ global_extra_value (Set.finite_singleton _)
theorem c12_holds : c12.Holds (model 0) (.closed (atom 0)) := by
  simpa [Expr.Holds,c12] using denotes_some _ _ _ _ global_large_value (Set.finite_singleton _)



theorem display_values (x : U) (hx : x ∈ objects 11) :
    (dereference9 (head9 (.widenObjects inclusion11 (Expr.this : Expr (support 11) [] _)))).denote
      (model 11) (.closed x) = some {integers.encode 3} := by
  cases x with
  | inr v => simp [objects,position,config] at hx
  | inl x =>
    simp [objects,position,config,heads] at hx
    rcases hx with rfl | rfl | rfl | rfl
    all_goals simp only [dereference9,head9,Expr.denote,lift₂,Option.bind_some,
      Option.map_some]
    all_goals repeat rw [image_reduced]
    all_goals simp [objects,maps,position,links,owner,config,heads,ownership,
      Environment.closed,integers,Set.ext_iff,Sum.exists,Sum.forall]

theorem server_version_values (x : U) (hx : x ∈ objects 11) :
    (dereference9 (head9 (.widenObjects inclusion10 (dereference12 (head12
      (Expr.this : Expr (support 11) [] _)))))).denote
      (model 11) (.closed x) = some {integers.encode 2} := by
  cases x with
  | inr v => simp [objects,position,config] at hx
  | inl x =>
    simp [objects,position,config,heads] at hx
    rcases hx with rfl | rfl | rfl | rfl
    all_goals simp only [dereference9,head9,dereference12,head12,Expr.denote,lift₂,
      Option.bind_some,Option.map_some]
    all_goals repeat rw [image_reduced]
    all_goals simp [objects,maps,position,links,owner,config,heads,ownership,targets,
      Environment.closed,integers,Set.ext_iff,Sum.exists,Sum.forall]

theorem c02_all (x : U) (hx : x ∈ objects 11) : c02.Holds (model 11) (.closed x) := by
  have hd : (version (.widenObjects inclusion11 Expr.this)).denote (model 11) (.closed x) =
      some ⟨3⟩ := by
    simp only [version,denote_integerOf,display_values x hx,Option.bind_some]
    exact congrArg (Option.map ULift.up) (integers.extract_encoded 3)
  have hs : (version (.widenObjects inclusion10 (dereference12 (head12 Expr.this)))).denote
      (model 11) (.closed x) = some ⟨2⟩ := by
    simp only [version,denote_integerOf,server_version_values x hx,Option.bind_some]
    exact congrArg (Option.map ULift.up) (integers.extract_encoded 2)
  simpa [Expr.Holds,c02] using denotes_ge _ _ _ _ _ _ hd hs

theorem c02_defined (x : Subtype (objects 11)) : c02.Defined (model 11) (.closed x.val) := by
  apply Telematics.Definedness.c02_defined
  · exact (config.head_multiplicity_iff core.toEffectiveCore typed 21 20 rfl).mpr
      (multiplicities 21 20 rfl)
  · exact (config.deref_one_iff core.toEffectiveCore typed 21 12 rfl).mpr
      (references_hold 21 12 rfl)
  · exact (config.head_multiplicity_iff core.toEffectiveCore typed 24 23 rfl).mpr
      (multiplicities 24 23 rfl)
  · exact (config.deref_one_iff core.toEffectiveCore typed 24 22 rfl).mpr
      (references_hold 24 22 rfl)

theorem c04_all (x : U) (hx : x ∈ objects 15) : c04.Holds (model 15) (.closed x) := by
  cases x with
  | inr v => simp [objects,position,config] at hx
  | inl x =>
    simp [objects,position,config,heads] at hx
    rcases hx with rfl | rfl | rfl | rfl
    all_goals simp only [Expr.Holds,c04,dereference12,head12,parent15,Expr.denote,lift₂,
      Option.bind_some,Option.map_some]
    all_goals repeat rw [image_reduced]
    all_goals simp [objects,maps,position,links,owner,config,heads,ownership,targets,
      Environment.closed,Set.ext_iff,Sum.exists,Sum.forall]

end Clafer.Examples.Telematics.Meaning
