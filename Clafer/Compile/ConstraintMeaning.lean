module

public import Clafer.Compile.Realization
public import Clafer.Constraints.Predicate

/-!
[impl->req~clafer-constraint-preservation~1]
[proof->req~clafer-constraint-preservation~1]
-/

/-!
# Resolved constraint meaning through Compile and gluing

SoSyM §6.2.2–5, B.4 Definition 10, B.5 and Appendix D.4.
Interpretation uses the actual generated support binding. Complete class and
map identities, including isolated/repeated occurrences, remain observable.
-/

@[expose] public section
namespace Clafer.Compile.ConstraintMeaning
open CategoryTheory MCS DPGraph DPGraph.Predicates Constraints

variable {a : AST} (i : Input a) {U : Type}

/-- Integer-domain realization and actual inclusion meanings are admissibility
conditions, independent of truth of authored bodies. Inclusion conditions can
be discharged from the generated local declaration bank. -/
structure Admissible (R : IntegerRealization U)
    (m : (roles i).graph ⥤q semanticGraph U) : Prop where
  inclusions : ∀ s : (family i).InclusionSlot,
    Inclusion (m.map ((roles i).inclusion s))
  integers : ∀ c, (a.at c).declaration.origin = .primitive .int → m.obj c = R.domain

theorem vertex_same_id (q : ConstraintId a) (v w : (support i q).Vertex)
    (h : (support i q).classId v = (support i q).classId w) :
    vertex i q v = vertex i q w :=
  sourceId_injective i.ast ((vertex_id i q v).trans (h.trans (vertex_id i q w).symm))

theorem mapOwner_same_id (q : ConstraintId a) (e f : (support i q).Edge)
    (h : ((support i q).mapRef e).owner = ((support i q).mapRef f).owner) :
    mapOwner i q e = mapOwner i q f := by
  apply sourceId_injective i.ast
  exact (resolve_id _ _).trans (h.trans (resolve_id _ _).symm)

private theorem ordinary_id_eq {C : Type} {f : Family C} {c d : C}
    (h : c = d) (r : Clafer.Roles.MapRole)
    (hp : Clafer.Roles.mapPresent (f.shape c).kind (f.shape c).hasParent r = true)
    (hq : Clafer.Roles.mapPresent (f.shape d).kind (f.shape d).hasParent r = true) :
    Family.MapId.ordinary c ⟨r, hp⟩ = Family.MapId.ordinary d ⟨r, hq⟩ := by
  subst d
  rfl

private theorem inclusion_id_eq {C : Type} {f : Family C} {c d s t : C}
    (h : c = d) (ht : s = t) (hp : f.super c = some s) (hq : f.super d = some t) :
    Family.MapId.inclusion ⟨c, s, Shape.headInclusion _ _, hp⟩ =
      Family.MapId.inclusion ⟨d, t, Shape.headInclusion _ _, hq⟩ := by
  subst d
  subst t
  rfl

private def ordinaryKind : Clafer.Roles.MapRole → MapKind
  | .head => .head | .parent => .parent | .dereference => .dereference | .target => .target

private theorem boundArrow_ordinary (q : ConstraintId a) (e : (support i q).Edge)
    (r : Clafer.Roles.MapRole) (h : ((support i q).mapRef e).kind = ordinaryKind r) :
    ∃ hp, (boundArrow i q e).val = Family.MapId.ordinary (mapOwner i q e) ⟨r, hp⟩ := by
  cases r <;> unfold boundArrow <;> split <;> try exact ⟨_, rfl⟩
  all_goals rename_i hk; cases h.symm.trans hk

private theorem boundArrow_inclusion (q : ConstraintId a) (e : (support i q).Edge)
    (h : ((support i q).mapRef e).kind = .inclusion) :
    ∃ hs, (boundArrow i q e).val = Family.MapId.inclusion
      ⟨mapOwner i q e, vertex i q ((support i q).mapRef e).target,
        Shape.headInclusion _ _, hs⟩ := by
  unfold boundArrow
  split <;> try exact ⟨_, rfl⟩
  all_goals rename_i hk; cases h.symm.trans hk

/-- Repeated occurrences resolve to the very same allocated map, independently
of their display labels and occurrence positions. -/
theorem boundArrow_same_id (q : ConstraintId a) (e f : (support i q).Edge)
    (ho : ((support i q).mapRef e).owner = ((support i q).mapRef f).owner)
    (hk : ((support i q).mapRef e).kind = ((support i q).mapRef f).kind) :
    (boundArrow i q e).val = (boundArrow i q f).val := by
  have hm := mapOwner_same_id i q e f ho
  have target_eq (he : ((support i q).mapRef e).kind = .inclusion) :
      vertex i q ((support i q).mapRef e).target =
        vertex i q ((support i q).mapRef f).target := by
    have hs := map_spec i q e
    have ht := map_spec i q f
    simp only [he] at hs
    simp only [← hk, he, ← hm] at ht
    exact vertex_same_id i q _ _ (Option.some.inj (hs.2.symm.trans ht.2))
  have ordinary (r : Clafer.Roles.MapRole)
      (he : ((support i q).mapRef e).kind = ordinaryKind r) :
      (boundArrow i q e).val = (boundArrow i q f).val := by
    obtain ⟨hp, heq⟩ := boundArrow_ordinary i q e r he
    obtain ⟨hp', hfq⟩ := boundArrow_ordinary i q f r (hk.symm.trans he)
    rw [heq, hfq]
    exact ordinary_id_eq hm r hp hp'
  cases he : ((support i q).mapRef e).kind with
  | head => exact ordinary .head he
  | parent => exact ordinary .parent he
  | dereference => exact ordinary .dereference he
  | target => exact ordinary .target he
  | inclusion =>
    obtain ⟨hs, heq⟩ := boundArrow_inclusion i q e he
    obtain ⟨hs', hfq⟩ := boundArrow_inclusion i q f (hk.symm.trans he)
    rw [heq, hfq]
    have ht := target_eq he
    exact inclusion_id_eq hm ht hs hs'

/-- A support occurrence's integer annotation resolves to an actual primitive
declaration, rather than a class whose name happens to be int. -/
theorem vertex_integer (q : ConstraintId a) (v : (support i q).Vertex)
    (h : (support i q).integer v = true) :
    (a.at (vertex i q v)).declaration.origin = .primitive .int := by
  obtain ⟨d, hd, hi, ho⟩ := (i.typed q).resolved.integers v h
  have he := entry_unique i.ast (List.getElem_mem _) hd
    ((vertex_id i q v).trans hi.symm)
  exact (congrArg (fun t : Located => t.declaration.origin) he).trans ho

theorem inclusion_of_identity (R : IntegerRealization U)
    (m : (roles i).graph ⥤q semanticGraph U) (h : Admissible i R m)
    {x y} (e : (roles i).Arrow x y)
    (hi : ∃ s, e.val = Family.MapId.inclusion s) : Inclusion (m.map e) := by
  rcases e with ⟨e, rfl, rfl⟩
  obtain ⟨s, rfl⟩ := hi
  exact h.inclusions s

/-- Equality of allocated maps retains a bijection of original links and both
ambient endpoints, even when support endpoint occurrences differ. -/
theorem links_of_identity (m : (roles i).graph ⥤q semanticGraph U)
    {x y x' y'} (e : (roles i).Arrow x y) (f : (roles i).Arrow x' y')
    (he : e.val = f.val) : Nonempty (LinkEquivalence (m.map e) (m.map f)) := by
  rcases e with ⟨e, rfl, rfl⟩
  rcases f with ⟨f, rfl, rfl⟩
  cases he
  exact ⟨⟨Equiv.refl _, fun _ => rfl, fun _ => rfl⟩⟩

noncomputable def supportModel (R : IntegerRealization U)
    (m : (roles i).graph ⥤q semanticGraph U) (h : Admissible i R m)
    (q : ConstraintId a) : IntegerBinding (support i q) U where
  realization := R
  model := (binding i q).comp m
  same_id v w hv := congrArg m.obj (vertex_same_id i q v w hv)
  inclusion e he := by
    apply inclusion_of_identity i R m h
    refine ⟨⟨mapOwner i q e, vertex i q ((support i q).mapRef e).target,
      Shape.headInclusion _ _, (super_eq i _ _).mpr (by
        have hs := map_spec i q e
        simp only [he] at hs
        simpa only [vertex_id] using hs.2)⟩, ?_⟩
    change (boundArrow i q e).val = _
    unfold boundArrow
    split
    next hh => cases he.symm.trans hh
    next hh => cases he.symm.trans hh
    next hh => cases he.symm.trans hh
    next hh => cases he.symm.trans hh
    next _ => rfl
  integer_domain v hv := h.integers _ (vertex_integer i q v hv)

/-- Arity binding is equality of the entire graph map, not its bag of arrows. -/
theorem arity_binding (R : IntegerRealization U)
    (m : (roles i).graph ⥤q semanticGraph U) (h : Admissible i R m)
    (q : ConstraintId a) :
    (supportModel i R m h q).model = (binding i q).comp m := rfl

theorem context_binding (R : IntegerRealization U)
    (m : (roles i).graph ⥤q semanticGraph U) (h : Admissible i R m)
    (q : ConstraintId a) :
    (supportModel i R m h q).model.obj (support i q).context = m.obj q.1 :=
  congrArg m.obj (binding_context i q)

theorem support_coherent (R : IntegerRealization U)
    (m : (roles i).graph ⥤q semanticGraph U) (h : Admissible i R m)
    (q : ConstraintId a) : (supportModel i R m h q).Coherent := by
  intro e f ho hk
  exact links_of_identity i m _ _ (boundArrow_same_id i q e f ho hk)

variable (domains : ∀ q, Domains (i.constraint q).support (i.constraint q).locals)

noncomputable def authored (R : IntegerRealization U) :=
  predicateInterpretation i.constraint domains R

/-- The canonical meaning of the existing Compile vocabulary. Callers supply
typed domain expressions and a primitive realization, never predicate truth. -/
noncomputable def interpretation (R : IntegerRealization U) :
    Interpretation (vocabulary i).signature (semanticGraph U) where
  meaning
    | .inl p => (DPGraph.Predicates.interpretation U).meaning p
    | .inr q => (authored i domains R).meaning q

theorem constraint_iff (R : IntegerRealization U)
    (m : (roles i).graph ⥤q semanticGraph U) (h : Admissible i R m)
    (q : ConstraintId a) :
    (interpretation i domains R).Satisfies m (formula i (.inr q)) ↔
      (i.constraint q).Holds (domains q) (supportModel i R m h q) :=
  predicate_meaning_iff i.constraint domains R q _ rfl (support_coherent i R m h q)

/-- Local generation discharges the inclusion part of admissibility. Primitive
realization remains explicit: structural names do not identify a value domain. -/
theorem admissible_of_local (R : IntegerRealization U)
    (m : (roles i).graph ⥤q semanticGraph U)
    (hm : (DPGraph.Predicates.interpretation U).IsModel
      (localFormulas (family i)).diagram m)
    (hi : ∀ c, (a.at c).declaration.origin = .primitive .int → m.obj c = R.domain) :
    Admissible i R m :=
  ⟨fun s => hm _ ⟨.inclusion s, rfl⟩, hi⟩

/-- Formula-level equivalence uses the actual label and complete binding. The
candidate on the right is precisely the reduct of this target candidate. -/
theorem glued_constraint_iff (R : IntegerRealization U)
    (m : (Realization.glued i).carrier ⥤q semanticGraph U)
    (h : Admissible i R ((groupLabel i).comp m)) (q : ConstraintId a) :
    (Realization.interpretation i U (authored i domains R)).Satisfies m
      ((Realization.promote i (Compile.promote i (formula i (.inr q)))).translate
        (groupLabel i)) ↔
      (i.constraint q).Holds (domains q)
        (supportModel i R ((groupLabel i).comp m) h q) := by
  erw [Interpretation.satisfies_translate]
  exact constraint_iff i domains R _ h q

/-- The occurrence is in the exact generated/glued image, with both promotion
steps retaining its complete support binding. -/
theorem glued_constraint_declared (q : ConstraintId a) :
    (Realization.promote i (Compile.promote i (formula i (.inr q)))).translate
      (groupLabel i) ∈ (Realization.glued i).declarations :=
  ⟨.inl (.inl (.inr q)), rfl⟩

def SourceHolds (R : IntegerRealization U)
    (m : (roles i).graph ⥤q semanticGraph U) (h : Admissible i R m) : Prop :=
  ∀ q, (i.constraint q).Holds (domains q) (supportModel i R m h q)

/-- Exhausting the generated sum of local and source occurrences proves
completeness in both directions; no coverage premise is supplied by the caller. -/
theorem compiled_model_iff (R : IntegerRealization U)
    (m : (roles i).graph ⥤q semanticGraph U) (h : Admissible i R m) :
    (interpretation i domains R).IsModel (compile i).formulas.diagram m ↔
      (DPGraph.Predicates.interpretation U).IsModel (localFormulas (family i)).diagram m ∧
      SourceHolds i domains R m h := by
  constructor
  · intro hm
    refine ⟨?_, ?_⟩
    · rintro φ ⟨l, rfl⟩
      exact hm _ ⟨.inl l, rfl⟩
    · intro q
      exact (constraint_iff i domains R m h q).mp (hm _ ⟨.inr q, rfl⟩)
  · rintro ⟨hl, hs⟩ φ ⟨l | q, rfl⟩
    · exact hl _ ⟨l, rfl⟩
    · exact (constraint_iff i domains R m h q).mpr (hs q)

theorem authored_iff (R : IntegerRealization U)
    (s : Semantics.Configuration a.Occurrence U)
    (h : Admissible i R (s.interpret (Semantics.EffectiveCore.erase i))) :
    Realization.AuthoredHolds i (authored i domains R) s ↔
      SourceHolds i domains R (s.interpret (Semantics.EffectiveCore.erase i)) h := by
  apply forall_congr'
  intro q
  exact constraint_iff i domains R _ h q

/-- Selected whole-model correspondence. The target candidate is the canonical
descent of a shared-object configuration; root/typing and primitive realization
remain explicit. Local/group/inheritance/abstract formulas and their complete
declaration images are generated by Compile, not assumed as a bridge.

Both directions concern this exact bank and interpretation. They do not assert
reflection along arbitrary DP morphisms or correctness of textual elaboration. -/
theorem whole_model (R : IntegerRealization U)
    (selected : (Semantics.Realization.Core.ofInput i).Selected)
    (s : Semantics.Configuration a.Occurrence U)
    (h : Admissible i R (s.interpret (Semantics.EffectiveCore.erase i))) :
    (s.Typed (Semantics.EffectiveCore.erase i) ∧ s.Rooted (Semantics.EffectiveCore.erase i) ∧
      s.DeclarationDisjoint (Semantics.EffectiveCore.erase i) ∧
      (Realization.interpretation i U (authored i domains R)).IsModel
        (Realization.glued i).toDPGraph (Realization.descend i s)) ↔
    (Semantics.Realization.Satisfies (Semantics.Realization.Core.ofInput i) s ∧
      SourceHolds i domains R (s.interpret (Semantics.EffectiveCore.erase i)) h) := by
  rw [Realization.whole_model i (authored i domains R) selected s,
    authored_iff i domains R s h]

end Clafer.Compile.ConstraintMeaning
