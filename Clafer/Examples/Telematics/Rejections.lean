module

public import Clafer.Examples.Telematics.Compiled
public import Clafer.Examples.Telematics.Mutations

/-!
[impl->req~clafer-appendix-f-rejections~1]
[proof->req~clafer-appendix-f-rejections~1]
-/

/-!
# Focused rejection obligations of the complete telematics input

SoSyM Appendix 6 (PDF p.34).

These arity witnesses exercise the actual attached source symbols. They need
not satisfy unrelated structural or source obligations. Rejection transports
to the actual generated formula whenever its full arity reduct is this witness.
-/

@[expose] public section
namespace Clafer.Examples.Telematics.Rejections
open CategoryTheory MCS Compile DPGraph DPGraph.Predicates Constraints
open Telematics.Expressions

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- A failed applicable body rejects the exact attached source symbol. -/
theorem symbol_rejected {V : Type} (q : ConstraintId ast)
    (m : IntegerBinding (input.constraint q).support V) (hc : m.Coherent)
    (x : V) (hx : (m.model.obj (input.constraint q).support.context : Set V) x)
    (hf : ¬ ((domains q).close (input.constraint q).body).Holds m (.closed x)) :
    ¬ m.model ∈ (ConstraintMeaning.authored input domains m.realization).meaning q := by
  erw [predicate_meaning_iff input.constraint domains m.realization q m rfl hc]
  intro h
  exact hf (h x hx)

/-- This symbol is precisely the one in Compile's emitted full binding.
Matching a complete arity reduct is sufficient; a bag of arrow names is not. -/
theorem generated_rejected {V : Type} (q : ConstraintId ast)
    (m : IntegerBinding (input.constraint q).support V)
    (hf : ¬ m.model ∈ (ConstraintMeaning.authored input domains m.realization).meaning q)
    (candidate : (roles input).graph ⥤q semanticGraph V)
    (he : (binding input q).comp candidate = m.model) :
    ¬ (ConstraintMeaning.interpretation input domains m.realization).Satisfies candidate
      (formula input (.inr q)) := by
  change ¬ (binding input q).comp candidate ∈
    (ConstraintMeaning.authored input domains m.realization).meaning q
  rw [he]
  exact hf

theorem wrong_display_count :
    ¬ (Telematics.ExpressionEnvironment.model 19 2 3).model ∈
      (ConstraintMeaning.authored input domains Telematics.ExpressionEnvironment.integers).meaning (occurrence 5) := by
  apply symbol_rejected (occurrence 5) _ (Telematics.ExpressionEnvironment.model_coherent _ _ _)
    (Telematics.ExpressionEnvironment.atom 19)
  · change Telematics.ExpressionEnvironment.atom 19 ∈ Telematics.ExpressionEnvironment.objects 19
    simp [Telematics.ExpressionEnvironment.objects,Telematics.ExpressionEnvironment.position,Telematics.Structural.config,Telematics.Structural.heads]
  · exact Telematics.ExpressionExamples.actual_c06_rejects_one_display

theorem wrong_server_parent :
    ¬ (Telematics.Mutations.movedModel 15).model ∈
      (ConstraintMeaning.authored input domains Telematics.ExpressionEnvironment.integers).meaning (occurrence 3) := by
  apply symbol_rejected (occurrence 3) _ (Telematics.Mutations.moved_coherent _)
    (Telematics.ExpressionEnvironment.atom 5)
  · change Telematics.ExpressionEnvironment.atom 5 ∈ Telematics.ExpressionEnvironment.objects 15
    simp [Telematics.ExpressionEnvironment.objects,Telematics.ExpressionEnvironment.position,Telematics.Structural.config,Telematics.Structural.heads]
  · exact Telematics.Mutations.c04_rejects_wrong_owner

theorem lower_display_version :
    ¬ (Telematics.ExpressionEnvironment.model 11 3 2).model ∈
      (ConstraintMeaning.authored input domains Telematics.ExpressionEnvironment.integers).meaning (occurrence 1) := by
  apply symbol_rejected (occurrence 1) _ (Telematics.ExpressionEnvironment.model_coherent _ _ _)
    (Telematics.ExpressionEnvironment.atom 4)
  · change Telematics.ExpressionEnvironment.atom 4 ∈ Telematics.ExpressionEnvironment.objects 11
    simp [Telematics.ExpressionEnvironment.objects,Telematics.ExpressionEnvironment.position,Telematics.Structural.config,Telematics.Structural.heads]
  · exact Telematics.ExpressionExamples.actual_c02_lower



namespace Probe

abbrev V := Sum Unit Int
abbrev a : V := Sum.inl ()

def integers : IntegerRealization V where
  encode := ⟨Sum.inr,Sum.inr_injective⟩
  decode | .inl _ => 0 | .inr i => i
  decode_encode _ := rfl

def objects (d : Fin 28) : Set V := if d = 27 then integers.domain else {a}

def links (missing : Option (Fin 34)) (i : Fin 34) (x y : V) : Prop :=
  if (maps i).kind = .inclusion then x = y
  else missing ≠ some i ∧ x = a ∧ y = a

def span (missing : Option (Fin 34)) (i : Fin 34) :
    Span (objects (maps i).source) (objects (maps i).target) :=
  .ofRelation (fun x y => links missing i x.val y.val)

def graph (c : Fin 28) (missing : Option (Fin 34)) : (support c).graph ⥤q semanticGraph V where
  obj := objects
  map := by
    rintro x y ⟨i,hs,ht⟩
    subst x; subst y
    exact span missing i

def model (c : Fin 28) (missing : Option (Fin 34)) : IntegerBinding (support c) V where
  realization := integers
  model := graph c missing
  same_id := by
    intro x y h
    have he : x = y := Fin.ext (congrArg DeclId.value h)
    subst y; rfl
  inclusion := by
    intro i hi
    change Inclusion (span missing i)
    unfold span
    have he : (fun (x : objects (maps i).source) (y : objects (maps i).target) =>
        links missing i x.val y.val) = (fun x y => x.val = y.val) := by
      funext x y
      simp [links,show (maps i).kind = .inclusion from hi]
    rw [he]
    apply (Semantics.identity_inclusion_iff _ _).mpr
    fin_cases i <;> try { cases hi }
    all_goals simp [objects,maps]
  integer_domain := by
    intro x hx
    have he : x = 27 := by simpa [Telematics.Expressions.support] using hx
    subst x; simp [graph,objects]

theorem coherent (c : Fin 28) (missing : Option (Fin 34)) : (model c missing).Coherent := by
  intro i j ho hk
  have he := Telematics.ExpressionEnvironment.map_identity_unique i j ho hk
  subst j
  exact ⟨⟨Equiv.refl _,fun _ => rfl,fun _ => rfl⟩⟩

theorem image_reduced (c : Fin 28) (missing : Option (Fin 34)) (i : Fin 34) (S : Set V) :
    relationalImage S (ambientRelation ((model c missing).model.map ((support c).arrow i))) =
      {y | ∃ x, x ∈ S ∧ x ∈ objects (maps i).source ∧
        y ∈ objects (maps i).target ∧ links missing i x y} := by
  ext y
  constructor
  · rintro ⟨x,hx,⟨⟨b,d⟩,h⟩,hs,ht⟩
    change b.val = x at hs
    change d.val = y at ht
    exact ⟨x,hx,hs ▸ b.property,ht ▸ d.property,hs ▸ ht ▸ h⟩
  · rintro ⟨x,hx,ha,hb,h⟩
    exact ⟨x,hx,⟨(⟨x,ha⟩,⟨y,hb⟩),h⟩,rfl,rfl⟩

/-- All navigation collections here are finite singletons or empty. The probe
is intentionally not claimed to satisfy the complete structural bank. -/
theorem forbidden_cache : ¬ c03.Holds (model 15 none) (.closed a) := by
  simp only [c03,inheritedCache,head5,head13,Expr.no,Expr.Holds,Expr.denote,lift₂,
    Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  simp [objects,maps,links,Environment.closed,finiteCard]

theorem c01_requires_fixed : ¬ c01.Holds (model 1 (some 5)) (.closed a) := by
  simp only [c01,head2,head3,head5,head6,head7,Expr.some,Expr.implies,
    Expr.Holds,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  simp [objects,maps,links,Environment.closed,finiteCard]

theorem c05_requires_equivalence : ¬ c05.Holds (model 19 (some 16)) (.closed a) := by
  simp only [c05,head20,head22,Expr.some,Expr.iff,Expr.implies,
    Expr.Holds,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  change _ = _ → False
  simp [model,graph,objects,maps,links,Environment.closed,finiteCard]

theorem c08_rejects_small_options : ¬ c08.Holds (model 19 none) (.closed a) := by
  simp only [c08,allSizes,head26,head24,head3,head2,head13,head15,Expr.some,
    Expr.iff,Expr.implies,Expr.Holds,Expr.denote,lift₂,
    Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  simp [model,graph,objects,maps,links,Environment.closed,finiteCard]

theorem c09_rejects_large_options : ¬ c09.Holds (model 19 none) (.closed a) := by
  simp only [c09,allSizes,head25,head24,head4,head2,head13,head15,Expr.some,
    Expr.iff,Expr.implies,Expr.Holds,Expr.denote,lift₂,
    Option.bind_some,Option.map_some]
  repeat rw [image_reduced]
  simp [model,graph,objects,maps,links,Environment.closed,finiteCard]

end Probe

theorem forbidden_cache : ¬ (Probe.model 15 none).model ∈
    (ConstraintMeaning.authored input domains Probe.integers).meaning (occurrence 2) := by
  apply symbol_rejected (occurrence 2) _ (Probe.coherent _ _) Probe.a
  · change Probe.a ∈ Probe.objects 15
    simp [Probe.objects]
  · exact Probe.forbidden_cache

theorem missing_fixed : ¬ (Probe.model 1 (some 5)).model ∈
    (ConstraintMeaning.authored input domains Probe.integers).meaning (occurrence 0) := by
  apply symbol_rejected (occurrence 0) _ (Probe.coherent _ _) Probe.a
  · change Probe.a ∈ Probe.objects 1
    simp [Probe.objects]
  · exact Probe.c01_requires_fixed

theorem missing_dual : ¬ (Probe.model 19 (some 16)).model ∈
    (ConstraintMeaning.authored input domains Probe.integers).meaning (occurrence 4) := by
  apply symbol_rejected (occurrence 4) _ (Probe.coherent _ _) Probe.a
  · change Probe.a ∈ Probe.objects 19
    simp [Probe.objects]
  · exact Probe.c05_requires_equivalence

theorem conflicting_small_options : ¬ (Probe.model 19 none).model ∈
    (ConstraintMeaning.authored input domains Probe.integers).meaning (occurrence 7) := by
  apply symbol_rejected (occurrence 7) _ (Probe.coherent _ _) Probe.a
  · change Probe.a ∈ Probe.objects 19
    simp [Probe.objects]
  · exact Probe.c08_rejects_small_options

theorem conflicting_large_options : ¬ (Probe.model 19 none).model ∈
    (ConstraintMeaning.authored input domains Probe.integers).meaning (occurrence 8) := by
  apply symbol_rejected (occurrence 8) _ (Probe.coherent _ _) Probe.a
  · change Probe.a ∈ Probe.objects 19
    simp [Probe.objects]
  · exact Probe.c09_rejects_large_options



/-- A small typed candidate for the actual full model's channel group. Other
obligations may fail; this is a focused zero/one/two group boundary witness. -/
def xorConfig (k : Fin 3) : Semantics.Configuration (Fin 28) (Fin 3) where
  root := 0
  head d x := (d = 5 ∧ x = 0) ∨ (d = 6 ∧ x = 1 ∧ 1 ≤ k.val) ∨
    (d = 7 ∧ x = 2 ∧ k.val = 2)
  contains d x y := (d = 6 ∧ x = 0 ∧ y = 1 ∧ 1 ≤ k.val) ∨
    (d = 7 ∧ x = 0 ∧ y = 2 ∧ k.val = 2)
  deref _ _ _ := False

theorem xor_typed (k : Fin 3) : (xorConfig k).Typed core.toEffectiveCore := by
  constructor
  · intro d x y h
    rcases h with ⟨rfl,rfl,rfl,hk⟩ | ⟨rfl,rfl,rfl,hk⟩
    · exact ⟨Or.inr (Or.inl ⟨rfl,rfl,hk⟩),5,rfl,Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨Or.inr (Or.inr ⟨rfl,rfl,hk⟩),5,rfl,Or.inl ⟨rfl,rfl⟩⟩
  · intro _ _ _ h; exact h.elim

instance xorHeadDecidable (k : Fin 3) (d : Fin 28) :
    DecidablePred (fun x => x ∈ (xorConfig k).head d) := by
  intro x
  change Decidable ((d = 5 ∧ x = 0) ∨ (d = 6 ∧ x = 1 ∧ 1 ≤ k.val) ∨
    (d = 7 ∧ x = 2 ∧ k.val = 2))
  infer_instance

instance xorContainsDecidable (k : Fin 3) (d : Fin 28) (x y : Fin 3) :
    Decidable ((xorConfig k).contains d x y) := by
  change Decidable ((d = 6 ∧ x = 0 ∧ y = 1 ∧ 1 ≤ k.val) ∨
    (d = 7 ∧ x = 0 ∧ y = 2 ∧ k.val = 2))
  infer_instance

instance xorChildDecidable (k : Fin 3) (d : Fin 28) (x y : Fin 3) :
    Decidable (Groups.ChildObjects core.family (xorConfig k) d x y) :=
  decidable_of_iff
    (∃ a, a ∈ Telematics.Structural.ancestorTable d ∧ ∃ c,
      Telematics.Structural.parents c = some a ∧ (xorConfig k).contains c x y)
    (by simp only [Groups.ChildObjects,ancestor_iff,parents_eq])

noncomputable def channelGroup : Groups.Id (family input) := ⟨5,rfl⟩

theorem xor_counts (k : Fin 3) : Groups.Holds (family input) (xorConfig k) 5 ↔ k = 1 := by
  change (∀ x : (xorConfig k).head 5,
    InRange one {y : Fin 3 // Groups.ChildObjects core.family (xorConfig k) 5 x.val y}) ↔ _
  simp only [DPGraph.Predicates.inRange_card]
  fin_cases k <;> decide

theorem xor_generated_rejected (k : Fin 3) (hk : k ≠ 1)
    (authored : Interpretation (Constraints.signature input.constraint) (semanticGraph (Fin 3))) :
    ¬ (Compile.Realization.interpretation input (Fin 3) authored).Satisfies
      ((xorConfig k).interpret core.toEffectiveCore)
      (Compile.Realization.promote input (generatedGroup input channelGroup)) := by
  change ¬ (groupInterpretation input (Fin 3) authored).Satisfies
    ((xorConfig k).interpret core.toEffectiveCore) (generatedGroup input channelGroup)
  erw [generated_group_iff input authored _ (xor_typed k)]
  exact fun h => hk ((xor_counts k).mp h)

theorem xor_glued_rejected (k : Fin 3) (hk : k ≠ 1)
    (authored : Interpretation (Constraints.signature input.constraint) (semanticGraph (Fin 3))) :
    ¬ (Compile.Realization.interpretation input (Fin 3) authored).Satisfies
      (Compile.Realization.descend input (xorConfig k))
      ((Compile.Realization.promote input (generatedGroup input channelGroup)).translate (groupLabel input)) := by
  erw [Interpretation.satisfies_translate, Compile.Realization.descend_reduct]
  exact xor_generated_rejected k hk authored

theorem xor_declared :
    (Compile.Realization.promote input (generatedGroup input channelGroup)).translate
      (groupLabel input) ∈ (Compile.Realization.glued input).declarations :=
  ⟨.inl (.inr channelGroup),rfl⟩



theorem c07_wrong_display_count :
    ¬ (Telematics.ExpressionEnvironment.model 19 2 3).model ∈
      (ConstraintMeaning.authored input domains Telematics.ExpressionEnvironment.integers).meaning (occurrence 6) := by
  apply symbol_rejected (occurrence 6) _ (Telematics.ExpressionEnvironment.model_coherent _ _ _)
    (Telematics.ExpressionEnvironment.atom 19)
  · change Telematics.ExpressionEnvironment.atom 19 ∈ Telematics.ExpressionEnvironment.objects 19
    simp [Telematics.ExpressionEnvironment.objects,Telematics.ExpressionEnvironment.position,Telematics.Structural.config,Telematics.Structural.heads]
  · exact Telematics.ExpressionExamples.actual_c07_rejects_one_display

theorem c07_vacuity {V : Type} (m : IntegerBinding (support 19) V)
    (ρ : Environment (support 19) V []) (absent : (m.model.obj (17 : Fin 28) : Set V) = (∅ : Set V)) :
    ((domains (occurrence 6)).close (input.constraint (occurrence 6)).body).denote m ρ =
      (head23 Expr.this).some.denote m ρ :=
  Telematics.Definedness.c07_vacuity m ρ absent

end Clafer.Examples.Telematics.Rejections
