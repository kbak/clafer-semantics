module

public import FormalCD.Metamodel.Realization.Context

/-! # The exact restricted realization theorem
SoSyM Figure 21c: total args and the literal bag key are independent restrictions.
All other declarations follow from the canonical encoding and source metadata.
-/

@[expose] public section

universe p s va ua v u z z' w
namespace FormalCD.Metamodel.Realization
open CategoryTheory DPGraph DPGraph.Predicates

/-- A singleton-valued output bag compares its unique target. -/
theorem function_bag {A : Type z} {B : Type z'} (f : A → B) (a b : A) :
    Nonempty (BagEquiv (Span.ofFunction f) a b) ↔ f a = f b := by
  constructor
  · rintro ⟨h⟩
    have ht := h.target_eq ⟨a, rfl⟩
    have hs := (h.equiv ⟨a, rfl⟩).property
    change (h.equiv ⟨a, rfl⟩).val = b at hs
    change f (h.equiv ⟨a, rfl⟩).val = f a at ht
    exact ht.symm.trans (congrArg f hs)
  · intro h
    refine ⟨⟨?_, ?_⟩⟩
    · exact
        { toFun := fun _ => ⟨b, rfl⟩
          invFun := fun _ => ⟨a, rfl⟩
          left_inv := fun l => Subtype.ext l.property.symm
          right_inv := fun l => Subtype.ext l.property.symm }
    · intro l
      change f b = f l.val
      exact h.symm.trans (congrArg f l.property).symm

/-- B.1 occurrence equivalence, without finiteness or deduplication. -/
theorem family_bag {A : Type z} {B : Type z'} (F : IndexedFamily.{z,z',w} A B) (a b : A) :
    Nonempty (BagEquiv F.toSpan a b) ↔
      ∃ e : F.Index a ≃ F.Index b, ∀ i, F.eval a i = F.eval b (e i) := by
  let E := F.spanFamilyEquivalence
  constructor
  · rintro ⟨h⟩
    refine ⟨(E.equiv a).symm.trans (h.equiv.trans (E.equiv b)), fun i => ?_⟩
    change F.eval a i = F.eval b (E.equiv b (h.equiv ((E.equiv a).symm i)))
    rw [E.eval_eq]
    change F.eval a i = F.toSpan.target (h.equiv ((E.equiv a).symm i)).val
    rw [h.target_eq]
    exact (congrArg (F.eval a) ((E.equiv a).apply_symm_apply i)).symm.trans
      (E.eval_eq a ((E.equiv a).symm i))
  · rintro ⟨e, he⟩
    refine ⟨⟨(E.equiv a).trans (e.trans (E.equiv b).symm), fun l => ?_⟩⟩
    change F.toSpan.toFamily.eval b ((E.equiv b).symm (e (E.equiv a l))) = _
    rw [← E.eval_eq, Equiv.apply_symm_apply, ← he, E.eval_eq]
    rfl

variable {V : Vocabulary.{s,va,ua}} {R : Registry.{p}}
variable (D : CDOver.{s,va,ua,p,v,u} V R)

theorem total_args_iff : Total ((encode D).map Edge.args) ↔ Supported D := by
  change Total (arguments D).toSpan ↔ _
  rw [total_fibers]
  constructor
  · intro h f
    have hf := (h (formulas D f)).map (argumentIndex D (formulas D f))
    simpa only [Equiv.symm_apply_apply] using hf
  · intro h f
    exact (h ((formulas D).symm f)).map (argumentIndex D f).symm

theorem args_bags (f g : extent D .formula) :
    Nonempty (BagEquiv ((encode D).map Edge.args) f g) ↔
      SameArguments D ((formulas D).symm f) ((formulas D).symm g) := by
  change Nonempty (BagEquiv (arguments D).toSpan f g) ↔ _
  rw [family_bag (arguments D)]
  unfold SameArguments
  exact exists_congr (fun e => forall_congr' (fun a => (arrows D).injective.eq_iff))

theorem pred_bags (f g : extent D .formula) :
    Nonempty (BagEquiv ((encode D).map Edge.pred) f g) ↔
      ((formulas D).symm f).val.symbol = ((formulas D).symm g).val.symbol := by
  change Nonempty (BagEquiv (Span.ofFunction
    (fun x => symbols D ((formulas D).symm x).val.symbol)) f g) ↔ _
  rw [function_bag]
  exact (symbols D).injective.eq_iff

theorem literal_key_iff :
    (interpretation (context D)).Satisfies (encode D) literalKey ↔ Separated D := by
  change Key _ ↔ _
  constructor
  · intro h f g hs hb
    apply (formulas D).injective
    apply h
    intro i
    fin_cases i
    · apply (args_bags D _ _).mpr
      simpa only [Equiv.symm_apply_apply] using hb
    · apply (pred_bags D _ _).mpr
      simpa only [Equiv.symm_apply_apply] using hs
  · intro h f g hh
    apply (formulas D).symm.injective
    exact h _ _ ((pred_bags D f g).mp (hh 1)) ((args_bags D f g).mp (hh 0))

theorem classifiers_cover :
    (interpretation (context D)).Satisfies (encode D) (declaration .classifiersCover) := by
  rintro ⟨x, (⟨c, hc⟩ | ⟨e, he⟩)⟩
  · exact ⟨0, vertices D c, Subtype.ext hc⟩
  · exact ⟨1, arrows D e, Subtype.ext he⟩

theorem classifiers_disjoint :
    (interpretation (context D)).Satisfies (encode D) (declaration .classifiersDisjoint) := by
  intro i j hij l m he
  fin_cases i <;> fin_cases j
  · exact hij rfl
  · obtain ⟨c, hc⟩ := l.property
    obtain ⟨e, hm⟩ := m.property
    have h := hc.trans ((congrArg Subtype.val he).trans hm.symm)
    cases h
  · obtain ⟨e, he'⟩ := l.property
    obtain ⟨c, hm⟩ := m.property
    have h := he'.trans ((congrArg Subtype.val he).trans hm.symm)
    cases h
  · exact hij rfl

theorem predefined_cover :
    (interpretation (context D)).Satisfies (encode D) (declaration .predefinedCover) := by
  rintro ⟨x, hc, i, hi⟩
  cases hk : R.kind i with
  | singleton => exact ⟨0, ⟨x, hc, i, hi, hk⟩, rfl⟩
  | primitive => exact ⟨1, ⟨x, hc, i, hi, hk⟩, rfl⟩

theorem predefined_disjoint :
    (interpretation (context D)).Satisfies (encode D) (declaration .predefinedDisjoint) := by
  intro i j hij l m he
  fin_cases i <;> fin_cases j
  · exact hij rfl
  · obtain ⟨a, ha, ka⟩ := l.property.2
    obtain ⟨b, hb, kb⟩ := m.property.2
    have hv : l.val = m.val := congrArg Subtype.val he
    rw [hv] at ha
    have hab := Option.some.inj (ha.symm.trans hb)
    cases hab
    cases ka.symm.trans kb
  · obtain ⟨a, ha, ka⟩ := l.property.2
    obtain ⟨b, hb, kb⟩ := m.property.2
    have hv : l.val = m.val := congrArg Subtype.val he
    rw [hv] at ha
    have hab := Option.some.inj (ha.symm.trans hb)
    cases hab
    cases ka.symm.trans kb
  · exact hij rfl

/-- Exactly the two independent printed constraints are conditional. -/
theorem other_declarations (d : Declaration) (ht : d ≠ .argsTotal) (hk : d ≠ .key) :
    (interpretation (context D)).Satisfies (encode D) (declaration d) := by
  cases d
  all_goals first
    | exact (ht rfl).elim
    | exact (hk rfl).elim
    | exact satisfies_names D
    | exact satisfies_arities D
    | exact classifiers_cover D
    | exact classifiers_disjoint D
    | exact predefined_cover D
    | exact predefined_disjoint D
    | exact ⟨Function.bijective_id, fun _ => rfl⟩
    | exact Function.injective_id
    | exact Function.surjective_id
    | exact fun _ _ h => congrArg Prod.fst h

-- [proof->req~formalcd-metamodel-realization~1]
/-- Canonical syntax realizes the unchanged Figure 21c iff its declared formulas
have positive argument support and are separated by symbol plus argument bag. -/
theorem model_iff : (interpretation (context D)).IsModel diagram.toDPGraph (encode D) ↔
    Supported D ∧ Separated D := by
  constructor
  · intro h
    exact ⟨(total_args_iff D).mp (h _ (declared .argsTotal)),
      (literal_key_iff D).mp (h _ (declared .key))⟩
  · rintro ⟨ht, hk⟩ _ ⟨d, rfl⟩
    by_cases hdt : d = .argsTotal
    · subst d; exact (total_args_iff D).mpr ht
    by_cases hdk : d = .key
    · subst d; exact (literal_key_iff D).mpr hk
    exact other_declarations D d hdt hdk

noncomputable def model (ht : Supported D) (hk : Separated D) :
    (interpretation (context D)).Model diagram.toDPGraph :=
  ⟨encode D, (model_iff D).mpr ⟨ht, hk⟩⟩

end FormalCD.Metamodel.Realization
