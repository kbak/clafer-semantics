module

public import DPGraph.Predicates.FunctionalKey
public import Mathlib.Tactic.FinCases

/-! # Relational representations of span predicates

SoSyM Appendix 2, mappings (Definitions 1–5), mapping composition (Q1),
and Table 3/Appendix 1. All hypotheses concern spans, fibers and subsets;
no Clafer ownership or finite-carrier policy is imposed.
-/

@[expose] public section
universe u v z w w'
namespace DPGraph.Predicates

theorem inRange_one_iff (A : Type u) :
    InRange (⟨1, .finite 1⟩ : Range) A ↔ Nonempty A ∧ Subsingleton A := by
  unfold InRange
  constructor
  · rintro ⟨⟨lo⟩, ⟨hi⟩⟩
    exact ⟨⟨lo 0⟩, ⟨fun a b => hi.injective (Subsingleton.elim _ _)⟩⟩
  · rintro ⟨⟨a⟩, hs⟩
    exact ⟨⟨⟨fun _ => a, fun _ _ _ => Subsingleton.elim _ _⟩⟩,
      ⟨⟨fun _ => 0, fun x y _ => @Subsingleton.elim _ hs x y⟩⟩⟩

theorem one_iff_total_single {A : Type u} {B : Type v} (q : Span.{u,v,w} A B) :
    TargetMultiplicity (⟨1, .finite 1⟩ : Range) q ↔ Total q ∧ SingleValued q := by
  simp only [TargetMultiplicity, inRange_one_iff, total_fibers, singleValued_fibers,
    forall_and]

theorem relation_one_iff {A : Type u} {B : Type v} (R : A → B → Prop) :
    TargetMultiplicity (⟨1, .finite 1⟩ : Range) (Span.ofRelation R) ↔ ∀ a, ∃! b, R a b := by
  rw [one_iff_total_single]
  constructor
  · rintro ⟨ht, hs⟩ a
    obtain ⟨⟨⟨a', b⟩, hr⟩, he⟩ := ht a
    change a' = a at he
    subst a'
    refine ⟨b, hr, ?_⟩
    intro b' hb'
    have he := hs (a₁ := ⟨(a, b'), hb'⟩) (a₂ := ⟨(a, b), hr⟩) rfl
    exact congrArg (fun l => l.val.2) he
  · intro h
    constructor
    · intro a
      obtain ⟨b, hb, _⟩ := h a
      exact ⟨⟨(a, b), hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, hb⟩ ⟨⟨a', b'⟩, hb'⟩ he
      change a = a' at he
      subst a'
      exact Subtype.ext (Prod.ext rfl ((h a).unique hb hb'))

theorem setValued_one_iff {A : Type u} {B : Type v} (q : Span.{u,v,w} A B) (hq : SetValued q) :
    TargetMultiplicity (⟨1, .finite 1⟩ : Range) q ↔ ∀ a, ∃! b, q.red a b :=
  (targetMultiplicity_iff _ (q.relationIso hq)).trans (relation_one_iff _)

theorem unique_subtype_iff {U : Type u} (B : Set U) (P : U → Prop)
    (typed : ∀ b, P b → b ∈ B) : (∃! b : B, P b.val) ↔ ∃! b, P b := by
  constructor
  · rintro ⟨b, hb, hu⟩
    exact ⟨b.val, hb, fun c hc => congrArg Subtype.val (hu ⟨c, typed c hc⟩ hc)⟩
  · rintro ⟨b, hb, hu⟩
    exact ⟨⟨b, typed b hb⟩, hb, fun c hc => Subtype.ext (hu c.val hc)⟩

theorem identity_inclusion_iff {U : Type u} (A B : Set U) :
    Inclusion (Span.ofRelation (fun (a : A) (b : B) => a.val = b.val)) ↔ A ⊆ B := by
  constructor
  · exact inclusion_subset
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ he
      change a = a' at he
      subst a'
      exact Subtype.ext (Prod.ext rfl (Subtype.ext (hab.symm.trans hab')))
    · intro a
      exact ⟨⟨(a, ⟨a.val, h a.property⟩), rfl⟩, rfl⟩
    · intro l
      exact l.property.symm

-- [impl->req~reusable-span-laws~1]
/-- With one dereference link per head, composable target links and head
links have exactly the same multiplicity, including repeated target values. -/
noncomputable def compositeFiber {A : Type u} {B : Type v} {C : Type z}
    (q : Span.{u,v,w} A B) (r : Span.{v,z,w'} B C)
    (ht : Total r) (hs : SingleValued r) (a : A) :
    (q.comp r).toFamily.Index a ≃ q.toFamily.Index a :=
  Equiv.ofBijective (fun l => ⟨l.val.val.1, l.property⟩)
    ⟨by
      intro l k he
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg Subtype.val he
      · apply hs
        exact l.val.property.symm.trans
          ((congrArg q.target (congrArg Subtype.val he)).trans k.val.property), by
      intro l
      obtain ⟨r', hr⟩ := ht (q.target l.val)
      exact ⟨⟨⟨(l.val, r'), hr.symm⟩, l.property⟩, rfl⟩⟩

-- [proof->req~reusable-span-laws~1]
theorem composite_multiplicity {A : Type u} {B : Type v} {C : Type z}
    (q : Span.{u,v,w} A B) (r : Span.{v,z,w'} B C)
    (ht : Total r) (hs : SingleValued r) (range : Range) :
    TargetMultiplicity range (q.comp r) ↔ TargetMultiplicity range q :=
  forall_congr' (fun a => inRange_iff range (compositeFiber q r ht hs a))

def pairSpans {A : Type u} {B C : Type v}
    (q : Span.{u,v,w} A B) (r : Span.{u,v,w} A C) :
    (i : Fin 2) → Span A (Fin.cases B (fun _ => C) i) :=
  Fin.cases q (fun _ => r)

theorem two_key_iff {A : Type u} {B : Fin 2 → Type v} (q : ∀ i, Span.{u,v,w} A (B i))
    (ht : ∀ i, Total (q i)) (hs : ∀ i, SingleValued (q i)) :
    Key q ↔ ∀ a a' (b : B 0) (c : B 1),
      (q 0).red a b → (q 1).red a c →
      (q 0).red a' b → (q 1).red a' c → a = a' := by
  rw [key_total_singleValued_iff _ ht hs]
  constructor
  · intro h a a' b c hq hr hq' hr'
    apply h
    funext i
    fin_cases i
    · exact ((red_iff_targetValue_eq (q 0) (ht 0) (hs 0) a b).mp hq).trans
        ((red_iff_targetValue_eq (q 0) (ht 0) (hs 0) a' b).mp hq').symm
    · exact ((red_iff_targetValue_eq (q 1) (ht 1) (hs 1) a c).mp hr).trans
        ((red_iff_targetValue_eq (q 1) (ht 1) (hs 1) a' c).mp hr').symm
  · intro h a a' he
    exact h a a' (targetValue (q 0) (ht 0) (hs 0) a)
      (targetValue (q 1) (ht 1) (hs 1) a)
      ((red_iff_targetValue_eq _ _ _ _ _).mpr rfl)
      ((red_iff_targetValue_eq _ _ _ _ _).mpr rfl)
      ((red_iff_targetValue_eq _ _ _ _ _).mpr (congrFun he 0).symm)
      ((red_iff_targetValue_eq _ _ _ _ _).mpr (congrFun he 1).symm)

theorem pair_key_iff {A : Type u} {B C : Type v}
    (q : Span.{u,v,w} A B) (r : Span.{u,v,w} A C)
    (qt : Total q) (qs : SingleValued q) (rt : Total r) (rs : SingleValued r) :
    Key (pairSpans q r) ↔
      ∀ a a' b c, q.red a b → r.red a c → q.red a' b → r.red a' c → a = a' := by
  have ht : ∀ i, Total (pairSpans q r i) := by intro i; fin_cases i <;> assumption
  have hs : ∀ i, SingleValued (pairSpans q r i) := by intro i; fin_cases i <;> assumption
  rw [key_total_singleValued_iff _ ht hs]
  constructor
  · intro h a a' b c hq hr hq' hr'
    apply h
    funext i
    fin_cases i
    · exact ((red_iff_targetValue_eq q qt qs a b).mp hq).trans
        ((red_iff_targetValue_eq q qt qs a' b).mp hq').symm
    · exact ((red_iff_targetValue_eq r rt rs a c).mp hr).trans
        ((red_iff_targetValue_eq r rt rs a' c).mp hr').symm
  · intro h a a' he
    exact h a a' (targetValue q qt qs a) (targetValue r rt rs a)
      ((red_iff_targetValue_eq q qt qs _ _).mpr rfl)
      ((red_iff_targetValue_eq r rt rs _ _).mpr rfl)
      ((red_iff_targetValue_eq q qt qs _ _).mpr (congrFun he 0).symm)
      ((red_iff_targetValue_eq r rt rs _ _).mpr (congrFun he 1).symm)

/-- Every represented identity inclusion preserves its ambient object. -/
noncomputable def inclusionIso {A B : Set U} (q : Span.{u,u,w} A B) (h : Inclusion q) :
    Span.Iso q (Span.ofRelation (fun (a : A) (b : B) => a.val = b.val)) := by
  have sv : SetValued q := fun a b he => h.1.1 (congrArg Prod.fst he)
  have he : q.red = (fun (a : A) (b : B) => a.val = b.val) := by
    funext a b
    apply propext
    constructor
    · rintro ⟨l, rfl, rfl⟩; exact (h.2 l).symm
    · intro hab
      obtain ⟨l, hl⟩ := h.1.2 a
      refine ⟨l, hl, Subtype.ext ?_⟩
      exact (h.2 l).trans ((congrArg Subtype.val hl).trans hab)
  rw [← he]
  exact q.relationIso sv

end DPGraph.Predicates
