module

public import DPGraph.Predicates.Meaning

/-!
[impl->req~predicate-key-functional~1]
[proof->req~predicate-key-functional~1]
-/

/-!
# Ordinary keys as a specialization of bag-sensitive keys

Derived from SoSyM B.1 Definitions 1–5 / Theorems 1–2 and Table 3 key /
Figure 21c. The comparison is motivated by Diskin et al. (2000), §2.1 p. 348
(separating family / injective tuple). Totality and single-valuedness supply
the unique links used here; unrestricted `Key` still compares full bags.
-/

@[expose] public section

universe u v w

namespace DPGraph.Predicates

variable {A : Type u} {B : Type v}

theorem ofFunction_total (f : A → B) : Total (Span.ofFunction f) :=
  fun a => ⟨a, rfl⟩

theorem ofFunction_singleValued (f : A → B) : SingleValued (Span.ofFunction f) :=
  fun _ _ h => h

/-- Singleton output bags agree exactly when their values agree. -/
theorem bagEquiv_ofFunction_iff (f : A → B) (a a' : A) :
    Nonempty (BagEquiv (Span.ofFunction f) a a') ↔ f a = f a' := by
  constructor
  · rintro ⟨e⟩
    have ht := e.target_eq ⟨a, rfl⟩
    have hs : (e.equiv ⟨a, rfl⟩).val = a' := (e.equiv ⟨a, rfl⟩).property
    exact ht.symm.trans (congrArg f hs)
  · intro h
    refine ⟨⟨{
      toFun := fun _ => ⟨a', rfl⟩
      invFun := fun _ => ⟨a, rfl⟩
      left_inv := fun l => Subtype.ext l.property.symm
      right_inv := fun l => Subtype.ext l.property.symm }, ?_⟩⟩
    intro l
    exact h.symm.trans (congrArg f l.property).symm

/-- Arbitrary finite arity, including zero; no inhabitance or finiteness of A. -/
theorem key_ofFunction_iff {n : Nat} {B : Fin n → Type v} (f : ∀ i, A → B i) :
    Key (fun i => Span.ofFunction (f i)) ↔
      Function.Injective (fun a i => f i a) := by
  constructor
  · intro h a a' he
    exact h a a' (fun i => (bagEquiv_ofFunction_iff (f i) a a').mpr (congrFun he i))
  · intro h a a' he
    exact h (funext (fun i => (bagEquiv_ofFunction_iff (f i) a a').mp (he i)))

/-- The target of the unique link at a source, using the bijective source leg. -/
noncomputable def targetValue (q : Span.{u,v,w} A B)
    (ht : Total q) (hs : SingleValued q) (a : A) : B :=
  q.target ((Equiv.ofBijective q.source ⟨hs, ht⟩).symm a)

theorem targetValue_eq_of_source (q : Span.{u,v,w} A B)
    (ht : Total q) (hs : SingleValued q) {a : A} (l : q.Link)
    (hl : q.source l = a) : targetValue q ht hs a = q.target l := by
  subst a
  exact congrArg q.target ((Equiv.ofBijective q.source ⟨hs, ht⟩).symm_apply_apply l)

/-- Existence and uniqueness of the target value are justified by both hypotheses. -/
theorem red_iff_targetValue_eq (q : Span.{u,v,w} A B)
    (ht : Total q) (hs : SingleValued q) (a : A) (b : B) :
    q.red a b ↔ targetValue q ht hs a = b := by
  constructor
  · rintro ⟨l, hl, hb⟩
    exact (targetValue_eq_of_source q ht hs l hl).trans hb
  · intro h
    exact ⟨(Equiv.ofBijective q.source ⟨hs, ht⟩).symm a,
      (Equiv.ofBijective q.source ⟨hs, ht⟩).apply_symm_apply a, h⟩

/-- Link-preserving, even when the original head and source universes differ. -/
noncomputable def functionalSpanIso (q : Span.{u,v,w} A B)
    (ht : Total q) (hs : SingleValued q) :
    Span.Iso q (Span.ofFunction (targetValue q ht hs)) where
  equiv := Equiv.ofBijective q.source ⟨hs, ht⟩
  source_eq _ := rfl
  target_eq l := targetValue_eq_of_source q ht hs l rfl

/-- The ordinary tuple criterion for arbitrary componentwise total, single-valued spans. -/
theorem key_total_singleValued_iff {n : Nat} {B : Fin n → Type v}
    (q : ∀ i, Span.{u,v,w} A (B i))
    (ht : ∀ i, Total (q i)) (hs : ∀ i, SingleValued (q i)) :
    Key q ↔ Function.Injective (fun a i => targetValue (q i) (ht i) (hs i) a) :=
  (key_iff (fun i => functionalSpanIso (q i) (ht i) (hs i))).trans
    (key_ofFunction_iff (fun i => targetValue (q i) (ht i) (hs i)))

/-- The empty dependent tuple criterion agrees with the unrestricted `key_zero`. -/
theorem tuple_injective_zero_iff {B : Fin 0 → Type v} (f : ∀ i, A → B i) :
    Function.Injective (fun a i => f i a) ↔ Subsingleton A :=
  (key_ofFunction_iff f).symm.trans (key_zero _)

end DPGraph.Predicates
