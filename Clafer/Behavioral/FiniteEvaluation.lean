module

public import Clafer.Behavioral.Lasso

/-! # Executable normalized-core evaluation

Behavioral paper §5 Definition 5, with pinned errata T1/T2/T7/T13 and the
accepted D1 observations, supplies the independent meaning being implemented.
Finite observations supply total atom values and finite domains, with a separate
agreement contract against the independent `Observation`. All captured sets are
retained across time; quantification never changes the attachment identity.
-/

@[expose] public section
namespace Clafer.Behavioral

-- [impl->req~behavioral-finite-checker~1]
structure FiniteEnvironment (size n : Nat) where
  this : Fin size
  lookup : Fin n → Finset (Fin size)

namespace FiniteEnvironment
variable {size n : Nat}
def closed (x : Fin size) : FiniteEnvironment size 0 := ⟨x, Fin.elim0⟩
def push (ρ : FiniteEnvironment size n) (s : Finset (Fin size)) : FiniteEnvironment size (n + 1) :=
  ⟨ρ.this, Fin.cases s ρ.lookup⟩
def realize (ρ : FiniteEnvironment size n) : Environment (Fin size) n :=
  ⟨ρ.this, fun v => ↑(ρ.lookup v)⟩

@[simp] theorem realize_closed (x : Fin size) : (closed x).realize = Environment.closed x := by
  unfold closed realize Environment.closed
  congr 1
  funext v
  exact Fin.elim0 v

@[simp] theorem realize_push (ρ : FiniteEnvironment size n) (s : Finset (Fin size)) :
    (ρ.push s).realize = ρ.realize.push (↑s) := by
  unfold realize push Environment.push
  congr 1
  funext v
  refine Fin.cases ?_ (fun _ => ?_) v <;> rfl
end FiniteEnvironment

-- [impl->req~behavioral-finite-checker~1]
structure FiniteObservation (A D : Nat → Type) (size last : Nat) where
  atom : ∀ {n}, A n → FiniteEnvironment size n → Lasso.Clock last → Bool
  domain : ∀ {n}, D n → FiniteEnvironment size n → Lasso.Clock last → Finset (Fin size)

namespace FiniteObservation
variable {A D : Nat → Type} {C : Type} {size last : Nat}

/-- Adapter obligations include every captured environment and every absolute
time. Checking a few observed states cannot replace these source agreements. -/
structure Agrees (F : FiniteObservation A D size last) (L : Lasso C size last)
    (O : Observation A D (Fin size)) : Prop where
  atom : ∀ {n} (a : A n) ρ t, F.atom a ρ (L.clock t) = true ↔ O.atom a ρ.realize t
  domain : ∀ {n} (d : D n) ρ t, (↑(F.domain d ρ (L.clock t)) : Set (Fin size)) =
    O.domain d ρ.realize t
end FiniteObservation

namespace Quantifier
-- [impl->req~behavioral-finite-checker~1]
def finite {size : Nat} (q : Quantifier) (s : Finset (Fin size)) (a : Fin size → Bool) : Bool :=
  match q with
  | .all => decide (∀ x ∈ s, a x = true)
  | .some => decide (∃ x ∈ s, a x = true)
  | .no => !decide (∃ x ∈ s, a x = true)
  | .one => decide (∃ x, x ∈ s ∧ a x = true ∧ ∀ y, y ∈ s ∧ a y = true → y = x)
  | .lone => decide (∀ x ∈ s, ∀ y ∈ s, a x = true → a y = true → x = y)

-- [proof->req~behavioral-finite-checker~1]
theorem finite_agrees {size : Nat} (q : Quantifier) (s : Finset (Fin size)) (a : Fin size → Bool) :
    q.finite s a = true ↔ q.eval (↑s) (fun x => a x = true) := by
  cases q <;> simp [finite, eval, ExistsUnique, and_assoc]
end Quantifier

namespace Core
variable {A D : Nat → Type} {C : Type} {size last : Nat}

-- [impl->req~behavioral-finite-checker~1]
/-- A terminating evaluator for every accepted core constructor. The search
bound is the proved cardinality of the history-expanded finite clock. -/
def evaluateStep (L : Lasso C size last) (F : FiniteObservation A D size last)
    (go : ∀ {n}, Core A D n → FiniteEnvironment size n → Lasso.Clock last → Bool) {n} :
    Core A D n → FiniteEnvironment size n → Lasso.Clock last → Bool
  | .truth, _, _ => true
  | .atom (.source a), ρ, s => F.atom a ρ s
  | .atom .parentPresent, ρ, s => L.parentPresent s ρ.this
  | .atom .starts, ρ, s => L.starts s ρ.this
  | .atom .ends, ρ, s => L.ends s ρ.this
  | .not a, ρ, s => !go a ρ s
  | .and a b, ρ, s => go a ρ s && go b ρ s
  | .or a b, ρ, s => go a ρ s || go b ρ s
  | .next a, ρ, s => go a ρ (L.step s)
  | .eventually a, ρ, s => Orbit.some L.step (go a ρ) s
  | .always a, ρ, s => Orbit.every L.step (go a ρ) s
  | .strongUntil a b, ρ, s => Orbit.untilB L.step (go a ρ) (go b ρ) s
  | .weakUntil a b, ρ, s => Orbit.every L.step (go a ρ) s || Orbit.untilB L.step (go a ρ) (go b ρ) s
  | .quant q d a, ρ, s => q.finite (F.domain d ρ s) (fun x => go a (ρ.push {x}) s)
  | .letSet d a, ρ, s => go a (ρ.push (F.domain d ρ s)) s

-- [impl->req~behavioral-finite-checker~1]
/-- Direct well-founded recursion keeps the kernel-checked decreasing measure
without introducing a generated partial recursion declaration. The syntax-size
measure is used only in proofs, never as a temporal or runtime cutoff. -/
def finite (L : Lasso C size last) (F : FiniteObservation A D size last) {n}
    (a : Core A D n) : FiniteEnvironment size n → Lasso.Clock last → Bool :=
  (measure (fun p : (n : Nat) × Core A D n => sizeOf p.2)).wf.fix
    (C := fun (p : (n : Nat) × Core A D n) => FiniteEnvironment size p.1 → Lasso.Clock last → Bool)
    (fun p go => match p with
      | ⟨_, .truth⟩ => fun _ _ => true
      | ⟨_, .atom (.source a)⟩ => fun ρ s => F.atom a ρ s
      | ⟨_, .atom .parentPresent⟩ => fun ρ s => L.parentPresent s ρ.this
      | ⟨_, .atom .starts⟩ => fun ρ s => L.starts s ρ.this
      | ⟨_, .atom .ends⟩ => fun ρ s => L.ends s ρ.this
      | ⟨_, .not a⟩ => fun ρ s => !go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ s
      | ⟨_, .and a b⟩ => fun ρ s => go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ s &&
          go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ s
      | ⟨_, .or a b⟩ => fun ρ s => go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ s ||
          go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ s
      | ⟨_, .next a⟩ => fun ρ s => go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ (L.step s)
      | ⟨_, .eventually a⟩ => fun ρ s => Orbit.some L.step
          (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ) s
      | ⟨_, .always a⟩ => fun ρ s => Orbit.every L.step
          (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ) s
      | ⟨_, .strongUntil a b⟩ => fun ρ s => Orbit.untilB L.step
          (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ)
          (go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ) s
      | ⟨_, .weakUntil a b⟩ => fun ρ s => Orbit.every L.step
          (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ) s || Orbit.untilB L.step
          (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ)
          (go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ) s
      | ⟨_, .quant q d a⟩ => fun ρ s => q.finite (F.domain d ρ s) (fun x =>
          go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) (ρ.push {x}) s)
      | ⟨_, .letSet d a⟩ => fun ρ s =>
          go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) (ρ.push (F.domain d ρ s)) s) ⟨n, a⟩

theorem finite_eq (L : Lasso C size last) (F : FiniteObservation A D size last) {n}
    (a : Core A D n) :
    a.finite L F = evaluateStep L F (finite L F) a := by
  funext ρ s
  unfold finite
  rw [WellFounded.fix_eq]
  cases a <;> try rfl
  rename_i a
  cases a <;> rfl

-- Constructor equations keep reduction on concrete syntax terminating.
variable (L : Lasso C size last) (F : FiniteObservation A D size last)

@[simp] theorem finite_truth {n : Nat} :
    finite L F (.truth : Core A D n) = fun _ _ => true := finite_eq L F _

@[simp] theorem finite_source {n : Nat} (a : A n) :
    finite L F (.atom (.source a)) = fun ρ s => F.atom a ρ s := finite_eq L F _

@[simp] theorem finite_parentPresent {n : Nat} :
    finite L F (.atom (.parentPresent) : Core A D n) = fun ρ s => L.parentPresent s ρ.this := finite_eq L F _

@[simp] theorem finite_starts {n : Nat} :
    finite L F (.atom (.starts) : Core A D n) = fun ρ s => L.starts s ρ.this := finite_eq L F _

@[simp] theorem finite_ends {n : Nat} :
    finite L F (.atom (.ends) : Core A D n) = fun ρ s => L.ends s ρ.this := finite_eq L F _

@[simp] theorem finite_not {n : Nat} (a : Core A D n) :
    finite L F (.not a) = fun ρ s => !a.finite L F ρ s := finite_eq L F _

@[simp] theorem finite_and {n : Nat} (a b : Core A D n) :
    finite L F (.and a b) = fun ρ s => a.finite L F ρ s && b.finite L F ρ s := finite_eq L F _

@[simp] theorem finite_or {n : Nat} (a b : Core A D n) :
    finite L F (.or a b) = fun ρ s => a.finite L F ρ s || b.finite L F ρ s := finite_eq L F _

@[simp] theorem finite_next {n : Nat} (a : Core A D n) :
    finite L F (.next a) = fun ρ s => a.finite L F ρ (L.step s) := finite_eq L F _

@[simp] theorem finite_eventually {n : Nat} (a : Core A D n) :
    finite L F (.eventually a) = fun ρ s => Orbit.some L.step (a.finite L F ρ) s := finite_eq L F _

@[simp] theorem finite_always {n : Nat} (a : Core A D n) :
    finite L F (.always a) = fun ρ s => Orbit.every L.step (a.finite L F ρ) s := finite_eq L F _

@[simp] theorem finite_strongUntil {n : Nat} (a b : Core A D n) :
    finite L F (.strongUntil a b) = fun ρ s => Orbit.untilB L.step (a.finite L F ρ) (b.finite L F ρ) s := finite_eq L F _

@[simp] theorem finite_weakUntil {n : Nat} (a b : Core A D n) :
    finite L F (.weakUntil a b) = fun ρ s => Orbit.every L.step (a.finite L F ρ) s ||
      Orbit.untilB L.step (a.finite L F ρ) (b.finite L F ρ) s := finite_eq L F _

@[simp] theorem finite_quant {n : Nat} (q : Quantifier) (d : D n) (a : Core A D (n + 1)) :
    finite L F (.quant q d a) = fun ρ s => q.finite (F.domain d ρ s) (fun x => a.finite L F (ρ.push {x}) s) := finite_eq L F _

@[simp] theorem finite_letSet {n : Nat} (d : D n) (a : Core A D (n + 1)) :
    finite L F (.letSet d a) = fun ρ s => a.finite L F (ρ.push (F.domain d ρ s)) s := finite_eq L F _


private theorem exists_offset (p : Nat → Prop) (t : Nat) :
    (∃ k, p (t + k)) ↔ ∃ j, t ≤ j ∧ p j := by
  constructor
  · rintro ⟨k, hk⟩; exact ⟨t + k, by omega, hk⟩
  · rintro ⟨j, hj, hp⟩; exact ⟨j - t, by simpa [Nat.add_sub_of_le hj] using hp⟩

private theorem all_offset (p : Nat → Prop) (t : Nat) :
    (∀ k, p (t + k)) ↔ ∀ j, t ≤ j → p j := by
  constructor
  · intro h j hj; simpa [Nat.add_sub_of_le hj] using h (j - t)
  · intro h k; exact h (t + k) (by omega)

private theorem until_offset (a b : Nat → Prop) (t : Nat) :
    (∃ k, b (t + k) ∧ ∀ i, i < k → a (t + i)) ↔ Temporal.strongUntil a b t := by
  constructor
  · rintro ⟨k, hb, ha⟩
    refine ⟨t + k, by omega, hb, ?_⟩
    intro j hj hjk
    simpa [Nat.add_sub_of_le hj] using ha (j - t) (by omega)
  · rintro ⟨j, hj, hb, ha⟩
    refine ⟨j - t, by simpa [Nat.add_sub_of_le hj] using hb, ?_⟩
    intro i hi; exact ha (t + i) (by omega) (by omega)

-- [proof->req~behavioral-finite-checker~1]
/-- Exact-candidate soundness and completeness on the infinite unfolding.
No validity assumption is hidden in observation agreement; structural admission
is a separate gate. Even raw signals have a well-defined temporal meaning. -/
theorem finite_agrees (L : Lasso C size last) (F : FiniteObservation A D size last)
    (O : Observation A D (Fin size)) (h : F.Agrees L O) {n} (a : Core A D n)
    (ρ : FiniteEnvironment size n) (t : Nat) :
    a.finite L F ρ (L.clock t) = true ↔ a.eval L.unfold O ρ.realize t := by
  induction a generalizing t with
  | truth => simp [finite_eq, evaluateStep, eval]
  | atom a =>
    rw [finite_eq]
    cases a with
    | source a => exact h.atom a ρ t
    | parentPresent => exact L.parentPresent_agrees t ρ.this
    | starts => exact L.starts_agrees t ρ.this
    | ends => exact L.ends_agrees t ρ.this
  | not a ih =>
    rw [finite_eq]
    simpa [evaluateStep, eval] using not_congr (ih ρ t)
  | and a b ia ib => rw [finite_eq]; simp [evaluateStep, eval, ia, ib]
  | or a b ia ib => rw [finite_eq]; simp [evaluateStep, eval, ia, ib]
  | next a ih =>
    rw [finite_eq]
    simpa [evaluateStep, eval, Temporal.next, Lasso.clock_succ] using ih ρ (t + 1)
  | eventually a ih =>
    rw [finite_eq]
    simp only [evaluateStep, eval, Orbit.some_iff, ← L.clock_add, ih, Temporal.eventually]
    exact exists_offset _ t
  | always a ih =>
    rw [finite_eq]
    simp only [evaluateStep, eval, Orbit.every_iff, ← L.clock_add, ih, Temporal.always]
    exact all_offset _ t
  | strongUntil a b ia ib =>
    rw [finite_eq]
    simp only [evaluateStep, eval, Orbit.until_iff, ← L.clock_add, ia, ib]
    exact until_offset _ _ t
  | weakUntil a b ia ib =>
    rw [finite_eq]
    simp only [evaluateStep, eval, Bool.or_eq_true, Orbit.every_iff, Orbit.until_iff,
      ← L.clock_add, ia, ib, Temporal.weakUntil, ← until_offset, Temporal.always, ← all_offset]
  | quant q d a ih =>
    rw [finite_eq]
    simp only [evaluateStep, eval, Quantifier.finite_agrees, Quantifier.eval, ih,
      FiniteEnvironment.realize_push, Finset.coe_singleton, ← h.domain d ρ t]
  | letSet d a ih =>
    rw [finite_eq]
    simpa only [evaluateStep, eval, FiniteEnvironment.realize_push, h.domain] using
      ih (ρ.push (F.domain d ρ (L.clock t))) t

-- [proof->req~behavioral-finite-checker~1]
theorem normalized_finite_agrees (L : Lasso C size last) (F : FiniteObservation A D size last)
    (O : Observation A D (Fin size)) (h : F.Agrees L O) {n} (a : Formula A D n)
    (sign : Bool) (ρ : FiniteEnvironment size n) (t : Nat) :
    (a.normalize sign).lower.finite L F ρ (L.clock t) = true ↔
      a.denote L.unfold O sign ρ.realize t :=
  (finite_agrees L F O h _ ρ t).trans (Formula.normalize_lower_agrees _ _ _ _ _ _)
end Core
end Clafer.Behavioral
