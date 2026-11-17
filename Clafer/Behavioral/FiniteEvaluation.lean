module

public import Clafer.Behavioral.Lasso
public import Clafer.Behavioral.FiniteMachine

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

def clockMachine {α : Type} (L : Lasso C size last) (output : Lasso.Clock last → α) : FiniteMachine α :=
  FiniteMachine.ofFinite Lasso.start L.step output

@[simp] theorem run_clockMachine {α : Type} (L : Lasso C size last)
    (output : Lasso.Clock last → α) (t : Nat) :
    (clockMachine L output).run t = output (L.clock t) := rfl

-- [impl->req~behavioral-past-verification~1]
def machineStep (L : Lasso C size last) (F : FiniteObservation A D size last)
    (go : ∀ {n}, Core A D n → FiniteEnvironment size n → FiniteMachine Bool) {n} :
    Core A D n → FiniteEnvironment size n → FiniteMachine Bool
  | .truth, _ => clockMachine L (fun _ => true)
  | .atom (.source a), ρ => clockMachine L (F.atom a ρ)
  | .atom .parentPresent, ρ => clockMachine L (fun s => L.parentPresent s ρ.this)
  | .atom .contextPresent, ρ => clockMachine L (fun s => L.live s.1 ρ.this)
  | .atom .starts, ρ => clockMachine L (fun s => L.starts s ρ.this)
  | .atom .ends, ρ => clockMachine L (fun s => L.ends s ρ.this)
  | .not a, ρ => (go a ρ).map Bool.not
  | .and a b, ρ => ((go a ρ).pair (go b ρ)).map (fun p => p.1 && p.2)
  | .or a b, ρ => ((go a ρ).pair (go b ρ)).map (fun p => p.1 || p.2)
  | .next a, ρ => (go a ρ).next
  | .eventually a, ρ => (go a ρ).eventually
  | .always a, ρ => (go a ρ).always
  | .strongUntil a b, ρ => ((go a ρ).pair (go b ρ)).searchUntil Prod.fst Prod.snd
  | .weakUntil a b, ρ => (((go a ρ).always).pair (((go a ρ).pair (go b ρ)).searchUntil Prod.fst Prod.snd)).map (fun p => p.1 || p.2)
  | .previous a, ρ => (go a ρ).previous
  | .since a b, ρ => ((go a ρ).pair (go b ρ)).since
  | .quant q d a, ρ => ((clockMachine L (F.domain d ρ)).pair (FiniteMachine.family (fun x => go a (ρ.push {x})))).map (fun p => q.finite p.1 p.2)
  | .letSet d a, ρ => ((clockMachine L id).pair (FiniteMachine.family (fun s => go a (ρ.push (F.domain d ρ s))))).map (fun p => p.2 p.1)

/-- Syntax recursion builds a finite history machine. The closure under capture
uses all identities for quantifiers, and only base-clock-indexed domain values
for let: it never enumerates the powerset of the object carrier. -/
def machine (L : Lasso C size last) (F : FiniteObservation A D size last) {n}
    (a : Core A D n) : FiniteEnvironment size n → FiniteMachine Bool :=
  (measure (fun p : (n : Nat) × Core A D n => sizeOf p.2)).wf.fix
    (C := fun (p : (n : Nat) × Core A D n) => FiniteEnvironment size p.1 → FiniteMachine Bool)
    (fun p go => match p with
      | ⟨_, .truth⟩ => fun _ => clockMachine L (fun _ => true)
      | ⟨_, .atom (.source a)⟩ => fun ρ => clockMachine L (F.atom a ρ)
      | ⟨_, .atom .parentPresent⟩ => fun ρ => clockMachine L (fun s => L.parentPresent s ρ.this)
      | ⟨_, .atom .contextPresent⟩ => fun ρ => clockMachine L (fun s => L.live s.1 ρ.this)
      | ⟨_, .atom .starts⟩ => fun ρ => clockMachine L (fun s => L.starts s ρ.this)
      | ⟨_, .atom .ends⟩ => fun ρ => clockMachine L (fun s => L.ends s ρ.this)
      | ⟨_, .not a⟩ => fun ρ => (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ).map Bool.not
      | ⟨_, .and a b⟩ => fun ρ => ((go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ).pair (go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ)).map (fun p => p.1 && p.2)
      | ⟨_, .or a b⟩ => fun ρ => ((go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ).pair (go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ)).map (fun p => p.1 || p.2)
      | ⟨_, .next a⟩ => fun ρ => (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ).next
      | ⟨_, .eventually a⟩ => fun ρ => (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ).eventually
      | ⟨_, .always a⟩ => fun ρ => (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ).always
      | ⟨_, .strongUntil a b⟩ => fun ρ => ((go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ).pair (go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ)).searchUntil Prod.fst Prod.snd
      | ⟨_, .weakUntil a b⟩ => fun ρ => (((go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ).always).pair (((go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ).pair (go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ)).searchUntil Prod.fst Prod.snd)).map (fun p => p.1 || p.2)
      | ⟨_, .previous a⟩ => fun ρ => (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ).previous
      | ⟨_, .since a b⟩ => fun ρ => ((go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ).pair (go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp +arith) ρ)).since
      | ⟨_, .quant q d a⟩ => fun ρ => ((clockMachine L (F.domain d ρ)).pair (FiniteMachine.family (fun x => go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) (ρ.push {x})))).map (fun p => q.finite p.1 p.2)
      | ⟨_, .letSet d a⟩ => fun ρ => ((clockMachine L id).pair (FiniteMachine.family (fun s => go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp +arith) (ρ.push (F.domain d ρ s))))).map (fun p => p.2 p.1)) ⟨n, a⟩

theorem machine_eq (L : Lasso C size last) (F : FiniteObservation A D size last) {n}
    (a : Core A D n) : a.machine L F = machineStep L F (machine L F) a := by
  funext ρ
  unfold machine
  rw [WellFounded.fix_eq]
  cases a <;> try rfl
  rename_i a
  cases a <;> rfl

-- Constructor equations expose executable syntax recursion to kernel reduction.

@[simp] theorem machine_truth (L : Lasso C size last) (F : FiniteObservation A D size last)
    {n}  (ρ : FiniteEnvironment size n) :
    machine L F (.truth : Core A D n) ρ = clockMachine L (fun _ => true) := congrFun (machine_eq L F _) ρ

@[simp] theorem machine_source (L : Lasso C size last) (F : FiniteObservation A D size last)
    {n} (a : A n) (ρ : FiniteEnvironment size n) :
    machine L F (.atom (.source a) : Core A D n) ρ = clockMachine L (F.atom a ρ) := congrFun (machine_eq L F _) ρ

@[simp] theorem machine_parentPresent (L : Lasso C size last) (F : FiniteObservation A D size last)
    {n}  (ρ : FiniteEnvironment size n) :
    machine L F (.atom .parentPresent : Core A D n) ρ = clockMachine L (fun s => L.parentPresent s ρ.this) := congrFun (machine_eq L F _) ρ

@[simp] theorem machine_contextPresent (L : Lasso C size last) (F : FiniteObservation A D size last)
    {n} (ρ : FiniteEnvironment size n) :
    machine L F (.atom .contextPresent : Core A D n) ρ = clockMachine L (fun s => L.live s.1 ρ.this) :=
  congrFun (machine_eq L F _) ρ

@[simp] theorem machine_starts (L : Lasso C size last) (F : FiniteObservation A D size last)
    {n}  (ρ : FiniteEnvironment size n) :
    machine L F (.atom .starts : Core A D n) ρ = clockMachine L (fun s => L.starts s ρ.this) := congrFun (machine_eq L F _) ρ

@[simp] theorem machine_ends (L : Lasso C size last) (F : FiniteObservation A D size last)
    {n}  (ρ : FiniteEnvironment size n) :
    machine L F (.atom .ends : Core A D n) ρ = clockMachine L (fun s => L.ends s ρ.this) := congrFun (machine_eq L F _) ρ

@[simp] theorem machine_not (L : Lasso C size last) (F : FiniteObservation A D size last)
    {n} (a : Core A D n) (ρ : FiniteEnvironment size n) :
    machine L F (.not a : Core A D n) ρ = (machine L F a ρ).map Bool.not := congrFun (machine_eq L F _) ρ

@[simp] theorem machine_and (L : Lasso C size last) (F : FiniteObservation A D size last)
    {n} (a b : Core A D n) (ρ : FiniteEnvironment size n) :
    machine L F (.and a b : Core A D n) ρ = ((machine L F a ρ).pair (machine L F b ρ)).map (fun p => p.1 && p.2) := congrFun (machine_eq L F _) ρ

@[simp] theorem machine_or (L : Lasso C size last) (F : FiniteObservation A D size last)
    {n} (a b : Core A D n) (ρ : FiniteEnvironment size n) :
    machine L F (.or a b : Core A D n) ρ = ((machine L F a ρ).pair (machine L F b ρ)).map (fun p => p.1 || p.2) := congrFun (machine_eq L F _) ρ

@[simp] theorem machine_next (L : Lasso C size last) (F : FiniteObservation A D size last)
    {n} (a : Core A D n) (ρ : FiniteEnvironment size n) :
    machine L F (.next a : Core A D n) ρ = (machine L F a ρ).next := congrFun (machine_eq L F _) ρ

@[simp] theorem machine_eventually (L : Lasso C size last) (F : FiniteObservation A D size last)
    {n} (a : Core A D n) (ρ : FiniteEnvironment size n) :
    machine L F (.eventually a : Core A D n) ρ = (machine L F a ρ).eventually := congrFun (machine_eq L F _) ρ

@[simp] theorem machine_always (L : Lasso C size last) (F : FiniteObservation A D size last)
    {n} (a : Core A D n) (ρ : FiniteEnvironment size n) :
    machine L F (.always a : Core A D n) ρ = (machine L F a ρ).always := congrFun (machine_eq L F _) ρ

@[simp] theorem machine_strongUntil (L : Lasso C size last) (F : FiniteObservation A D size last)
    {n} (a b : Core A D n) (ρ : FiniteEnvironment size n) :
    machine L F (.strongUntil a b : Core A D n) ρ = ((machine L F a ρ).pair (machine L F b ρ)).searchUntil Prod.fst Prod.snd := congrFun (machine_eq L F _) ρ

@[simp] theorem machine_weakUntil (L : Lasso C size last) (F : FiniteObservation A D size last)
    {n} (a b : Core A D n) (ρ : FiniteEnvironment size n) :
    machine L F (.weakUntil a b : Core A D n) ρ = (((machine L F a ρ).always).pair (((machine L F a ρ).pair (machine L F b ρ)).searchUntil Prod.fst Prod.snd)).map (fun p => p.1 || p.2) := congrFun (machine_eq L F _) ρ

@[simp] theorem machine_previous (L : Lasso C size last) (F : FiniteObservation A D size last)
    {n} (a : Core A D n) (ρ : FiniteEnvironment size n) :
    machine L F (.previous a : Core A D n) ρ = (machine L F a ρ).previous := congrFun (machine_eq L F _) ρ

@[simp] theorem machine_since (L : Lasso C size last) (F : FiniteObservation A D size last)
    {n} (a b : Core A D n) (ρ : FiniteEnvironment size n) :
    machine L F (.since a b : Core A D n) ρ = ((machine L F a ρ).pair (machine L F b ρ)).since := congrFun (machine_eq L F _) ρ

@[simp] theorem machine_quant (L : Lasso C size last) (F : FiniteObservation A D size last)
    {n} (q : Quantifier) (d : D n) (a : Core A D (n + 1)) (ρ : FiniteEnvironment size n) :
    machine L F (.quant q d a : Core A D n) ρ = ((clockMachine L (F.domain d ρ)).pair (FiniteMachine.family (fun x => machine L F a (ρ.push {x})))).map (fun p => q.finite p.1 p.2) := congrFun (machine_eq L F _) ρ

@[simp] theorem machine_letSet (L : Lasso C size last) (F : FiniteObservation A D size last)
    {n} (d : D n) (a : Core A D (n + 1)) (ρ : FiniteEnvironment size n) :
    machine L F (.letSet d a : Core A D n) ρ = ((clockMachine L id).pair (FiniteMachine.family (fun s => machine L F a (ρ.push (F.domain d ρ s))))).map (fun p => p.2 p.1) := congrFun (machine_eq L F _) ρ

-- [impl->req~behavioral-past-verification~1]
/-- Absolute time is required: repeated base clocks may have different pasts. -/
@[simp] def finite (L : Lasso C size last) (F : FiniteObservation A D size last) {n}
    (a : Core A D n) (ρ : FiniteEnvironment size n) (t : Nat) : Bool :=
  (a.machine L F ρ).run t

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

-- [proof->req~behavioral-past-verification~1]
/-- Agreement includes mixed nesting and every captured environment. -/
theorem machine_agrees (L : Lasso C size last) (F : FiniteObservation A D size last)
    (O : Observation A D (Fin size)) (h : F.Agrees L O) {n} (a : Core A D n)
    (ρ : FiniteEnvironment size n) (t : Nat) :
    (a.machine L F ρ).run t = true ↔ a.eval L.unfold O ρ.realize t := by
  induction a generalizing t with
  | truth => rw [machine_eq]; simp [machineStep, eval]
  | atom a =>
    rw [machine_eq]
    cases a with
    | source a => exact h.atom a ρ t
    | parentPresent => exact L.parentPresent_agrees t ρ.this
    | contextPresent => rfl
    | starts => exact L.starts_agrees t ρ.this
    | ends => exact L.ends_agrees t ρ.this
  | not a ih =>
    rw [machine_eq]
    simpa [machineStep, eval] using not_congr (ih ρ t)
  | and a b ia ib =>
    rw [machine_eq]
    simp only [machineStep, FiniteMachine.run_map, FiniteMachine.run_pair, Bool.and_eq_true, eval, ia, ib]
  | or a b ia ib =>
    rw [machine_eq]
    simp only [machineStep, FiniteMachine.run_map, FiniteMachine.run_pair, Bool.or_eq_true, eval, ia, ib]
  | next a ih =>
    rw [machine_eq]
    simpa only [machineStep, FiniteMachine.run_next, eval, Temporal.next] using ih ρ (t + 1)
  | eventually a ih =>
    rw [machine_eq]
    simp only [machineStep, FiniteMachine.eventually_agrees, ih, eval, Temporal.eventually]
    exact exists_offset _ t
  | always a ih =>
    rw [machine_eq]
    simp only [machineStep, FiniteMachine.always_agrees, ih, eval, Temporal.always]
    exact all_offset _ t
  | strongUntil a b ia ib =>
    rw [machine_eq]
    simp only [machineStep, FiniteMachine.searchUntil_agrees, FiniteMachine.run_pair, ia, ib, eval]
    exact until_offset _ _ t
  | weakUntil a b ia ib =>
    rw [machine_eq]
    simp only [machineStep, FiniteMachine.run_map, FiniteMachine.run_pair, Bool.or_eq_true,
      FiniteMachine.always_agrees, FiniteMachine.searchUntil_agrees, ia, ib, eval,
      Temporal.weakUntil, ← until_offset, Temporal.always, ← all_offset]
  | previous a ih =>
    rw [machine_eq]
    simp only [machineStep, FiniteMachine.previous_agrees, eval]
    cases t <;> simp only [Temporal.previous, ih]
  | since a b ia ib =>
    rw [machine_eq]
    simp only [machineStep, FiniteMachine.since_agrees, FiniteMachine.run_pair, eval,
      Temporal.since, ia, ib]
  | quant q d a ih =>
    rw [machine_eq]
    simp only [machineStep, FiniteMachine.run_map, FiniteMachine.run_pair, run_clockMachine,
      Quantifier.finite_agrees, Quantifier.eval, FiniteMachine.run_family, eval, ih,
      FiniteEnvironment.realize_push, Finset.coe_singleton, ← h.domain d ρ t]
  | letSet d a ih =>
    rw [machine_eq]
    simp only [machineStep, FiniteMachine.run_map, FiniteMachine.run_pair, run_clockMachine,
      FiniteMachine.run_family, eval]
    simpa only [FiniteEnvironment.realize_push, h.domain, id_eq] using
      ih (ρ.push (F.domain d ρ (L.clock t))) t

-- [proof->req~behavioral-finite-checker~1]
theorem finite_agrees (L : Lasso C size last) (F : FiniteObservation A D size last)
    (O : Observation A D (Fin size)) (h : F.Agrees L O) {n} (a : Core A D n)
    (ρ : FiniteEnvironment size n) (t : Nat) :
    a.finite L F ρ t = true ↔ a.eval L.unfold O ρ.realize t :=
  machine_agrees L F O h a ρ t

-- [proof->req~behavioral-finite-checker~1]
theorem normalized_finite_agrees (L : Lasso C size last) (F : FiniteObservation A D size last)
    (O : Observation A D (Fin size)) (h : F.Agrees L O) {n} (a : Formula A D n)
    (sign : Bool) (ρ : FiniteEnvironment size n) (t : Nat) :
    (a.normalize sign).lower.finite L F ρ t = true ↔
      a.denote L.unfold O sign ρ.realize t :=
  (finite_agrees L F O h _ ρ t).trans (Formula.normalize_lower_agrees _ _ _ _ _ _)

end Core
end Clafer.Behavioral
