module

public import Clafer.Behavioral.PartialCompatibility

/-! # Six scoped temporal patterns

Behavioral §§4.2/6.1 and T2/T9; the complete thirty-cell source contract.
The signed interval algebra below quantifies over times and uninterrupted parent
lifetimes independently of Formula, expansion, normalization and the compiler.
The resolved expansion is a separate syntax transformation. Two reviewed D2
corrections require responses throughout a completed interval and prohibit
skipping the first opener for after-precedence.
-/

@[expose] public section
namespace Clafer.Behavioral.Patterns
universe u
variable {A D : Nat → Type} {C : Type} {U : Type u} {n : Nat}

inductive Scope (F : Type) where
  | suffix | before (r : F) | after (q : F) | between (q r : F) | afterUntil (q r : F)

inductive Pattern (F : Type) where
  | never (p : F) | sometime (p : F) | lonce (p : F) | always (p : F)
  | precede (s p : F) | follow (s p : F)

abbrev Judgment := Bool → Signal

namespace Interval
def neg (a : Judgment) : Judgment := fun s => a (!s)
def both (a b : Judgment) : Judgment := fun s t =>
  if s then a true t ∧ b true t else a false t ∨ b false t
def either (a b : Judgment) : Judgment := fun s t =>
  if s then a true t ∨ b true t else a false t ∧ b false t
def implies (a b : Judgment) : Judgment := fun s t =>
  if s then a false t ∨ b true t else a true t ∧ b false t

/-- Inclusive live interval; a gap is never bridged by reappearance. -/
def active (P : Signal) (i j : Nat) : Prop := ∀ k, i ≤ k → k ≤ j → P k
def throughout (P a : Signal) (i : Nat) : Prop := ∀ j, i ≤ j → active P i j → a j
def reaches (P a : Signal) (i : Nat) : Prop :=
  (∃ j, i ≤ j ∧ ¬ P j) ∨ ∃ j, i ≤ j ∧ active P i j ∧ a j
def segment (P a b : Signal) (i : Nat) : Prop :=
  ∃ j, i ≤ j ∧ (¬ P j ∨ b j) ∧ ∀ k, i ≤ k → k < j → P k ∧ a k
def openSegment (P a b : Signal) (i : Nat) : Prop := throughout P a i ∨ segment P a b i

def all (P : Signal) (a : Judgment) : Judgment := fun s =>
  if s then throughout P (a true) else reaches P (a false)
def eventual (P : Signal) (a : Judgment) : Judgment := fun s =>
  if s then reaches P (a true) else throughout P (a false)
def strong (P : Signal) (a b : Judgment) : Judgment := fun s =>
  if s then segment P (a true) (b true)
  else openSegment P (b false) (fun j => a false j ∧ b false j)
def weak (P : Signal) (a b : Judgment) : Judgment := fun s =>
  if s then openSegment P (a true) (b true)
  else segment P (b false) (fun j => a false j ∧ b false j)
end Interval

-- [impl->req~behavioral-patterns~1]
/-- Independent interval meaning. Operands carry both source judgments: scope
premises such as F r use their negative judgment in an implication, not the
classical negation of positive bounded eventuality. -/
def meaning (P : Signal) (pattern : Pattern Judgment) (scope : Scope Judgment) : Judgment :=
  let g := Interval.all P
  let f := Interval.eventual P
  let u := Interval.strong P
  let w := Interval.weak P
  let no := Interval.neg
  let a := Interval.both
  let o := Interval.either
  let imp := Interval.implies
  match pattern, scope with
  | .never p, .suffix => g (no p)
  | .never p, .before r => imp (f r) (u (no p) r)
  | .never p, .after q => g (imp q (g (no p)))
  | .never p, .between q r => g (imp (a (a q (no r)) (f r)) (u (no p) r))
  | .never p, .afterUntil q r => g (imp (a q (no r)) (w (no p) r))
  | .sometime p, .suffix => f p
  | .sometime p, .before r => w (no r) (a p (no r))
  | .sometime p, .after q => o (g (no q)) (f (a q (f p)))
  | .sometime p, .between q r => g (imp (a q (no r)) (w (no r) (a p (no r))))
  | .sometime p, .afterUntil q r => g (imp (a q (no r)) (u (no r) (a p (no r))))
  | .lonce p, .suffix => w (no p) (w p (g (no p)))
  | .lonce p, .before r => imp (f r) (u (a (no p) (no r)) (o r (u (a p (no r)) (o r (u (no p) r)))))
  | .lonce p, .after q => imp (f q) (u (no q) (a q (w (no p) (w p (g (no p))))))
  | .lonce p, .between q r => g (imp (a q (f r))
      (u (a (no p) (no r)) (o r (u (a p (no r)) (o r (u (no p) r))))))
  | .lonce p, .afterUntil q r => g (imp q
      (u (a (no p) (no r)) (o r (u (a p (no r)) (o (o r (w (no p) r)) (g p))))))
  | .always p, .suffix => g p
  | .always p, .before r => imp (f r) (u p r)
  | .always p, .after q => g (imp q (g p))
  | .always p, .between q r => g (imp (a (a q (no r)) (f r)) (u p r))
  | .always p, .afterUntil q r => g (imp (a q (no r)) (w p r))
  | .precede s p, .suffix => w (no p) s
  | .precede s p, .before r => imp (f r) (u (no p) (o s r))
  | .precede s p, .after q => imp (f q) (u (no q) (a q (w (no p) s)))
  | .precede s p, .between q r => g (imp (a (a q (no r)) (f r)) (u (no p) (o s r)))
  | .precede s p, .afterUntil q r => g (imp (a q (no r)) (w (no p) (o s r)))
  | .follow s p, .suffix => g (imp p (f s))
  | .follow s p, .before r => imp (f r) (u (imp p (u (no r) (a s (no r)))) r)
  | .follow s p, .after q => g (imp q (g (imp p (f s))))
  | .follow s p, .between q r => g (imp (a (a q (no r)) (f r))
      (u (imp p (u (no r) (a s (no r)))) r))
  | .follow s p, .afterUntil q r => g (imp (a q (no r)) (w (imp p (u (no r) (a s (no r)))) r))

-- [impl->req~behavioral-patterns~1]
/-- Resolved source syntax only. This transformation has no parser or backend
dependency and never consults the interval interpretation. -/
def expand (pattern : Pattern (Formula A D n)) (scope : Scope (Formula A D n)) : Formula A D n :=
  let g := Formula.always
  let f := Formula.eventually
  let u := Formula.strongUntil
  let w := Formula.weakUntil
  let no := Formula.not
  let a := Formula.and
  let o := Formula.or
  let imp := Formula.implies
  match pattern, scope with
  | .never p, .suffix => g (no p)
  | .never p, .before r => imp (f r) (u (no p) r)
  | .never p, .after q => g (imp q (g (no p)))
  | .never p, .between q r => g (imp (a (a q (no r)) (f r)) (u (no p) r))
  | .never p, .afterUntil q r => g (imp (a q (no r)) (w (no p) r))
  | .sometime p, .suffix => f p
  | .sometime p, .before r => w (no r) (a p (no r))
  | .sometime p, .after q => o (g (no q)) (f (a q (f p)))
  | .sometime p, .between q r => g (imp (a q (no r)) (w (no r) (a p (no r))))
  | .sometime p, .afterUntil q r => g (imp (a q (no r)) (u (no r) (a p (no r))))
  | .lonce p, .suffix => w (no p) (w p (g (no p)))
  | .lonce p, .before r => imp (f r) (u (a (no p) (no r)) (o r (u (a p (no r)) (o r (u (no p) r)))))
  | .lonce p, .after q => imp (f q) (u (no q) (a q (w (no p) (w p (g (no p))))))
  | .lonce p, .between q r => g (imp (a q (f r))
      (u (a (no p) (no r)) (o r (u (a p (no r)) (o r (u (no p) r))))))
  | .lonce p, .afterUntil q r => g (imp q
      (u (a (no p) (no r)) (o r (u (a p (no r)) (o (o r (w (no p) r)) (g p))))))
  | .always p, .suffix => g p
  | .always p, .before r => imp (f r) (u p r)
  | .always p, .after q => g (imp q (g p))
  | .always p, .between q r => g (imp (a (a q (no r)) (f r)) (u p r))
  | .always p, .afterUntil q r => g (imp (a q (no r)) (w p r))
  | .precede s p, .suffix => w (no p) s
  | .precede s p, .before r => imp (f r) (u (no p) (o s r))
  | .precede s p, .after q => imp (f q) (u (no q) (a q (w (no p) s)))
  | .precede s p, .between q r => g (imp (a (a q (no r)) (f r)) (u (no p) (o s r)))
  | .precede s p, .afterUntil q r => g (imp (a q (no r)) (w (no p) (o s r)))
  | .follow s p, .suffix => g (imp p (f s))
  | .follow s p, .before r => imp (f r) (u (imp p (u (no r) (a s (no r)))) r)
  | .follow s p, .after q => g (imp q (g (imp p (f s))))
  | .follow s p, .between q r => g (imp (a (a q (no r)) (f r))
      (u (imp p (u (no r) (a s (no r)))) r))
  | .follow s p, .afterUntil q r => g (imp (a q (no r)) (w (imp p (u (no r) (a s (no r)))) r))

def Pattern.map {F G : Type} (f : F → G) : Pattern F → Pattern G
  | .never p => .never (f p) | .sometime p => .sometime (f p)
  | .lonce p => .lonce (f p) | .always p => .always (f p)
  | .precede s p => .precede (f s) (f p) | .follow s p => .follow (f s) (f p)

def Scope.map {F G : Type} (f : F → G) : Scope F → Scope G
  | .suffix => .suffix | .before r => .before (f r) | .after q => .after (f q)
  | .between q r => .between (f q) (f r) | .afterUntil q r => .afterUntil (f q) (f r)

-- [proof->req~behavioral-patterns~1]
/-- All thirty cases, both signs, arbitrary temporal operands and environments.
No classical-complement assumption on an operand's two judgments is required. -/
theorem expand_agrees (τ : Trace C U) (O : Observation A D U)
    (pattern : Pattern (Formula A D n)) (scope : Scope (Formula A D n)) (ρ) (s) (t) :
    (expand pattern scope).denote τ O s ρ t ↔
      meaning (τ.ParentPresent ρ.this)
        (pattern.map (fun a s => a.denote τ O s ρ))
        (scope.map (fun a s => a.denote τ O s ρ)) s t := by
  cases pattern <;> cases scope <;> cases s <;> rfl

theorem lower_agrees (τ : Trace C U) (O : Observation A D U)
    (pattern : Pattern (Formula A D n)) (scope : Scope (Formula A D n)) (ρ) (s) (t) :
    ((expand pattern scope).normalize s).lower.eval τ O ρ t ↔
      meaning (τ.ParentPresent ρ.this)
        (pattern.map (fun a s => a.denote τ O s ρ))
        (scope.map (fun a s => a.denote τ O s ρ)) s t := by
  rw [Formula.normalize_lower_agrees, expand_agrees]

theorem partial_agrees (τ : Trace C U) (O : PartialObservation A D U)
    (pattern : Pattern (Formula A D n)) (scope : Scope (Formula A D n)) (ρ) (s) (t) :
    (expand pattern scope).Satisfies τ O s ρ t ↔
      (expand pattern scope).Defined τ O ρ t ∧
      meaning (τ.ParentPresent ρ.this)
        (pattern.map (fun a s => a.denote τ O.canonical s ρ))
        (scope.map (fun a s => a.denote τ O.canonical s ρ)) s t := by
  rw [Formula.Satisfies, expand_agrees]


/-- On an uninterrupted parent interval and classical event signals, the
corrected response clause says exactly that every trigger before the first r
has a response before that r. This characterization does not use the expander. -/
-- [proof->req~behavioral-patterns~1]
theorem response_interval (p s r : Signal) (i close : Nat) (hic : i ≤ close)
    (closing : r close) (first : ∀ k, i ≤ k → k < close → ¬ r k) :
    Interval.segment (fun _ => True)
      (fun k => p k → Interval.segment (fun _ => True) (fun j => ¬ r j)
        (fun j => s j ∧ ¬ r j) k) r i ↔
      ∀ k, i ≤ k → k < close → p k → ∃ j, k ≤ j ∧ j < close ∧ s j := by
  constructor
  · rintro ⟨stop, his, terminal, body⟩ k hik hkc hp
    have rs : r stop := terminal.resolve_left (by simp)
    have hcs : close ≤ stop := by
      by_contra h
      exact first stop his (by omega) rs
    obtain ⟨j, hkj, finish, prior⟩ := (body k hik (by omega)).2 hp
    have finish' : s j ∧ ¬ r j := finish.resolve_left (by simp)
    have hjc : j < close := by
      by_contra h
      by_cases he : j = close
      · exact finish'.2 (he ▸ closing)
      · exact (prior close (by omega) (by omega)).2 closing
    exact ⟨j, hkj, hjc, finish'.1⟩
  · intro responses
    refine ⟨close, hic, Or.inr closing, ?_⟩
    intro k hik hkc
    refine ⟨trivial, ?_⟩
    intro hp
    obtain ⟨j, hkj, hjc, hs⟩ := responses k hik hkc hp
    refine ⟨j, hkj, Or.inr ⟨hs, first j (by omega) hjc⟩, ?_⟩
    intro z hkz hzj
    exact ⟨trivial, first z (by omega) (by omega)⟩

/-- The after-precedence search cannot cross the first opener. The target
property at that opener may itself contain any temporal meaning. -/
theorem first_opener (q property : Signal) (i opening : Nat) (hio : i ≤ opening)
    (atOpening : q opening) (first : ∀ k, i ≤ k → k < opening → ¬ q k) :
    Interval.segment (fun _ => True) (fun k => ¬ q k)
      (fun k => q k ∧ property k) i ↔ property opening := by
  constructor
  · rintro ⟨j, hij, terminal, prior⟩
    have finish : q j ∧ property j := terminal.resolve_left (by simp)
    have he : j = opening := by
      by_contra h
      rcases lt_or_gt_of_ne h with hj | hj
      · exact first j hij hj finish.1
      · exact (prior opening hio hj).2 atOpening
    exact he ▸ finish.2
  · intro h
    exact ⟨opening, hio, Or.inr ⟨atOpening, h⟩,
      fun k hik hko => ⟨trivial, first k hik hko⟩⟩

end Clafer.Behavioral.Patterns
