module

public import Mathlib.Logic.Equiv.Basic

/-!
[impl->req~span-inversion~1]
[impl->req~span-representation~1]
[impl->req~span-set-valuedness~1]
[proof->req~span-inversion~1]
[proof->req~span-representation~1]
-/

/-!
# Spans and head isomorphisms

SoSyM Appendix B.1, Definitions 1–5. Links carry identity independently of
endpoints. The endpoint and link universes are independent. B.2.2 inversion
swaps legs; it does not assert categorical invertibility.
-/

@[expose] public section

universe u v w w' w''

namespace DPGraph

/-- A mapping with individually identifiable links (SoSyM B.1). -/
structure Span (A : Type u) (B : Type v) where
  Link : Type w
  source : Link → A
  target : Link → B

namespace Span

variable {A : Type u} {B : Type v}

/-- An ordinary function as a B.1 span, with exactly one link at each source. -/
def ofFunction (f : A → B) : Span.{u, v, u} A B where
  Link := A
  source := id
  target := f

/-- A head equivalence commuting with both legs, even across head universes. -/
structure Iso (q : Span.{u, v, w} A B) (r : Span.{u, v, w'} A B) where
  equiv : q.Link ≃ r.Link
  source_eq : ∀ l, r.source (equiv l) = q.source l
  target_eq : ∀ l, r.target (equiv l) = q.target l

namespace Iso

variable {q : Span.{u, v, w} A B} {r : Span.{u, v, w'} A B}
  {s : Span.{u, v, w''} A B}

def refl (q : Span.{u, v, w} A B) : Iso q q where
  equiv := Equiv.refl _
  source_eq _ := rfl
  target_eq _ := rfl

def symm (e : Iso q r) : Iso r q where
  equiv := e.equiv.symm
  source_eq l := by simpa using (e.source_eq (e.equiv.symm l)).symm
  target_eq l := by simpa using (e.target_eq (e.equiv.symm l)).symm

def trans (e : Iso q r) (f : Iso r s) : Iso q s where
  equiv := e.equiv.trans f.equiv
  source_eq l := (f.source_eq (e.equiv l)).trans (e.source_eq l)
  target_eq l := (f.target_eq (e.equiv l)).trans (e.target_eq l)

end Iso

/-- Existential endpoint membership forgets link multiplicity (B.1). -/
def red (q : Span.{u, v, w} A B) (a : A) (b : B) : Prop :=
  ∃ l, q.source l = a ∧ q.target l = b

/-- Set-valuedness means joint injectivity, not injectivity of either leg. -/
def JointlyInjective (q : Span.{u, v, w} A B) : Prop :=
  Function.Injective (fun l => (q.source l, q.target l))

theorem Iso.red_eq {q : Span.{u, v, w} A B} {r : Span.{u, v, w'} A B}
    (e : Iso q r) : q.red = r.red := by
  funext a b
  apply propext
  constructor
  · rintro ⟨l, hs, ht⟩
    exact ⟨e.equiv l, (e.source_eq l).trans hs, (e.target_eq l).trans ht⟩
  · rintro ⟨l, hs, ht⟩
    exact ⟨e.equiv.symm l, (e.symm.source_eq l).trans hs,
      (e.symm.target_eq l).trans ht⟩

/-- Inversion retains every link (SoSyM B.2.2). -/
def inverse (q : Span.{u, v, w} A B) : Span.{v, u, w} B A where
  Link := q.Link
  source := q.target
  target := q.source

@[simp] theorem inverse_inverse (q : Span.{u, v, w} A B) :
    q.inverse.inverse = q := rfl

theorem red_inverse (q : Span.{u, v, w} A B) (b : B) (a : A) :
    q.inverse.red b a ↔ q.red a b := by
  constructor <;> rintro ⟨l, h₁, h₂⟩ <;> exact ⟨l, h₂, h₁⟩

/-- Relabeling commutes with leg-swapping inversion (B.2.2). -/
def Iso.inverse {q : Span.{u, v, w} A B} {r : Span.{u, v, w'} A B}
    (e : Iso q r) : Iso q.inverse r.inverse where
  equiv := e.equiv
  source_eq := e.target_eq
  target_eq := e.source_eq

end Span
end DPGraph
