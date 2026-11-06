module

public import DPGraph.Span.IndexedFamily

/-!
# Pullback composition

SoSyM B.2.1: composition is in source-to-target order and retains all compatible
link pairs. Units and associativity are isomorphisms of heads. A composite head
has universe `max w w'`; associativity uses the join of all three link universes.
-/

@[expose] public section

universe u v z t w w' w''

namespace DPGraph
namespace Span

variable {A : Type u} {B : Type v} {C : Type z} {D : Type t}

-- [impl->req~span-composition~1]
def comp (q : Span.{u, v, w} A B) (r : Span.{v, z, w'} B C) :
    Span.{u, z, max w w'} A C where
  Link := { p : q.Link × r.Link // q.target p.1 = r.source p.2 }
  source p := q.source p.1.1
  target p := r.target p.1.2

/-- Pullback composition retains isomorphisms of both link types (B.2.1). -/
def Iso.comp {q : Span.{u, v, w} A B} {q' : Span.{u, v, w'} A B}
    {r : Span.{v, z, w''} B C} {r' : Span.{v, z, t} B C}
    (e : Iso q q') (f : Iso r r') : Iso (q.comp r) (q'.comp r') where
  equiv :=
    { toFun := fun p => ⟨(e.equiv p.1.1, f.equiv p.1.2),
        (e.target_eq _).trans (p.2.trans (f.source_eq _).symm)⟩
      invFun := fun p => ⟨(e.equiv.symm p.1.1, f.equiv.symm p.1.2),
        (e.symm.target_eq _).trans (p.2.trans (f.symm.source_eq _).symm)⟩
      left_inv := fun p => Subtype.ext (Prod.ext (e.equiv.left_inv p.1.1) (f.equiv.left_inv p.1.2))
      right_inv := fun p => Subtype.ext (Prod.ext (e.equiv.right_inv p.1.1) (f.equiv.right_inv p.1.2)) }
  source_eq p := e.source_eq p.1.1
  target_eq p := f.target_eq p.1.2

/-- Identity links are the objects themselves. -/
def identity (A : Type u) : Span.{u, u, u} A A where
  Link := A
  source a := a
  target a := a

def leftUnit (q : Span.{u, v, w} A B) : Iso ((identity A).comp q) q where
  equiv :=
    { toFun := fun p => p.1.2
      invFun := fun l => ⟨(q.source l, l), rfl⟩
      left_inv := fun p => Subtype.ext (Prod.ext p.2.symm rfl)
      right_inv := fun _ => rfl }
  source_eq p := p.2.symm
  target_eq _ := rfl

def rightUnit (q : Span.{u, v, w} A B) : Iso (q.comp (identity B)) q where
  equiv :=
    { toFun := fun p => p.1.1
      invFun := fun l => ⟨(l, q.target l), rfl⟩
      left_inv := fun p => Subtype.ext (Prod.ext rfl p.2)
      right_inv := fun _ => rfl }
  source_eq _ := rfl
  target_eq p := p.2

-- [proof->req~span-composition~1]
/-- The canonical reassociation `((l,m),n) ↦ (l,(m,n))`. -/
def associator (q : Span.{u, v, w} A B) (r : Span.{v, z, w'} B C)
    (s : Span.{z, t, w''} C D) : Iso ((q.comp r).comp s) (q.comp (r.comp s)) where
  equiv :=
    { toFun := fun p => ⟨(p.1.1.1.1, ⟨(p.1.1.1.2, p.1.2), p.2⟩), p.1.1.2⟩
      invFun := fun p => ⟨(⟨(p.1.1, p.1.2.1.1), p.2⟩, p.1.2.1.2), p.1.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  source_eq _ := rfl
  target_eq _ := rfl

end Span

namespace IndexedFamily

variable {A : Type u} {B : Type v} {C : Type z}

/-- All pairs of indices are retained, including repeated evaluations. -/
def comp (f : IndexedFamily.{u, v, w} A B) (g : IndexedFamily.{v, z, w'} B C) :
    IndexedFamily.{u, z, max w w'} A C where
  Index a := Σ i : f.Index a, g.Index (f.eval a i)
  eval a p := g.eval (f.eval a p.1) p.2

/-- Family composition and pullback composition give isomorphic spans. -/
def compSpanIso (f : IndexedFamily.{u, v, w} A B)
    (g : IndexedFamily.{v, z, w'} B C) :
    Span.Iso (f.comp g).toSpan (f.toSpan.comp g.toSpan) where
  equiv :=
    { toFun := fun p => ⟨(⟨p.1, p.2.1⟩, ⟨f.eval p.1 p.2.1, p.2.2⟩), rfl⟩
      invFun := fun p => ⟨p.1.1.1, ⟨p.1.1.2, cast (congrArg g.Index p.2.symm) p.1.2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨⟨a, i⟩, ⟨b, j⟩⟩, h⟩
        change f.eval a i = b at h
        cases h
        rfl }
  source_eq _ := rfl
  target_eq _ := rfl

end IndexedFamily

namespace Span

variable {A : Type u} {B : Type v} {C : Type z}

/-- Equivalently, source fibers of the pullback are composed family indices. -/
def compFamilyEquivalence (q : Span.{u, v, w} A B) (r : Span.{v, z, w'} B C) :
    IndexedFamily.Equivalence (q.comp r).toFamily (q.toFamily.comp r.toFamily) where
  equiv _a :=
    { toFun := fun p => ⟨⟨p.1.1.1, p.2⟩, ⟨p.1.1.2, p.1.2.symm⟩⟩
      invFun := fun p => ⟨⟨(p.1.1, p.2.1), p.2.2.symm⟩, p.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  eval_eq _ _ := rfl

end Span
end DPGraph
