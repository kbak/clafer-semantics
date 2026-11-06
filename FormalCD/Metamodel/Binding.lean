module

public import FormalCD.Signature

/-!
# Full graph-binding data and its validation

SoSyM B.4 Definition 8 (PDF p.31). Candidate data can be malformed; validity is an
explicit incidence condition. All arity vertices and indexed arrow occurrences
are retained. No finite-arrow or no-isolated-vertex hypothesis is imposed.
-/

@[expose] public section

universe s va ua v u

namespace FormalCD.Metamodel
open CategoryTheory

abbrev ArrowData (G : Quiv.{v,u}) := Σ a b : G, (a ⟶ b)

-- [impl->req~formalcd-formula-identity~1]
structure Candidate (σ : DPGraph.Signature.{s,va,ua}) (G : Quiv.{v,u}) where
  symbol : σ.Symbol
  vertex : σ.arity symbol → G
  argument : ArrowData (σ.arity symbol) → ArrowData G

namespace Candidate
variable {σ : DPGraph.Signature.{s,va,ua}} {G : Quiv.{v,u}}

-- [impl->req~formalcd-metamodel-disciplines~1]
structure Valid (c : Candidate σ G) : Prop where
  source : ∀ e, (c.argument e).1 = c.vertex e.1
  target : ∀ e, (c.argument e).2.1 = c.vertex e.2.1

def ofFormula (f : DPGraph.Formula σ G) : Candidate σ G where
  symbol := f.symbol
  vertex := f.binding.obj
  argument e := ⟨f.binding.obj e.1, f.binding.obj e.2.1, f.binding.map e.2.2⟩

theorem ofFormula_valid (f : DPGraph.Formula σ G) : (ofFormula f).Valid :=
  ⟨fun _ => rfl, fun _ => rfl⟩

def toFormula (c : Candidate σ G) (h : c.Valid) : DPGraph.Formula σ G where
  symbol := c.symbol
  binding :=
    { obj := c.vertex
      map := fun {a b} e => Quiver.homOfEq (c.argument ⟨a,b,e⟩).2.2
        (h.source ⟨a,b,e⟩) (h.target ⟨a,b,e⟩) }

@[simp] theorem to_ofFormula (f : DPGraph.Formula σ G) :
    (ofFormula f).toFormula (ofFormula_valid f) = f := by cases f; rfl

private theorem transport_edge (e : ArrowData G) (a b : G)
    (hs : e.1 = a) (ht : e.2.1 = b) :
    (⟨a,b,Quiver.homOfEq e.2.2 hs ht⟩ : ArrowData G) = e := by
  cases hs; cases ht; rfl

@[simp] theorem of_toFormula (c : Candidate σ G) (h : c.Valid) :
    ofFormula (c.toFormula h) = c := by
  cases c with
  | mk p vertex argument =>
    change Candidate.mk p vertex _ = Candidate.mk p vertex argument
    congr 1
    funext e
    exact transport_edge (argument e) _ _ (h.source e) (h.target e)

/-- Validity is exactly the missing incidence condition, not an unexplained
assumption that every raw candidate already denotes a formula. -/
def formulaEquiv : {c : Candidate σ G // c.Valid} ≃ DPGraph.Formula σ G where
  toFun c := c.val.toFormula c.property
  invFun f := ⟨ofFormula f, ofFormula_valid f⟩
  left_inv c := Subtype.ext (of_toFormula c.val c.property)
  right_inv := to_ofFormula

-- [proof->req~formalcd-metamodel-disciplines~1]
theorem valid_iff_represents (c : Candidate σ G) :
    c.Valid ↔ ∃ f, ofFormula f = c := by
  constructor
  · intro h; exact ⟨c.toFormula h, of_toFormula c h⟩
  · rintro ⟨f, rfl⟩; exact ofFormula_valid f

end Candidate

/-- The authoritative equality is symbol plus full binding, including vertices. -/
theorem formula_ext {σ : DPGraph.Signature.{s,va,ua}} {G : Quiv.{v,u}}
    {f g : DPGraph.Formula σ G} (hs : f.symbol = g.symbol)
    (hb : HEq f.binding g.binding) : f = g := by
  cases f; cases g; cases hs; cases hb; rfl

theorem formula_binding_ext {σ : DPGraph.Signature.{s,va,ua}} {G : Quiv.{v,u}}
    (p : σ.Symbol) (b c : σ.arity p ⥤q G)
    (hv : b.obj = c.obj) (ha : HEq (@b.map) (@c.map)) :
    (⟨p,b⟩ : DPGraph.Formula σ G) = ⟨p,c⟩ := by
  cases b; cases c; cases hv; cases ha; rfl

-- [proof->req~formalcd-formula-identity~1]
/-- Equality of the full raw representation reflects and preserves formula identity. -/
theorem full_binding_identity {σ : DPGraph.Signature.{s,va,ua}} {G : Quiv.{v,u}}
    (f g : DPGraph.Formula σ G) : Candidate.ofFormula f = Candidate.ofFormula g ↔ f = g := by
  constructor
  · intro h
    have he : (⟨Candidate.ofFormula f, Candidate.ofFormula_valid f⟩ :
        {c : Candidate σ G // c.Valid}) = ⟨Candidate.ofFormula g, Candidate.ofFormula_valid g⟩ :=
      Subtype.ext h
    exact congrArg Candidate.formulaEquiv he
  · exact congrArg Candidate.ofFormula

end FormalCD.Metamodel
