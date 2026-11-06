module

public import FormalCD.Metamodel.Interpretation

/-! # Checked identity and projection boundaries (B.4 Definition 8)
These are finite formula/fiber witnesses, not a universal metamodel instance
construction. `ordered` has total args and fails the literal key; `repeated`
has total args and satisfies the key; `isolated` has empty args and fails both.
-/

@[expose] public section

namespace FormalCD.Metamodel.Examples
open CategoryTheory DPGraph DPGraph.Predicates

inductive Point where | point
  deriving DecidableEq
instance : Quiver Point := ⟨fun _ _ => Bool⟩
def loops : Quiv := Quiv.of Point

def loopSignature : Signature where
  Symbol := Bool
  arity _ := loops

def loopBinding (f : Bool → Bool) : loops ⥤q loops where
  obj _ := .point
  map e := f e

-- [impl->req~formalcd-metamodel-examples~1]
def ordered (b : Bool) : Formula loopSignature loops :=
  ⟨false, loopBinding (fun i => if b then !i else i)⟩

def repeated : Formula loopSignature loops := ⟨false, loopBinding (fun _ => true)⟩

theorem repeated_occurrences :
    repeated.binding.map (X := Point.point) (Y := Point.point) false =
      repeated.binding.map (X := Point.point) (Y := Point.point) true := rfl

def firstArg (f : Formula loopSignature loops) : Bool :=
  f.binding.map (X := Point.point) (Y := Point.point) false

theorem changed_position : ordered false ≠ ordered true := by
  intro h
  cases congrArg firstArg h

theorem changed_symbol :
    repeated ≠ (⟨true, repeated.binding⟩ : Formula loopSignature loops) := by
  intro h; cases congrArg Formula.symbol h

-- [proof->req~formalcd-formula-identity~1]
theorem reconstructed_identity :
    (Candidate.ofFormula (ordered false)).toFormula (Candidate.ofFormula_valid _) = ordered false :=
  Candidate.to_ofFormula _

/-- A malformed endpoint assignment, independent of Lean's typed map constructor. -/
def badIncidence : Candidate DPGraph.Predicates.signature Arity.unary where
  symbol := .total
  vertex _ := .target
  argument _ := ⟨.source, .target, Arity.UnaryEdge.arrow⟩

-- [proof->req~formalcd-metamodel-disciplines~1]
theorem bad_incidence_rejected : ¬ badIncidence.Valid := by
  intro h
  have hs := h.source ⟨.source, .target, Arity.UnaryEdge.arrow⟩
  cases hs

theorem bad_incidence_has_no_formula : ¬ ∃ f, Candidate.ofFormula f = badIncidence :=
  fun h => bad_incidence_rejected ((Candidate.valid_iff_represents _).mpr h)

/-- A finite family span retains its index even when values repeat. -/
def familySpan {A B I : Type} (f : A → I → B) : Span A B where
  Link := A × I
  source := Prod.fst
  target l := f l.1 l.2

def fiber {A B I : Type} (f : A → I → B) (a : A) :
    (familySpan f).toFamily.Index a ≃ I where
  toFun l := l.val.2
  invFun i := ⟨(a,i), rfl⟩
  left_inv := by rintro ⟨⟨a', i⟩, h⟩; cases h; rfl
  right_inv _ := rfl

def orderedArgs : Span Bool Bool := familySpan (fun b i : Bool => if b then !i else i)
def orderedPred : Span Bool Bool := familySpan (fun (_ : Bool) (_ : Unit) => false)

def flip : Bool ≃ Bool := ⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩

theorem ordered_args_projection (b i : Bool) :
    orderedArgs.target (b,i) = (ordered b).binding.map (X := Point.point) (Y := Point.point) i := rfl

theorem ordered_pred_projection (b : Bool) : orderedPred.target (b,()) = (ordered b).symbol := rfl

def orderedArgsBag : BagEquiv orderedArgs false true where
  equiv := (fiber _ false).trans (flip.trans (fiber _ true).symm)
  target_eq := by
    rintro ⟨⟨b,i⟩,h⟩
    cases h
    cases i <;> rfl

def orderedPredBag : BagEquiv orderedPred false true where
  equiv := (fiber _ false).trans (fiber _ true).symm
  target_eq _ := rfl

def orderedKeyFamily (i : Fin 2) : Span Bool Bool := if i = 0 then orderedArgs else orderedPred

theorem ordered_total : Total orderedArgs := by
  intro b; exact ⟨(b,false), rfl⟩

theorem unindexed_bag_forgets_position :
    ordered false ≠ ordered true ∧ Nonempty (BagEquiv orderedArgs false true) :=
  ⟨changed_position, ⟨orderedArgsBag⟩⟩

-- [proof->req~formalcd-metamodel-examples~1]
theorem ordered_literal_key_fails : ¬ Key orderedKeyFamily := by
  intro h
  have he := h false true (by
    intro i; fin_cases i
    · exact ⟨orderedArgsBag⟩
    · exact ⟨orderedPredBag⟩)
  cases he

def repeatedArgs : Span Unit Bool := familySpan (fun (_ : Unit) (_ : Bool) => true)
def repeatedPred : Span Unit Bool := familySpan (fun (_ : Unit) (_ : Unit) => false)
def repeatedKeyFamily (i : Fin 2) : Span Unit Bool := if i = 0 then repeatedArgs else repeatedPred

theorem repeated_total : Total repeatedArgs := by intro a; exact ⟨(a,false),rfl⟩
theorem repeated_literal_key : Key repeatedKeyFamily := by intro a b _; exact Subsingleton.elim a b

theorem repeated_not_setValued : ¬ SetValued repeatedArgs := by
  intro h
  have he := h (a₁ := ((),false)) (a₂ := ((),true)) rfl
  cases he

inductive Isolated where | left | right
  deriving DecidableEq
instance : Quiver Isolated := ⟨fun _ _ => Empty⟩
def isolatedGraph : Quiv := Quiv.of Isolated

def isolatedSignature : Signature where
  Symbol := Unit
  arity _ := isolatedGraph

def isolated (x : Isolated) : Formula isolatedSignature isolatedGraph :=
  ⟨(), { obj := fun _ => x, map := fun e => nomatch e }⟩

def isolatedImage (f : Formula isolatedSignature isolatedGraph) : Isolated := f.binding.obj .left

theorem changed_isolated_vertex : isolated .left ≠ isolated .right := by
  intro h
  cases congrArg isolatedImage h

theorem arrow_projection_forgets_isolated :
    (Candidate.ofFormula (isolated .left)).argument =
      (Candidate.ofFormula (isolated .right)).argument := by
  funext e; exact e.2.2.elim

theorem empty_arity_valid : (Candidate.ofFormula (isolated .left)).Valid :=
  Candidate.ofFormula_valid _

def isolatedArgs : Span Bool Bool := familySpan (fun (_ : Bool) (i : Empty) => i.elim)

def isolatedBag : BagEquiv isolatedArgs false true where
  equiv := (fiber _ false).trans (fiber _ true).symm
  target_eq l := l.val.2.elim

def isolatedKeyFamily (i : Fin 2) : Span Bool Bool := if i = 0 then isolatedArgs else orderedPred

theorem isolated_not_total : ¬ Total isolatedArgs := by
  intro h; obtain ⟨l,_⟩ := h false; exact l.2.elim

theorem isolated_literal_key_fails : ¬ Key isolatedKeyFamily := by
  intro h
  have he := h false true (by
    intro i; fin_cases i
    · exact ⟨isolatedBag⟩
    · exact ⟨orderedPredBag⟩)
  cases he

end FormalCD.Metamodel.Examples
