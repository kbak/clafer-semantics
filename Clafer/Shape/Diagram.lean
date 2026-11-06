module

public import Clafer.Shape

/-!
# Local diagram predicates of an individual Shape

SoSyM Figure 16/Table 4 (PDF pp.14–15). This local CD uses role labels for source/target;
cojoining, inherited constraints, abstract cover/disjointness and global label
identification belong to MCS/Compile/gluing. No model-existence claim is made.
-/

@[expose] public section
namespace Clafer.Shape
open CategoryTheory DPGraph.Predicates Roles

def sourceClass (s : Shape) (h : s.hasParent = true) : s.carrier := ⟨.source, h⟩
def targetClass (s : Shape) (h : s.kind ≠ .basic) : s.carrier :=
  ⟨.target, by simpa [classPresent] using h⟩

def headArrow (s : Shape) (h : s.hasParent = true) :
    sourceClass s h ⟶ head s.kind s.hasParent := ⟨.head, h, rfl, rfl⟩
def parentArrow (s : Shape) (h : s.hasParent = true) :
    head s.kind s.hasParent ⟶ sourceClass s h := ⟨.parent, h, rfl, rfl⟩
def derefArrow (s : Shape) (h : s.kind ≠ .basic) :
    head s.kind s.hasParent ⟶ targetClass s h :=
  ⟨.dereference, by simpa [mapPresent] using h, rfl, rfl⟩
def targetArrow (s : Shape) (hp : s.hasParent = true) (ht : s.kind ≠ .basic) :
    sourceClass s hp ⟶ targetClass s ht :=
  ⟨.target, by simp [mapPresent, hp, ht], rfl, rfl⟩

def inverseBinding (s : Shape) (hp : s.hasParent = true) : Arity.opposite ⥤q s.carrier where
  obj | .left => sourceClass s hp | .right => head s.kind s.hasParent
  map | .forward => headArrow s hp | .backward => parentArrow s hp

def triangleBinding (s : Shape) (hp : s.hasParent = true) (ht : s.kind ≠ .basic) :
    Arity.triangle ⥤q s.carrier where
  obj | .first => sourceClass s hp | .middle => head s.kind s.hasParent
      | .last => targetClass s ht
  map | .first => headArrow s hp | .second => derefArrow s ht | .direct => targetArrow s hp ht

def keyBinding (s : Shape) (hp : s.hasParent = true) (ht : s.kind ≠ .basic) :
    Arity.fanOut 2 ⥤q s.carrier where
  obj
    | .center => head s.kind s.hasParent
    | .member i => if i = 0 then sourceClass s hp else targetClass s ht
  map := by
    intro a b e
    cases e with
    | edge i =>
      change head s.kind s.hasParent ⟶ (if i = 0 then sourceClass s hp else targetClass s ht)
      by_cases hi : i = 0
      · simpa [hi] using parentArrow s hp
      · simpa [hi] using derefArrow s ht

-- [impl->req~clafer-individual-shapes~1]
/-- Effective local declarations, including the set-reference key only when
both projections exist. A bag target receives no ordinary set-valued default. -/
def declarations (s : Shape) : Set (DPGraph.Formula signature s.carrier) :=
  {φ |
    (∃ (a b : s.carrier) (e : a ⟶ b), mode s.kind e.val = .ordinary ∧
      φ = FormalCD.setValuedFormula e) ∨
    (∃ m : Map s.kind s.hasParent, (m.val = .head ∨ m.val = .target) ∧
      φ = ⟨.targetMultiplicity s.multiplicity, FormalCD.arrowBinding (arrow m)⟩) ∨
    (∃ m : Map s.kind s.hasParent, (m.val = .parent ∨ m.val = .dereference) ∧
      φ = ⟨.targetMultiplicity one, FormalCD.arrowBinding (arrow m)⟩) ∨
    (∃ hp, φ = ⟨.inverse, inverseBinding s hp⟩) ∨
    (∃ hp ht, φ = ⟨.commutation, triangleBinding s hp ht⟩) ∨
    (s.kind = .referenceSet ∧ ∃ hp ht, φ = ⟨.key 2, keyBinding s hp ht⟩)}

/-- A local role vocabulary, with no primitive-domain interpretation attached. -/
def roleRegistry : FormalCD.Registry where
  Id := Empty
  name := Empty.elim
  kind := Empty.elim

def raw (s : Shape) : FormalCD.Raw roleRegistry where
  carrier := s.carrier
  declarations := declarations s
  className c := match c.val with
    | .head => s.name | .source => "source" | .target => "target"
  mapName e := match e.val with
    | .head => s.name | .parent => "parent" | .dereference => "dref" | .target => s.name ++ "*"
  predefined _ := none
  mode e := mode s.kind e.val

-- [proof->req~clafer-individual-shapes~1]
theorem raw_wellFormed (s : Shape) : (raw s).WellFormed where
  predefined_name := by intro c i; exact Empty.elim i
  user_name := by rintro c _ ⟨i, _⟩; exact Empty.elim i
  unique_predefined := by intro c d i; exact Empty.elim i
  inclusion_name := by
    intro a b e he
    simp only [raw, mode] at he
    split at he <;> contradiction
  inclusion_decl := by
    intro a b e he
    simp only [raw, mode] at he
    split at he <;> contradiction
  ordinary_decl := by
    intro a b e he
    exact Or.inl ⟨a, b, e, he, rfl⟩

def diagram (s : Shape) : FormalCD.CD roleRegistry := ⟨raw s, raw_wellFormed s⟩

def realization (s : Shape) : s.Realization (raw s) where
  binding := Prefunctor.id s.carrier
  modes _ := rfl

theorem inverse_declared (s : Shape) (hp : s.hasParent = true) :
    (⟨.inverse, inverseBinding s hp⟩ : DPGraph.Formula signature s.carrier) ∈ declarations s :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, rfl⟩)))

theorem key_declared (s : Shape) (hk : s.kind = .referenceSet) (hp : s.hasParent = true) :
    (⟨.key 2, keyBinding s hp (by simp [hk])⟩ : DPGraph.Formula signature s.carrier) ∈
      declarations s :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hk, hp, by simp [hk], rfl⟩))))

theorem key_conditions (s : Shape) (φ : DPGraph.Formula signature s.carrier)
    (h : φ ∈ declarations s) (hk : φ.symbol = .key 2) :
    s.kind = .referenceSet ∧ s.hasParent = true := by
  rcases h with h | h | h | h | h | h
  · rcases h with ⟨a, b, e, _, rfl⟩; cases hk
  · rcases h with ⟨m, _, rfl⟩; cases hk
  · rcases h with ⟨m, _, rfl⟩; cases hk
  · rcases h with ⟨hp, rfl⟩; cases hk
  · rcases h with ⟨hp, ht, rfl⟩; cases hk
  · exact ⟨h.1, h.2.choose⟩

end Clafer.Shape
