module

public import Clafer.MCS.Laws

/-!
[impl->req~clafer-compile-formulas~1]
[proof->req~clafer-compile-formulas~1]
-/

/-!
# Generated local declarations

SoSyM Figure 16/Table 4, §5.5 and §6.2.4. One canonical occurrence is generated
for each applicable local predicate, plus an inclusion predicate for each super
slot. The literal bag key is proved from map-role identity, not assumed or
replaced by equality of ordered argument lists.
-/

@[expose] public section
namespace Clafer.Compile
open CategoryTheory Clafer.Roles MCS DPGraph.Predicates

variable {C : Type} (f : Family C)

inductive LocalId where
  | setValued (c : C) (m : Map (f.shape c).kind (f.shape c).hasParent)
      (ordinary : mode (f.shape c).kind m.val = .ordinary)
  | multiplicity (c : C) (m : Map (f.shape c).kind (f.shape c).hasParent)
  | inclusion (i : f.InclusionSlot)
  | inverse (c : C) (parent : (f.shape c).hasParent = true)
  | commutation (c : C) (parent : (f.shape c).hasParent = true)
      (reference : (f.shape c).kind ≠ .basic)
  | key (c : C) (set : (f.shape c).kind = .referenceSet)
      (parent : (f.shape c).hasParent = true)

namespace LocalId
variable {f}

def owner : LocalId f → C
  | .setValued c _ _ | .multiplicity c _ | .inverse c _ | .commutation c _ _ | .key c _ _ => c
  | .inclusion i => i.1

def edge (m : f.MapId) : f.canonicalRoles.Arrow
    (f.canonicalRoles.source m) (f.canonicalRoles.target m) := ⟨m, rfl, rfl⟩

def range (c : C) (m : Map (f.shape c).kind (f.shape c).hasParent) : Range :=
  match m.val with
  | .head | .target => f.multiplicity c
  | .parent | .dereference => Clafer.one

def formula : LocalId f → DPGraph.Formula signature f.canonicalRoles.graph
  | .setValued c m _ => FormalCD.setValuedFormula
      (G := f.canonicalRoles.graph) (edge (.ordinary c m))
  | .multiplicity c m => ⟨.targetMultiplicity (range c m),
      FormalCD.arrowBinding (G := f.canonicalRoles.graph) (edge (.ordinary c m))⟩
  | .inclusion i => FormalCD.inclusionFormula (G := f.canonicalRoles.graph) (edge (.inclusion i))
  | .inverse c hp => (⟨.inverse, Shape.inverseBinding (f.shape c) hp⟩ :
      DPGraph.Formula signature _).translate (f.canonicalRoles.binding c)
  | .commutation c hp ht => (⟨.commutation, Shape.triangleBinding (f.shape c) hp ht⟩ :
      DPGraph.Formula signature _).translate (f.canonicalRoles.binding c)
  | .key c hk hp => (⟨.key 2, Shape.keyBinding (f.shape c) hp (by simp [hk])⟩ :
      DPGraph.Formula signature _).translate (f.canonicalRoles.binding c)

end LocalId

def localFormulas : Formulas f.canonicalRoles signature where
  Id := LocalId f
  owner := LocalId.owner
  formula := LocalId.formula

namespace LocalId
variable {f}

def arg (i : LocalId f) : (localFormulas f).Arg i := by
  cases i with
  | setValued | multiplicity | inclusion => exact ⟨.source, .target, .arrow⟩
  | inverse => exact ⟨.left, .right, .forward⟩
  | commutation => exact ⟨.first, .middle, .first⟩
  | key => exact ⟨.center, .member 0, .edge 0⟩

theorem argument_owner (i : LocalId f) (a : (localFormulas f).Arg i) :
    ((localFormulas f).argument i a).2.2.val.owner = i.owner := by
  cases i <;> rcases a with ⟨a, b, e⟩
  all_goals first
    | (change Arity.UnaryEdge a b at e; cases e; rfl)
    | (change Arity.OppositeEdge a b at e; cases e <;> rfl)
    | (change Arity.TriangleEdge a b at e; cases e <;> rfl)
    | (change Arity.OutEdge 2 a b at e; cases e; simp [localFormulas,
        Formulas.argument, formula, DPGraph.Formula.translate, Shape.keyBinding,
        Prefunctor.comp, Roles.binding, Shape.parentArrow, Shape.derefArrow,
        Family.MapId.owner, owner])

theorem sameBag_owner (i j : LocalId f) (h : (localFormulas f).SameBag i j) :
    i.owner = j.owner := by
  obtain ⟨e, he⟩ := h
  have hh := congrArg (fun a : FormalCD.Metamodel.ArrowData f.canonicalRoles.graph =>
    a.2.2.val.owner) (he (arg i))
  simpa only [argument_owner] using hh.symm

theorem unary_argument_set (c) (m) (h) (a : (localFormulas f).Arg (.setValued c m h)) :
    ((localFormulas f).argument (.setValued c m h) a).2.2.val = .ordinary c m := by
  rcases a with ⟨a, b, e⟩; cases e; rfl

theorem unary_argument_mult (c) (m) (a : (localFormulas f).Arg (.multiplicity c m)) :
    ((localFormulas f).argument (.multiplicity c m) a).2.2.val = .ordinary c m := by
  rcases a with ⟨a, b, e⟩; cases e; rfl

theorem unary_argument_incl (i) (a : (localFormulas f).Arg (.inclusion i)) :
    ((localFormulas f).argument (.inclusion i) a).2.2.val = .inclusion i := by
  rcases a with ⟨a, b, e⟩; cases e; rfl

/-- Argument bag permutations preserve the unique generating slot. -/
theorem key_unique (i j : LocalId f)
    (hs : i.formula.symbol = j.formula.symbol) (hb : (localFormulas f).SameBag i j) : i = j := by
  have ho := sameBag_owner i j hb
  obtain ⟨e, he⟩ := hb
  have hm := congrArg (fun a : FormalCD.Metamodel.ArrowData f.canonicalRoles.graph =>
    a.2.2.val) (he (arg i))
  cases i <;> cases j <;> try { cases hs }
  all_goals try simp only [unary_argument_set, unary_argument_mult, unary_argument_incl] at hm
  all_goals first
    | (cases hm; rfl)
    | (cases ho; rfl)

end LocalId

theorem localFormulas_wellFormed : (localFormulas f).WellFormed where
  total_args i := ⟨i.arg⟩
  literal_key := LocalId.key_unique

/-- No local Shape predicate is dropped by canonical formula generation. -/
theorem local_complete (c : C) (φ : DPGraph.Formula signature (f.shape c).carrier)
    (h : φ ∈ Shape.declarations (f.shape c)) :
    ∃ i : LocalId f, i.owner = c ∧
      i.formula = φ.translate (f.canonicalRoles.binding c) := by
  rcases h with h | h | h | h | h | h
  · rcases h with ⟨a, b, e, ho, rfl⟩
    refine ⟨.setValued c ⟨e.val, e.property.1⟩ ho, rfl, ?_⟩
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    rcases e with ⟨m, hm, hs, ht⟩
    dsimp at hs ht
    subst a b
    erw [FormalCD.setValuedFormula_translate]
    rfl
  · rcases h with ⟨m, hm, rfl⟩
    refine ⟨.multiplicity c m, rfl, ?_⟩
    rcases m with ⟨m, hmp⟩
    rcases hm with hm | hm <;> cases hm
    all_goals
      unfold DPGraph.Formula.translate
      erw [FormalCD.arrowBinding_comp]
      rfl
  · rcases h with ⟨m, hm, rfl⟩
    refine ⟨.multiplicity c m, rfl, ?_⟩
    rcases m with ⟨m, hmp⟩
    rcases hm with hm | hm <;> cases hm
    all_goals
      unfold DPGraph.Formula.translate
      erw [FormalCD.arrowBinding_comp]
      rfl
  · rcases h with ⟨hp, rfl⟩; exact ⟨.inverse c hp, rfl, rfl⟩
  · rcases h with ⟨hp, ht, rfl⟩; exact ⟨.commutation c hp ht, rfl, rfl⟩
  · rcases h with ⟨hk, hp, ht, rfl⟩; exact ⟨.key c hk hp, rfl, rfl⟩

end Clafer.Compile
