module

public import FormalCD.Metamodel.Realization.Correctness
public import FormalCD.Metamodel.Realization.Reconstruction

/-! # Canonical realization boundaries
Actual whole-model acceptance and rejection, retaining isolated vertices,
repeated argument occurrences, repeated names, and parallel map identities.
-/

@[expose] public section

namespace FormalCD.Metamodel.Realization.Examples
open CategoryTheory DPGraph DPGraph.Predicates

inductive SourceNode where | left | right
  deriving DecidableEq
instance : Quiver SourceNode := ⟨fun _ _ => Bool⟩
abbrev sourceGraph : Quiv := Quiv.of SourceNode

inductive Position where | source | target | isolated
inductive PositionEdge : Position → Position → Type where
  | first : PositionEdge .source .target
  | second : PositionEdge .source .target
instance : Quiver Position := ⟨PositionEdge⟩
abbrev positionGraph : Quiv := Quiv.of Position

def extra : Signature := ⟨Unit, fun _ => positionGraph⟩
def vocab : Vocabulary := Vocabulary.extend extra

def registry : Registry where
  Id := Unit
  name _ := "Reserved"
  kind _ := .primitive

def fixture (S : Set (Formula vocab.signature sourceGraph)) : CDOver vocab registry where
  carrier := sourceGraph
  declarations := S
  className _ := "User"
  mapName _ := "edge"
  predefined _ := none
  mode _ := .bag
  wellFormed :=
    { predefined_name := by intro _ _ h; cases h
      user_name := by
        rintro _ _ ⟨_, h⟩
        exact (by decide : "Reserved" ≠ "User") h
      unique_predefined := by intro _ _ _ h; cases h
      inclusion_name := by intro _ _ _ h; cases h
      inclusion_decl := by intro _ _ _ h; cases h
      ordinary_decl := by intro _ _ _ h; cases h }

def binding (isolated : SourceNode) : positionGraph ⥤q sourceGraph where
  obj | .source | .target => .left | .isolated => isolated
  map | .first | .second => false

def repeated (isolated : SourceNode) : Formula vocab.signature sourceGraph :=
  ⟨.inr (), binding isolated⟩

-- [impl->req~formalcd-realization-boundaries~1]
def positive := fixture {repeated .right}

theorem positive_supported : Supported positive := by
  rintro ⟨φ, h⟩
  have he : φ = repeated .right := h
  subst φ
  exact ⟨⟨_, _, PositionEdge.first⟩⟩

theorem positive_separated : Separated positive := by
  intro f g _ _
  exact Subtype.ext (f.property.trans g.property.symm)

/-- A nonempty arity with an isolated vertex and repeated arguments is admitted. -/
theorem positive_model :
    (interpretation (context positive)).IsModel diagram.toDPGraph (encode positive) :=
  (model_iff positive).mpr ⟨positive_supported, positive_separated⟩

theorem repeated_occurrences :
    (Candidate.ofFormula (repeated .right)).argument ⟨_, _, PositionEdge.first⟩ =
      (Candidate.ofFormula (repeated .right)).argument ⟨_, _, PositionEdge.second⟩ := rfl

theorem positions_distinct :
    (⟨_, _, PositionEdge.first⟩ : ArrowData positionGraph) ≠ ⟨_, _, PositionEdge.second⟩ := by
  intro h
  cases h

/-- Complete indexing prevents the two equal targets from becoming one link. -/
theorem repeated_args_not_setValued : ¬ SetValued ((encode positive).map Edge.args) := by
  intro h
  have hinj := (setValued_fibers _).mp h
  let f : Declared positive := ⟨repeated .right, rfl⟩
  let x := formulas positive f
  have hx : (formulas positive).symm x = f := (formulas positive).symm_apply_apply f
  have collide : ¬ Function.Injective ((arguments positive).eval x) := by
    change ¬ Function.Injective (fun a => arrows positive
      ((Candidate.ofFormula ((formulas positive).symm x).val).argument a))
    rw [hx]
    intro hi
    exact positions_distinct (hi (congrArg (arrows positive) repeated_occurrences))
  apply collide
  intro a b hab
  let E := (arguments positive).spanFamilyEquivalence
  have htarget : (arguments positive).toSpan.toFamily.eval x ((E.equiv x).symm a) =
      (arguments positive).toSpan.toFamily.eval x ((E.equiv x).symm b) := by
    rw [← E.eval_eq, ← E.eval_eq, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hab
  exact (E.equiv x).symm.injective (hinj x htarget)

theorem isolated_binding_retained :
    ((formulas positive).symm (formulas positive ⟨repeated .right, rfl⟩)).val = repeated .right ∧
    (repeated .right).binding.obj Position.isolated = SourceNode.right :=
  ⟨congrArg Subtype.val ((formulas positive).symm_apply_apply _), rfl⟩

theorem reserved_unrealized : text positive "Reserved" ∈ extent positive .predefStr ∧
    extent positive .predef = ∅ := by
  refine ⟨⟨(), rfl⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨c, rfl⟩, i, hi⟩
    cases hi
  · intro h; cases h

theorem repeated_names_distinct_objects :
    (names positive).name (vertex positive .left) = (names positive).name (vertex positive .right) ∧
    vertex positive .left ≠ vertex positive .right :=
  ⟨rfl, fun h => SourceNode.noConfusion ((vertex positive).injective h)⟩

theorem parallel_maps_distinct :
    arrow positive ⟨SourceNode.left, SourceNode.right, false⟩ ≠
      arrow positive ⟨SourceNode.left, SourceNode.right, true⟩ := by
  intro h
  have he := (arrow positive).injective h
  cases he

/-- Empty effective declarations need neither global positive arities nor formulas. -/
theorem empty_model : (interpretation (context (fixture ∅))).IsModel diagram.toDPGraph
    (encode (fixture ∅)) := by
  apply (model_iff _).mpr
  constructor
  · rintro ⟨_, h⟩; cases h
  · rintro ⟨_, h⟩; cases h

def zeroFormula : Formula vocab.signature sourceGraph :=
  vocab.embed ⟨.cover 0,
    { obj := fun _ => .left
      map := fun e => by cases e with | edge i => exact Fin.elim0 i }⟩
def zero := fixture {zeroFormula}

theorem zero_not_model : ¬ (interpretation (context zero)).IsModel diagram.toDPGraph (encode zero) := by
  intro h
  obtain ⟨⟨_, _, a⟩⟩ := ((model_iff zero).mp h).1 ⟨zeroFormula, rfl⟩
  cases a with | edge i => exact Fin.elim0 i

def collision := fixture {φ | φ = repeated .left ∨ φ = repeated .right}

def isolatedValue : Formula vocab.signature sourceGraph → SourceNode
  | ⟨.inr (), b⟩ => b.obj .isolated
  | _ => .left

theorem collision_supported : Supported collision := by
  rintro ⟨_, h | h⟩ <;> subst h
  all_goals exact ⟨⟨_, _, PositionEdge.first⟩⟩

theorem collision_not_separated : ¬ Separated collision := by
  intro h
  have he := h ⟨repeated .left, Or.inl rfl⟩ ⟨repeated .right, Or.inr rfl⟩ rfl
    ⟨Equiv.refl _, by rintro ⟨_, _, a⟩; cases a <;> rfl⟩
  cases congrArg isolatedValue (congrArg Subtype.val he)

-- [proof->req~formalcd-realization-boundaries~1]
/-- Positive support cannot repair the literal key's loss of isolated vertices. -/
theorem collision_not_model :
    ¬ (interpretation (context collision)).IsModel diagram.toDPGraph (encode collision) :=
  fun h => collision_not_separated ((model_iff collision).mp h).2

theorem rejected_syntax_roundtrip :
    decodeRaw (encode collision) (context collision) (modes collision) = collision.toRawOver :=
  decode_encode collision

end FormalCD.Metamodel.Realization.Examples
