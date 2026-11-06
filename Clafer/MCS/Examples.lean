module

public import Clafer.MCS.Metamodel

/-!
[proof->req~clafer-mcs-disciplines~1]
[proof->req~clafer-mcs-formulas~1]
[proof->req~clafer-mcs-metamodel~1]
-/

/-! # Nonempty MCS witnesses and rejected structural boundaries (Appendix 5) -/

@[expose] public section
namespace Clafer.MCS.Examples
open CategoryTheory Clafer.Roles DPGraph.Predicates

inductive Owner where
  | root | int | string | bool | basic | set | bag | abstractBasic | abstractRef
  | derivedAbstract | derivedSet
  deriving DecidableEq

instance : Fintype Owner := ⟨{.root, .int, .string, .bool, .basic, .set, .bag,
  .abstractBasic, .abstractRef, .derivedAbstract, .derivedSet}, by intro c; cases c <;> simp⟩

def family : Family Owner where
  root := .root
  parent
    | .root | .abstractBasic | .abstractRef => none
    | _ => some .root
  reference
    | .set | .abstractRef | .derivedAbstract | .derivedSet => .set .basic
    | .bag => .bag .set
    | _ => .basic
  super | .derivedAbstract => some .abstractRef | .derivedSet => some .set | _ => none
  origin
    | .root => .syntheticRoot
    | .int => .primitive .int | .string => .primitive .string | .bool => .primitive .bool
    | _ => .user
  isAbstract | .abstractBasic | .abstractRef => true | _ => false
  name
    | .root => "Sing" | .int => "int" | .string => "string" | .bool => "bool"
    | .abstractBasic => "Type" | .abstractRef => "RefType"
    | _ => "repeated"
  multiplicity _ := one

theorem family_valid : family.WellFormed := by
  constructor
  · intro c; cases c <;> simp [family]
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · intro c d; cases c <;> cases d <;> simp [family]
  · intro c c' d; cases c <;> cases c' <;> cases d <;> simp [family]
  · intro c; cases c <;> simp [family]
  · intro c p; cases c <;> cases p <;> simp [family]
  · intro c s; cases c <;> cases s <;> simp [family, ReferenceTo.kind, Kind.CanExtend]
  · intro c s; cases c <;> cases s <;> simp [family]
  · refine ⟨fun c => if c = .root then 0 else 1, ?_⟩
    intro c p; cases c <;> cases p <;> simp [family]
  · refine ⟨fun c => if c = .derivedAbstract ∨ c = .derivedSet then 1 else 0, ?_⟩
    intro c s; cases c <;> cases s <;> simp [family]
  · intro c; simp [family, ValidRange, one, Clafer.one]

def roles := family.canonicalRoles

inductive ClassReferent where | resolved (id : Owner)
inductive MapReferent where | resolved (id : family.MapId)

def labels : Labels (V := Owner) family where
  ClassRef := ClassReferent
  MapRef := MapReferent
  classReferent := ClassReferent.resolved
  mapReferent := MapReferent.resolved
  className := family.name
  mapName
    | .ordinary c m => match m.val with
      | .head => family.name c | .parent => "parent" | .dereference => "dref"
      | .target => family.name c ++ "*"
    | .inclusion _ => "isA"

theorem labels_valid : labels.WellFormed roles where
  head_name _ := rfl
  ordinary_name _ _ := rfl
  inclusion_name _ := rfl
  sing_iff c := by
    change family.origin c = .syntheticRoot ↔ family.name c = "Sing"
    cases c <;> decide
  primitive_iff c d := by
    change family.origin c = .primitive d ↔ family.name c = d.name
    cases c <;> cases d <;> decide

/-- Every map has a distinct role identity, including same-name arrows. -/
def edge (m : family.MapId) : roles.Arrow (roles.source m) (roles.target m) :=
  ⟨m, rfl, rfl⟩

/-- A nonempty bank of unary declarations. It is not a Compile output claim.
Inclusions get inclusion declarations; ordinary maps get an unrestricted bound. -/
def formula (m : family.MapId) : DPGraph.Formula signature roles.graph :=
  match m with
  | .ordinary c r => ⟨.targetMultiplicity unrestricted, FormalCD.arrowBinding (G := roles.graph) (edge (.ordinary c r))⟩
  | .inclusion i => FormalCD.inclusionFormula (G := roles.graph) (edge (.inclusion i))

def formulas : Formulas roles signature where
  Id := family.MapId
  owner := Family.MapId.owner
  formula := formula

/-- All formulas here have a unary arity, so this preserves the actual occurrence. -/
def arg (m : family.MapId) : formulas.Arg m := by
  cases m <;> change FormalCD.Metamodel.ArrowData Arity.unary <;>
    exact ⟨.source, .target, .arrow⟩

theorem argument_id (m : family.MapId) (a : formulas.Arg m) :
    (formulas.argument m a).2.2.val = m := by
  cases m <;> rcases a with ⟨a, b, e⟩ <;>
    change Arity.UnaryEdge a b at e <;> cases e <;> rfl

theorem formulas_valid : formulas.WellFormed where
  total_args m := ⟨arg m⟩
  literal_key i j _ h := by
    obtain ⟨e, he⟩ := h
    have hm := he (arg i)
    have hid := congrArg (fun a : FormalCD.Metamodel.ArrowData roles.graph => a.2.2.val) hm
    exact (argument_id i (arg i)).symm.trans
      (hid.symm.trans (argument_id j (e (arg i))))

theorem sample_valid : Valid labels formulas :=
  ⟨family_valid, family.canonical_cojoining, labels_valid, formulas_valid⟩

/-- All these Shapes have the existing well-formed local diagrams and typed
maps into one MCS carrier. The global formula bank remains explicit. -/
theorem shapes_compose (c : Owner) : (Shape.raw (family.shape c)).WellFormed ∧
    Nonempty ((family.shape c).carrier ⥤q roles.graph) :=
  ⟨Shape.raw_wellFormed _, ⟨roles.binding c⟩⟩

def basicParent : family.MapId := .ordinary .basic ⟨.parent, rfl⟩
def setParent : family.MapId := .ordinary .set ⟨.parent, rfl⟩
def setDref : family.MapId := .ordinary .set ⟨.dereference, rfl⟩
def bagDref : family.MapId := .ordinary .bag ⟨.dereference, rfl⟩

def headIncl : family.InclusionSlot :=
  ⟨.derivedAbstract, .abstractRef, Shape.headInclusion _ _, rfl⟩
def targetIncl : family.InclusionSlot :=
  ⟨.derivedAbstract, .abstractRef, ⟨.target, rfl, rfl⟩, rfl⟩
def sourceIncl : family.InclusionSlot :=
  ⟨.derivedSet, .set, ⟨.source, rfl, rfl⟩, rfl⟩

theorem repeated_parent_names : labels.mapName basicParent = labels.mapName setParent ∧
    basicParent ≠ setParent := by constructor; rfl; intro h; cases h

theorem repeated_dref_names : labels.mapName setDref = labels.mapName bagDref ∧
    setDref ≠ bagDref := by constructor; rfl; intro h; cases h

theorem repeated_inclusion_names : labels.mapName (.inclusion headIncl) =
    labels.mapName (.inclusion targetIncl) ∧ headIncl ≠ targetIncl := by
  constructor
  · rfl
  · intro h
    have hh := congrArg (fun i : family.InclusionSlot => i.2.2.val.val) h
    cases hh

theorem shared_source_present : sourceIncl.2.2.val.val = .source := rfl

theorem parentless_reference_retains_dref :
    family.parent .abstractRef = none ∧
      Nonempty (Map (family.shape .abstractRef).kind (family.shape .abstractRef).hasParent) :=
  ⟨rfl, ⟨⟨.dereference, rfl⟩⟩⟩

theorem missing_inherited_source (i : family.InclusionSlot)
    (h : i.2.1 = .abstractRef) : i.2.2.val.val ≠ .source :=
  missing_super_source i (by rw [h]; rfl)

theorem bag_mode : Family.MapId.mode (.ordinary (f := family) .bag ⟨.target, rfl⟩) =
    .bag := rfl

theorem user_named_Sing_rejected :
    ¬({labels with className := fun _ => "Sing"} : Labels (V := Owner) family).WellFormed roles := by
  intro h
  have hf := (h.sing_iff .basic).mpr rfl
  cases hf

theorem wrong_cojoining_rejected :
    ¬(⟨fun _ _ => Owner.basic⟩ : Roles Owner Owner family).Cojoining := by
  intro h
  have he := h.head_bijective.1 (a₁ := Owner.root) (a₂ := Owner.int) rfl
  cases he

def wrongParentRoles : Roles Owner Owner family where
  vertex c r := if r.val = .source then .basic else family.canonicalVertex c r

theorem wrong_parent_cojoining_rejected : ¬wrongParentRoles.Cojoining := by
  intro h
  have he := h.parent .basic .root rfl
  change Owner.basic = Owner.root at he
  cases he

def wrongTargetRoles : Roles Owner Owner family where
  vertex c r := if r.val = .target then .root else family.canonicalVertex c r

theorem wrong_target_cojoining_rejected : ¬wrongTargetRoles.Cojoining := by
  intro h
  have he := h.target .set .basic rfl (by decide)
  change Owner.root = Owner.basic at he
  cases he

def missingParent : Family Owner :=
  { family with parent := fun c => if c = .basic then none else family.parent c }

theorem missing_parent_rejected : ¬missingParent.WellFormed := by
  intro h
  have he := h.parentless_abstract .basic rfl (by decide)
  change false = true at he
  cases he

def badPrimitive : Family Owner :=
  { family with reference := fun c => if c = .int then .set .basic else family.reference c }

theorem primitive_reference_rejected : ¬badPrimitive.WellFormed := by
  intro h
  have he := (h.primitive_shape .int .int rfl).2.1
  change ReferenceTo.set Owner.basic = ReferenceTo.basic at he
  cases he

def badRoot : Family Owner :=
  { family with super := fun c => if c = .root then some .abstractBasic else family.super c }

theorem root_super_rejected : ¬badRoot.WellFormed := by
  intro h
  have he := h.root_shape.2.2.1
  change some Owner.abstractBasic = none at he
  cases he

/-- Two separately owned formula objects with the same bag and predicate are illegal. -/
def duplicateFormulas : Formulas roles signature where
  Id := Bool
  owner _ := .basic
  formula _ := formula basicParent

theorem duplicate_formulas_rejected : ¬duplicateFormulas.WellFormed := by
  intro h
  have he := h.literal_key false true rfl ⟨Equiv.refl _, fun _ => rfl⟩
  cases he

def sample : Model Owner Owner signature :=
  ⟨family, roles, labels, formulas, sample_valid⟩

def repeatedBinding : Arity.fanOut 2 ⥤q roles.graph where
  obj | .center => roles.source basicParent | .member _ => roles.target basicParent
  map | .edge _ => edge basicParent

def repeatedArgs : Formulas roles signature where
  Id := Unit
  owner _ := .basic
  formula _ := ⟨.key 2, repeatedBinding⟩

def firstArg : repeatedArgs.Arg () := ⟨.center, .member 0, .edge 0⟩
def secondArg : repeatedArgs.Arg () := ⟨.center, .member 1, .edge 1⟩

theorem repeated_args_valid : repeatedArgs.WellFormed where
  total_args _ := ⟨firstArg⟩
  literal_key i j _ _ := by cases i; cases j; rfl

theorem repeated_occurrences_preserved : firstArg ≠ secondArg ∧
    repeatedArgs.argument () firstArg = repeatedArgs.argument () secondArg := by
  constructor
  · intro h
    have ht := congrArg (fun e : repeatedArgs.Arg () => e.2.1) h
    have hn : (0 : Fin 2) = 1 := Arity.FanOut.member.inj ht
    exact (by decide : (0 : Fin 2) ≠ 1) hn
  · rfl

end Clafer.MCS.Examples
