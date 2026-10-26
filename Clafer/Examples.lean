module

public import Clafer.Shape.Diagram

/-! # Constructible and rejected witnesses for the selected 2014 syntax/Shapes -/

@[expose] public section
namespace Clafer.Examples
open Roles

def rootDecl : Declaration := { id := ⟨0⟩, name := "Sing", origin := .syntheticRoot }
def intDecl : Declaration := { id := ⟨1⟩, name := "int", origin := .primitive .int }
def basicDecl : Declaration := { id := ⟨2⟩, name := "same" }
def setDecl : Declaration := { id := ⟨3⟩, name := "same", reference := .set ⟨4⟩ }
def bagDecl : Declaration := { id := ⟨4⟩, name := "same", reference := .bag ⟨3⟩ }
def abstractDecl : Declaration :=
  { id := ⟨5⟩, name := "Type", authoredAbstract := true, isAbstract := true }
def abstractRefDecl : Declaration :=
  { id := ⟨6⟩, name := "RefType", reference := .set ⟨2⟩,
    authoredAbstract := true, isAbstract := true }
def derivedDecl : Declaration :=
  { id := ⟨7⟩, name := "derived", reference := .set ⟨2⟩, super := some ⟨6⟩ }
def abstractChild : Declaration := { id := ⟨8⟩, name := "same", isAbstract := true }

/-- Reference cycles do not cause containment recursion. Repeated names keep IDs. -/
def sample : AST := ⟨⟨0⟩,
  [.branch rootDecl [.branch intDecl [], .branch basicDecl [], .branch setDecl [],
    .branch bagDecl [], .branch derivedDecl []],
   .branch abstractDecl [.branch abstractChild []], .branch abstractRefDecl []]⟩

theorem sample_entries : sample.entries =
    [⟨rootDecl, none, 0⟩, ⟨intDecl, some ⟨0⟩, 1⟩, ⟨basicDecl, some ⟨0⟩, 1⟩,
     ⟨setDecl, some ⟨0⟩, 1⟩, ⟨bagDecl, some ⟨0⟩, 1⟩, ⟨derivedDecl, some ⟨0⟩, 1⟩,
     ⟨abstractDecl, none, 0⟩, ⟨abstractChild, some ⟨5⟩, 1⟩, ⟨abstractRefDecl, none, 0⟩] := by
  simp [sample, AST.entries, Tree.branch, Tree.entries, Forest.ofList, rootDecl, abstractDecl]

theorem sample_wellFormed : sample.WellFormed := by
  constructor
  all_goals try { simp [AST.Known, sample, AST.entries, Tree.branch, Tree.entries, Forest.ofList,
    rootDecl, intDecl, basicDecl, setDecl, bagDecl, derivedDecl, abstractDecl,
    abstractChild, abstractRefDecl, Reference.kind, Reference.target, Kind.CanExtend,
    PrimitiveDomain.name, ValidRange, GroupCard.range, one, unrestricted] }
  · refine ⟨fun i => if i = ⟨7⟩ then 1 else 0, ?_⟩
    simp [sample_entries, rootDecl, intDecl, basicDecl, setDecl, bagDecl,
      derivedDecl, abstractDecl, abstractChild, abstractRefDecl]
  · intro d hd hu p s hp hpm hs hsm
    simp only [sample_entries, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases p <;> cases s <;>
      simp_all [sample_entries, rootDecl, intDecl, basicDecl, setDecl, bagDecl,
        derivedDecl, abstractDecl, abstractChild, abstractRefDecl, Defaults,
        GroupCard.childDefault]
    all_goals aesop

theorem repeated_names_distinct_ids :
    basicDecl.name = setDecl.name ∧ basicDecl.id ≠ setDecl.id := by decide

theorem finite_reference_cycle : sample.entries.length = 9 ∧
    setDecl.reference.target = some bagDecl.id ∧
    bagDecl.reference.target = some setDecl.id := by rw [sample_entries]; decide

theorem fold_counts_reference_cycle :
    sample.trees.foldl (fun n t => n + t.fold
      (fun _ counts => 1 + counts.foldl (· + ·) 0)) 0 = 9 := by decide

def repeatedScope : ConstraintBoundary :=
  { id := 0, context := ⟨2⟩, scopeOccurrences := [⟨3⟩, ⟨3⟩, ⟨4⟩],
    binders := [⟨⟨0⟩, "x", [⟨3⟩, ⟨3⟩]⟩] }

theorem repeated_scope_resolved : repeatedScope.Resolved sample.Known := by
  simp [ConstraintBoundary.Resolved, repeatedScope, AST.Known, sample_entries,
    rootDecl, intDecl, basicDecl, setDecl, bagDecl, derivedDecl, abstractDecl,
    abstractChild, abstractRefDecl]

theorem repeated_scope_positions : (⟨0, by decide⟩ : repeatedScope.Occurrence) ≠ ⟨1, by decide⟩ ∧
    repeatedScope.referenced ⟨0, by decide⟩ = repeatedScope.referenced ⟨1, by decide⟩ := by decide

def xorParent : Declaration :=
  { basicDecl with group := ⟨some .xor, .xor⟩ }
def optionalChild : Declaration :=
  { setDecl with multiplicity := ⟨none, optional⟩ }
def explicitChild : Declaration :=
  { setDecl with multiplicity := ⟨some one, one⟩ }
def inheritedGroup : Declaration :=
  { derivedDecl with super := some xorParent.id, group := ⟨none, .xor⟩ }

theorem keyword_default : Defaults optionalChild (some xorParent) none := by unfold Defaults; decide
theorem explicit_overrides_keyword : Defaults explicitChild (some xorParent) none := by
  unfold Defaults; decide
theorem inherited_group_bounds : Defaults inheritedGroup (some rootDecl) (some xorParent) := by
  unfold Defaults; decide

/-- Numeric defaults cover every finite interval and every positive unbounded
lower bound, not just the keyword-equivalent ranges. Validity is checked separately. -/
theorem numeric_finite_default (lower upper : Nat) :
    (GroupCard.bounds ⟨lower, .finite upper⟩).childDefault = optional := by
  cases lower <;> rfl

theorem numeric_positive_unbounded_default (lower : Nat) :
    (GroupCard.bounds ⟨lower + 1, .unbounded⟩).childDefault = optional := rfl

theorem numeric_unrestricted_default :
    (GroupCard.bounds unrestricted).childDefault = one := rfl

theorem opt_provenance_matters :
    GroupCard.opt.range = (GroupCard.bounds unrestricted).range ∧
    GroupCard.opt.childDefault ≠ (GroupCard.bounds unrestricted).childDefault := by decide

def numericParent (r : DPGraph.Predicates.Range) : Declaration :=
  { basicDecl with group := ⟨some (.bounds r), .bounds r⟩ }

theorem numeric_child_defaults (lower upper : Nat) :
    Defaults optionalChild (some (numericParent ⟨lower, .finite upper⟩)) none := by
  cases lower <;>
    simp [Defaults, optionalChild, setDecl, numericParent, basicDecl, GroupCard.childDefault]

theorem numeric_mandatory_default_rejected :
    ¬Defaults setDecl (some (numericParent one)) none := by unfold Defaults; decide

theorem explicit_overrides_numeric :
    Defaults explicitChild (some (numericParent one)) none := by unfold Defaults; decide

def inheritedNumericGroup : Declaration :=
  { derivedDecl with super := some basicDecl.id, group := ⟨none, .bounds one⟩ }

theorem inherited_numeric_defaults :
    Defaults inheritedNumericGroup (some rootDecl) (some (numericParent one)) ∧
    Defaults optionalChild (some inheritedNumericGroup) none := by unfold Defaults; decide

theorem unrestricted_and_absent_defaults :
    Defaults setDecl (some (numericParent unrestricted)) none ∧
    Defaults setDecl (some basicDecl) none ∧ Defaults setDecl none none := by
  unfold Defaults; decide

theorem unbounded_range_valid : ValidRange ⟨100, .unbounded⟩ := trivial
theorem inverted_range_rejected : ¬ValidRange ⟨2, .finite 1⟩ := by unfold ValidRange; decide
theorem basic_reference_inheritance_rejected : ¬Kind.CanExtend .basic .referenceSet := by
  unfold Kind.CanExtend; decide
theorem bag_set_inheritance_rejected : ¬Kind.CanExtend .referenceBag .referenceSet := by
  unfold Kind.CanExtend; decide
theorem set_bag_inheritance_allowed : Kind.CanExtend .referenceSet .referenceBag := by
  unfold Kind.CanExtend; decide

def orphan : AST := ⟨⟨0⟩, [.branch rootDecl [], .branch basicDecl []]⟩
theorem concrete_orphan_rejected : ¬orphan.WellFormed := by
  intro h
  have ha := h.parentless_abstract ⟨basicDecl, none, 0⟩
    (by simp [orphan, AST.entries, Tree.branch, Tree.entries, Forest.ofList]) rfl (by decide)
  contradiction

def duplicate : AST := ⟨⟨0⟩, [.branch rootDecl [.branch basicDecl [], .branch basicDecl []]]⟩
theorem duplicate_ids_rejected : ¬duplicate.WellFormed := by
  intro h
  have hn := h.unique_ids
  simp [duplicate, AST.entries, Tree.branch, Tree.entries, Forest.ofList] at hn

def containerDecl : Declaration := { id := ⟨9⟩, name := "container" }
def badChild : Declaration := { derivedDecl with super := some basicDecl.id }
def badParents : AST := ⟨⟨0⟩,
  [.branch rootDecl [.branch basicDecl [], .branch containerDecl [.branch badChild []]]]⟩
theorem different_inheritance_parents_rejected : ¬badParents.WellFormed := by
  intro h
  have hp := h.inheritance_parent ⟨badChild, some ⟨9⟩, 2⟩
    (by simp [badParents, AST.entries, Tree.branch, Tree.entries, Forest.ofList, containerDecl])
    ⟨basicDecl, some ⟨0⟩, 1⟩ (by simp [badParents, AST.entries, Tree.branch, Tree.entries, Forest.ofList, rootDecl])
    rfl (by decide)
  contradiction

def selfSuperDecl : Declaration := { basicDecl with super := some basicDecl.id }
def selfSuper : AST := ⟨⟨0⟩, [.branch rootDecl [.branch selfSuperDecl []]]⟩
theorem self_inheritance_rejected : ¬selfSuper.WellFormed := by
  intro h
  exact h.no_self_super ⟨selfSuperDecl, some ⟨0⟩, 1⟩
    (by simp [selfSuper, AST.entries, Tree.branch, Tree.entries, Forest.ofList, rootDecl]) rfl

def badPrimitiveDecl : Declaration := { intDecl with reference := .set ⟨2⟩ }
def badPrimitive : AST := ⟨⟨0⟩, [.branch rootDecl [.branch badPrimitiveDecl [], .branch basicDecl []]]⟩
theorem primitive_reference_rejected : ¬badPrimitive.WellFormed := by
  intro h
  have hp := (h.primitive_shape ⟨badPrimitiveDecl, some ⟨0⟩, 1⟩
    (by simp [badPrimitive, AST.entries, Tree.branch, Tree.entries, Forest.ofList, rootDecl]) .int rfl).2.1
  contradiction

def badScope : ConstraintBoundary := { repeatedScope with scopeOccurrences := [⟨99⟩] }
theorem dangling_scope_rejected : ¬badScope.Resolved sample.Known := by
  simp [ConstraintBoundary.Resolved, badScope, repeatedScope, AST.Known, sample_entries,
    rootDecl, intDecl, basicDecl, setDecl, bagDecl, derivedDecl, abstractDecl,
    abstractChild, abstractRefDecl]

def basicShape : Shape := (Located.mk basicDecl (some ⟨0⟩) 1).shape
def setShape : Shape := (Located.mk setDecl (some ⟨0⟩) 1).shape
def bagShape : Shape := (Located.mk bagDecl (some ⟨0⟩) 1).shape
def abstractShape : Shape := (Located.mk abstractDecl none 0).shape
def abstractReferenceShape : Shape := (Located.mk abstractRefDecl none 0).shape

def basicHeadMap : Map basicShape.kind basicShape.hasParent := ⟨.head, rfl⟩
def setTargetMap : Map setShape.kind setShape.hasParent := ⟨.target, rfl⟩
def bagTargetMap : Map bagShape.kind bagShape.hasParent := ⟨.target, rfl⟩
def abstractDeref : Map abstractReferenceShape.kind abstractReferenceShape.hasParent :=
  ⟨.dereference, rfl⟩

theorem abstract_basic_keeps_head : Nonempty abstractShape.carrier := ⟨head _ _⟩
theorem abstract_reference_incidence :
    (mapSource abstractDeref).val = .head ∧ (mapTarget abstractDeref).val = .target := by decide
theorem reference_modes : mode setShape.kind setTargetMap.val = .ordinary ∧
    mode bagShape.kind bagTargetMap.val = .bag := by decide
theorem key_guard : needsReferenceKey setShape.kind setShape.hasParent = true ∧
    needsReferenceKey abstractReferenceShape.kind abstractReferenceShape.hasParent = false := by decide

theorem abstract_reference_no_key (φ : DPGraph.Formula DPGraph.Predicates.signature
    abstractReferenceShape.carrier) (h : φ ∈ Shape.declarations abstractReferenceShape) :
    φ.symbol ≠ .key 2 := by
  intro hk
  have hp := (Shape.key_conditions _ _ h hk).2
  contradiction

theorem bag_no_key (φ : DPGraph.Formula DPGraph.Predicates.signature bagShape.carrier)
    (h : φ ∈ Shape.declarations bagShape) : φ.symbol ≠ .key 2 := by
  intro hk
  have hp := (Shape.key_conditions _ _ h hk).1
  contradiction

theorem wrong_head_incidence_uninhabitable :
    IsEmpty {e : (head .basic true) ⟶ (⟨.source, rfl⟩ : Class .basic true) // e.val = .head} := by
  constructor
  rintro ⟨⟨r, hr⟩, he⟩
  change r = .head at he
  subst r
  cases hr.2.1

theorem abstract_inclusion_has_head :
    Nonempty (Shape.SharedClass setShape abstractReferenceShape) :=
  ⟨Shape.headInclusion _ _⟩
theorem abstract_inclusion_has_target :
    Nonempty {r : Shape.SharedClass setShape abstractReferenceShape // r.val = .target} :=
  ⟨⟨⟨.target, rfl, rfl⟩, rfl⟩⟩

/-- A partial carrier for inclusion incidence, not a claimed whole MCS/model. -/
inductive InclusionNode where
  | sub (c : setShape.carrier)
  | sup (c : abstractReferenceShape.carrier)
inductive InclusionEdge : InclusionNode → InclusionNode → Type where
  | sub {a b : setShape.carrier} (e : a ⟶ b) : InclusionEdge (.sub a) (.sub b)
  | sup {a b : abstractReferenceShape.carrier} (e : a ⟶ b) : InclusionEdge (.sup a) (.sup b)
  | incl (r : Shape.SharedClass setShape abstractReferenceShape) :
    InclusionEdge (.sub r.subClass) (.sup r.superClass)
instance : Quiver InclusionNode := ⟨InclusionEdge⟩

def inclusionRaw : FormalCD.Raw Shape.roleRegistry where
  carrier := CategoryTheory.Quiv.of InclusionNode
  declarations := ∅
  className _ := "role"
  mapName e := match e with | .sub _ | .sup _ => "map" | .incl _ => "isA"
  predefined _ := none
  mode e := match e with
    | .sub e => mode setShape.kind e.val
    | .sup e => mode abstractReferenceShape.kind e.val
    | .incl _ => .inclusion

def subRealization : setShape.Realization inclusionRaw where
  binding := { obj := InclusionNode.sub, map := InclusionEdge.sub }
  modes _ := rfl
def superRealization : abstractReferenceShape.Realization inclusionRaw where
  binding := { obj := InclusionNode.sup, map := InclusionEdge.sup }
  modes _ := rfl
def inclusionWitness : Shape.Inclusions subRealization superRealization where
  map := InclusionEdge.incl
  inclusion _ := rfl
def withSuper : Shape.OptionalInclusions subRealization (some abstractReferenceShape) :=
  ⟨superRealization, inclusionWitness⟩
def withoutSuper : Shape.OptionalInclusions subRealization none := ⟨⟩

theorem inclusion_witness_no_source (r : Shape.SharedClass setShape abstractReferenceShape) :
    r.val ≠ .source := by
  intro he
  have hr := r.property.2
  simp [classPresent, he, abstractReferenceShape, Located.shape] at hr

end Clafer.Examples
