module

public import Clafer.Shape.Diagram
public import FormalCD.Metamodel.Binding

/-!
# Multi-Clafer Shapes: structural data

SoSyM §6.2.3/Figure 23 and Tables 5–8 (see Appendix 5). Local slots are
occurrence identities; cojoining compares vertices of the role graph. Resolved
referents and strings are separate data. No quotient/gluing policy is imposed.
The seven corrected source multiplicities are 0..1, not existence requirements
on every arrow. Presence is governed by the existing Shape rules.
-/

@[expose] public section
namespace Clafer.MCS
open CategoryTheory Roles

/-- Already resolved reference edges. Dangling targets cannot inhabit this type. -/
inductive ReferenceTo (C : Type) where
  | basic | set (target : C) | bag (target : C)

def ReferenceTo.kind {C : Type} : ReferenceTo C → Kind
  | .basic => .basic | .set _ => .referenceSet | .bag _ => .referenceBag

def ReferenceTo.target {C : Type} : ReferenceTo C → Option C
  | .basic => none | .set t | .bag t => some t

-- [impl->req~clafer-compile-group-data~1]
/-- The resolved structural interface of an MCS; AST conversion belongs to #22.
Multiplicity and abstractness here are effective values, not another defaulting pass. -/
structure Family (C : Type) where
  parent : C → Option C
  reference : C → ReferenceTo C
  super : C → Option C
  origin : C → Origin
  isAbstract : C → Bool
  name : C → String
  multiplicity : C → DPGraph.Predicates.Range
  root : C
  /-- Appendix 3 group metadata. Interpretation and formula generation are
  separate from the existing structural MCS disciplines. -/
  group : C → GroupMultiplicity := fun _ => {}

def Family.shape {C : Type} (f : Family C) (c : C) : Shape :=
  ⟨(f.reference c).kind, (f.parent c).isSome, f.name c, f.multiplicity c⟩

/-- Table 7, with the accepted parentless exception and inherited AST restrictions. -/
structure Family.WellFormed {C : Type} (f : Family C) : Prop where
  root_origin : ∀ c, f.origin c = .syntheticRoot ↔ c = f.root
  root_shape : f.parent f.root = none ∧ f.reference f.root = .basic ∧
    f.super f.root = none ∧ f.isAbstract f.root = false
  primitive_shape : ∀ c d, f.origin c = .primitive d →
    f.parent c = some f.root ∧ f.reference c = .basic ∧ f.super c = none
  unique_primitive : ∀ c c' d, f.origin c = .primitive d →
    f.origin c' = .primitive d → c = c'
  parentless_abstract : ∀ c, f.parent c = none → c ≠ f.root → f.isAbstract c = true
  nested_abstract : ∀ c p, f.parent c = some p →
    f.isAbstract c = true → f.isAbstract p = true
  inheritance_kind : ∀ c s, f.super c = some s →
    (f.reference c).kind.CanExtend (f.reference s).kind
  inheritance_parent : ∀ c s, f.super c = some s →
    f.parent s ≠ none → f.parent c = f.parent s
  parent_rank : ∃ rank : C → Nat, ∀ c p, f.parent c = some p → rank p < rank c
  super_rank : ∃ rank : C → Nat, ∀ c s, f.super c = some s → rank s < rank c
  valid_bounds : ∀ c, ValidRange (f.multiplicity c)

/-- Each super slot exists exactly when the super and both class slots exist. -/
abbrev Family.InclusionSlot {C : Type} (f : Family C) :=
  Σ c s : C, {_r : Shape.SharedClass (f.shape c) (f.shape s) // f.super c = some s}

/-- An ordinary slot and an inclusion slot remain distinct even at equal endpoints. -/
inductive Family.MapId {C : Type} (f : Family C) where
  | ordinary (c : C) (r : Map (f.shape c).kind (f.shape c).hasParent)
  | inclusion (r : f.InclusionSlot)

def Family.MapId.owner {C : Type} {f : Family C} : f.MapId → C
  | .ordinary c _ => c | .inclusion r => r.1

def Family.MapId.mode {C : Type} {f : Family C} : f.MapId → FormalCD.MapMode
  | .ordinary c r => Roles.mode (f.shape c).kind r.val
  | .inclusion _ => .inclusion

/-- Class-slot assignment is raw data; cojoining is checked separately. -/
structure Roles (C V : Type) (f : Family C) where
  vertex : (c : C) → (f.shape c).carrier → V

def Roles.head {C V : Type} {f : Family C} (r : Roles C V f) (c : C) : V :=
  r.vertex c (Clafer.Roles.head _ _)

def Roles.source {C V : Type} {f : Family C} (r : Roles C V f) : f.MapId → V
  | .ordinary c m => r.vertex c (mapSource m)
  | .inclusion ⟨c, _, i⟩ => r.vertex c i.val.subClass

def Roles.target {C V : Type} {f : Family C} (r : Roles C V f) : f.MapId → V
  | .ordinary c m => r.vertex c (mapTarget m)
  | .inclusion ⟨_, s, i⟩ => r.vertex s i.val.superClass

abbrev Roles.Arrow {C V : Type} {f : Family C} (r : Roles C V f) (a b : V) :=
  {m : f.MapId // r.source m = a ∧ r.target m = b}

def Roles.graph {C V : Type} {f : Family C} (r : Roles C V f) : Quiv :=
  @Quiv.of V ⟨r.Arrow⟩

def Roles.binding {C V : Type} {f : Family C} (r : Roles C V f) (c : C) :
    (f.shape c).carrier ⥤q r.graph where
  obj := r.vertex c
  map e := ⟨.ordinary c ⟨e.val, e.property.1⟩, by
    change r.vertex c (mapSource _) = r.vertex c _ ∧
      r.vertex c (mapTarget _) = r.vertex c _
    exact ⟨congrArg (r.vertex c) (Subtype.ext e.property.2.1),
      congrArg (r.vertex c) (Subtype.ext e.property.2.2)⟩⟩

def Roles.inclusion {C V : Type} {f : Family C} (r : Roles C V f)
    (i : f.InclusionSlot) :
    r.Arrow (r.vertex i.1 i.2.2.val.subClass) (r.vertex i.2.1 i.2.2.val.superClass) := ⟨.inclusion i, rfl, rfl⟩

/-- Table 6 equalities are at role-graph vertex identity, before referents or names. -/
structure Roles.Cojoining {C V : Type} {f : Family C} (r : Roles C V f) : Prop where
  head_bijective : Function.Bijective r.head
  parent : ∀ c p (hp : f.parent c = some p),
    r.vertex c (Shape.sourceClass (f.shape c) (by simp [Family.shape, hp])) = r.head p
  target : ∀ c t (_ht : (f.reference c).target = some t),
    ∀ h : (f.shape c).kind ≠ .basic,
    r.vertex c (Shape.targetClass (f.shape c) h) = r.head t

/-- Resolved referent identities are not role identities or display strings.
Endpoint-compatible gluing of these referents is defined in `MCS.Gluing`. -/
structure Labels {C V : Type} (f : Family C) where
  ClassRef : Type
  MapRef : Type
  classReferent : V → ClassRef
  mapReferent : f.MapId → MapRef
  className : V → String
  mapName : f.MapId → String

/-- The ClassRole/MapRole cover and disjointness are structural, not extra flags. -/
abbrev Role (C V : Type) (f : Family C) := V ⊕ f.MapId

def Labels.label {C V : Type} {f : Family C} (l : Labels (V := V) f) : Role C V f → String
  | .inl c => l.className c | .inr m => l.mapName m

def predefinedStrings : Set String := {s | s = "Sing" ∨ ∃ d : PrimitiveDomain, s = d.name}

-- [impl->req~clafer-mcs-disciplines~1]
/-- Table 8, including both directions of each reserved-name equivalence. -/
structure Labels.WellFormed {C V : Type} {f : Family C}
    (l : Labels (V := V) f) (r : Roles C V f) : Prop where
  head_name : ∀ c, l.className (r.head c) = f.name c
  ordinary_name : ∀ c (m : Map (f.shape c).kind (f.shape c).hasParent),
    l.mapName (.ordinary c m) = match m.val with
      | .head => l.className (r.head c)
      | .parent => "parent" | .dereference => "dref"
      | .target => l.className (r.head c) ++ "*"
  inclusion_name : ∀ i, l.mapName (.inclusion i) = "isA"
  sing_iff : ∀ c, f.origin c = .syntheticRoot ↔ l.className (r.head c) = "Sing"
  primitive_iff : ∀ c d, f.origin c = .primitive d ↔ l.className (r.head c) = d.name

-- [impl->req~clafer-mcs-formulas~1]
/-- Formula objects retain complete graph maps and exactly one owner. Formula
generation/completeness is Compile's obligation; this is structural validity. -/
structure Formulas {C V : Type} {f : Family C} (r : Roles C V f)
    (σ : DPGraph.Signature.{0,0,0}) where
  Id : Type
  owner : Id → C
  formula : Id → DPGraph.Formula σ r.graph

abbrev Formulas.Arg {C V : Type} {f : Family C} {r : Roles C V f}
    {σ : DPGraph.Signature.{0,0,0}} (d : Formulas r σ) (i : d.Id) :=
  FormalCD.Metamodel.ArrowData (σ.arity (d.formula i).symbol)

def Formulas.argument {C V : Type} {f : Family C} {r : Roles C V f}
    {σ : DPGraph.Signature.{0,0,0}} (d : Formulas r σ) (i : d.Id) (a : d.Arg i) :
    FormalCD.Metamodel.ArrowData r.graph :=
  ⟨(d.formula i).binding.obj a.1, (d.formula i).binding.obj a.2.1,
    (d.formula i).binding.map a.2.2⟩

/-- Literal bag equality allows occurrence permutations; it is not indexed equality. -/
def Formulas.SameBag {C V : Type} {f : Family C} {r : Roles C V f}
    {σ : DPGraph.Signature.{0,0,0}} (d : Formulas r σ) (i j : d.Id) : Prop :=
  ∃ e : d.Arg i ≃ d.Arg j, ∀ a, d.argument j (e a) = d.argument i a

structure Formulas.WellFormed {C V : Type} {f : Family C} {r : Roles C V f}
    {σ : DPGraph.Signature.{0,0,0}} (d : Formulas r σ) : Prop where
  total_args : ∀ i, Nonempty (d.Arg i)
  literal_key : ∀ i j, (d.formula i).symbol = (d.formula j).symbol →
    d.SameBag i j → i = j

def Formulas.diagram {C V : Type} {f : Family C} {r : Roles C V f}
    {σ : DPGraph.Signature.{0,0,0}} (d : Formulas r σ) : DPGraph σ :=
  ⟨r.graph, Set.range d.formula⟩

/-- Proofs of the independent disciplines are bundled once, without copied flags. -/
structure Valid {C V : Type} {f : Family C} {r : Roles C V f}
    {σ : DPGraph.Signature.{0,0,0}} (l : Labels (V := V) f) (d : Formulas r σ) : Prop where
  family : f.WellFormed
  cojoining : r.Cojoining
  naming : l.WellFormed r
  formulas : d.WellFormed

-- [impl->req~clafer-mcs-metamodel~1]
structure Model (C V : Type) (σ : DPGraph.Signature.{0,0,0}) where
  family : Family C
  roles : Roles C V family
  labels : Labels (V := V) family
  formulas : Formulas roles σ
  valid : Valid labels formulas

end Clafer.MCS
