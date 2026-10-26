module

public import Clafer.Context
public import FormalCD.Basic

/-!
# Finite, resolved 2014 syntax

SoSyM §5.3.1–5, §5.4–5 (PDF pp.14–17), §6.2.2/Figure 22 (PDF p.21),
Appendix 3/Figure 27 (PDF pp.31–32). Input is already resolved and defaulted.
Containment is deep syntax; references and inheritance are identifier edges.
-/

@[expose] public section
namespace Clafer
open DPGraph.Predicates

inductive Kind where
  | basic | referenceSet | referenceBag
  deriving DecidableEq, Repr

inductive Reference where
  | basic
  | set (target : DeclId)
  | bag (target : DeclId)
  deriving DecidableEq, Repr

def Reference.kind : Reference → Kind
  | .basic => .basic | .set _ => .referenceSet | .bag _ => .referenceBag

def Reference.target : Reference → Option DeclId
  | .basic => none | .set i | .bag i => some i

/-- §5.5: basic cannot specialize reference, bag cannot specialize set. -/
def Kind.CanExtend (sub sup : Kind) : Prop :=
  (sub = .basic → sup = .basic) ∧
  (sub = .referenceBag → sup ≠ .referenceSet)

def one : Range := ⟨1, .finite 1⟩
def optional : Range := ⟨0, .finite 1⟩
def unrestricted : Range := ⟨0, .unbounded⟩

def ValidRange (r : Range) : Prop :=
  match r.upper with | .finite n => r.lower ≤ n | .unbounded => True

inductive GroupCard where
  | bounds (range : Range)
  | xor | or | mux | opt
  deriving DecidableEq

def GroupCard.range : GroupCard → Range
  | .bounds r => r | .xor => one | .or => ⟨1, .unbounded⟩
  | .mux => optional | .opt => unrestricted

/-- Adopted evolution of Appendix 3 defaults: every group except numeric 0..*
makes children optional. See docs/sources.md#current-child-default-policy. -/
def GroupCard.childDefault : GroupCard → Range
  | .bounds ⟨0, .unbounded⟩ => one
  | .bounds _ | .xor | .or | .mux | .opt => optional

structure Multiplicity where
  authored : Option Range := none
  effective : Range := one
  deriving DecidableEq

/-- Keep keyword provenance when inheriting a group at the resolved boundary. -/
structure GroupMultiplicity where
  authored : Option GroupCard := none
  effective : GroupCard := .bounds unrestricted
  deriving DecidableEq

inductive PrimitiveDomain where
  | int | string | bool
  deriving DecidableEq, Repr

def PrimitiveDomain.name : PrimitiveDomain → String
  | .int => "int" | .string => "string" | .bool => "bool"

inductive Origin where
  | syntheticRoot | primitive (domain : PrimitiveDomain) | user
  deriving DecidableEq, Repr

/-- Metadata and resolved edges, not a shallow encoding in Lean predicates. -/
structure Declaration where
  id : DeclId
  name : String
  origin : Origin := .user
  reference : Reference := .basic
  super : Option DeclId := none
  authoredAbstract : Bool := false
  isAbstract : Bool := false
  multiplicity : Multiplicity := {}
  group : GroupMultiplicity := {}
  constraints : List ConstraintBoundary := []
  deriving DecidableEq

mutual
  inductive Tree where
    | node (declaration : Declaration) (children : Forest)
  inductive Forest where
    | nil
    | cons (tree : Tree) (rest : Forest)
end

/-- Convenient finite-list construction, with structural recursion throughout. -/
def Forest.ofList (ts : List Tree) : Forest := ts.foldr Forest.cons .nil

def Tree.branch (d : Declaration) (children : List Tree) : Tree := .node d (Forest.ofList children)

/- Finite structural recursion for a future compiler's child-first algebra.
Neither target nor super IDs are followed by this traversal. Primitive recursors
are kernel-reducible; `noncomputable` only suppresses unsupported native code
generation for these recursors, without adding a choice or termination axiom. -/
noncomputable def Tree.fold {α : Type} (algebra : Declaration → List α → α) (t : Tree) : α :=
  Tree.rec (motive_1 := fun _ => α) (motive_2 := fun _ => List α)
    (fun d _ children => algebra d children) [] (fun _ _ x xs => x :: xs) t

noncomputable def Forest.fold {α : Type} (algebra : Declaration → List α → α) (ts : Forest) : List α :=
  Forest.rec (motive_1 := fun _ => α) (motive_2 := fun _ => List α)
    (fun d _ children => algebra d children) [] (fun _ _ x xs => x :: xs) ts

structure Located where
  declaration : Declaration
  parent : Option DeclId
  depth : Nat
  deriving DecidableEq

noncomputable def Tree.entries (t : Tree) (parent : Option DeclId) (depth : Nat) : List Located :=
  Tree.rec (motive_1 := fun _ => Option DeclId → Nat → List Located)
    (motive_2 := fun _ => Option DeclId → Nat → List Located)
    (fun d _ children p n => ⟨d, p, n⟩ :: children (some d.id) (n + 1))
    (fun _ _ => []) (fun _ _ t ts p n => t p n ++ ts p n) t parent depth

noncomputable def Forest.entries (ts : Forest) (parent : Option DeclId) (depth : Nat) : List Located :=
  Forest.rec (motive_1 := fun _ => Option DeclId → Nat → List Located)
    (motive_2 := fun _ => Option DeclId → Nat → List Located)
    (fun d _ children p n => ⟨d, p, n⟩ :: children (some d.id) (n + 1))
    (fun _ _ => []) (fun _ _ t ts p n => t p n ++ ts p n) ts parent depth

structure AST where
  root : DeclId
  trees : List Tree

noncomputable def AST.entries (a : AST) : List Located := a.trees.flatMap (fun t => t.entries none 0)
def AST.Known (a : AST) (i : DeclId) : Prop := ∃ d ∈ a.entries, d.declaration.id = i
abbrev AST.Occurrence (a : AST) := Fin a.entries.length
noncomputable def AST.at (a : AST) (i : a.Occurrence) : Located := a.entries[i]

/-- Structural child size is a usable decreasing measure for recursive compilation. -/
theorem Tree.child_smaller (d : Declaration) (cs : List Tree) (t : Tree) (h : t ∈ cs) :
    sizeOf t < sizeOf (Tree.branch d cs) := by
  have hs : sizeOf t < sizeOf (Forest.ofList cs) := by
    induction cs with
    | nil => cases h
    | cons c cs ih =>
      rcases List.mem_cons.mp h with rfl | hm
      · simp only [Forest.ofList, List.foldr_cons, Forest.cons.sizeOf_spec]
        omega
      · have := ih hm
        simp only [Forest.ofList] at this
        simp only [Forest.ofList, List.foldr_cons, Forest.cons.sizeOf_spec]
        omega
  simp only [Tree.branch, Tree.node.sizeOf_spec]
  exact Nat.lt_of_lt_of_le hs (by omega)

theorem AST.occurrences_finite (a : AST) : Finite a.Occurrence := inferInstance

theorem AST.every_entry_indexed (a : AST) (d : Located) (h : d ∈ a.entries) :
    ∃ i : a.Occurrence, a.at i = d := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
  exact ⟨⟨i, hi⟩, he⟩

/-- Consistency for already defaulted input under the adopted child-default policy.
An omitted group takes
the super's effective group (including keyword provenance), or 0..* otherwise.
Explicit child bounds override the parent's group default. -/
def Defaults (d : Declaration) (parent super : Option Declaration) : Prop :=
  d.group.effective = d.group.authored.getD
    (super.map (·.group.effective) |>.getD (.bounds unrestricted)) ∧
  d.multiplicity.effective = d.multiplicity.authored.getD
    (parent.map (·.group.effective.childDefault) |>.getD one) ∧
  d.isAbstract = (d.authoredAbstract || (parent.map (·.isAbstract)).getD false)

/-- Explicit selected resolved-input conditions, local to Clafer. The rank
witness rules out inheritance cycles; it is proof data, not another syntax edge.
The depth check applies to the actual deep traversal and unique resolved IDs. -/
structure AST.WellFormed (a : AST) : Prop where
  unique_ids : (a.entries.map (·.declaration.id)).Nodup
  root_exists : a.Known a.root
  root_origin : ∀ d ∈ a.entries, d.declaration.origin = .syntheticRoot ↔
    d.declaration.id = a.root
  root_shape : ∀ d ∈ a.entries, d.declaration.id = a.root →
    d.parent = none ∧ d.declaration.reference = .basic ∧
    d.declaration.super = none ∧ d.declaration.isAbstract = false
  parent_exists : ∀ d ∈ a.entries, ∀ p, d.parent = some p → a.Known p
  parent_depth : ∀ d ∈ a.entries, ∀ p ∈ a.entries,
    d.parent = some p.declaration.id → p.depth < d.depth
  parentless_abstract : ∀ d ∈ a.entries, d.parent = none →
    d.declaration.id ≠ a.root → d.declaration.isAbstract = true
  nested_abstract : ∀ d ∈ a.entries, ∀ p ∈ a.entries,
    d.parent = some p.declaration.id → d.declaration.isAbstract = true →
    p.declaration.isAbstract = true
  primitive_shape : ∀ d ∈ a.entries, ∀ dom, d.declaration.origin = .primitive dom →
    d.parent = some a.root ∧ d.declaration.reference = .basic ∧
    d.declaration.super = none ∧ d.declaration.name = dom.name
  unique_domains : ∀ d ∈ a.entries, ∀ e ∈ a.entries, ∀ dom,
    d.declaration.origin = .primitive dom → e.declaration.origin = .primitive dom → d = e
  targets_resolved : ∀ d ∈ a.entries, ∀ t, d.declaration.reference.target = some t → a.Known t
  supers_resolved : ∀ d ∈ a.entries, ∀ s, d.declaration.super = some s → a.Known s
  inheritance_kind : ∀ d ∈ a.entries, ∀ s ∈ a.entries,
    d.declaration.super = some s.declaration.id →
    d.declaration.reference.kind.CanExtend s.declaration.reference.kind
  inheritance_parent : ∀ d ∈ a.entries, ∀ s ∈ a.entries,
    d.declaration.super = some s.declaration.id →
    s.parent ≠ none → d.parent = s.parent
  inheritance_rank : ∃ rank : DeclId → Nat, ∀ d ∈ a.entries, ∀ s,
    d.declaration.super = some s → rank s < rank d.declaration.id
  valid_bounds : ∀ d ∈ a.entries,
    ValidRange d.declaration.multiplicity.effective ∧ ValidRange d.declaration.group.effective.range
  defaults : ∀ d ∈ a.entries, d.declaration.origin = .user →
    ∀ p s : Option Located,
    (p.map (·.declaration.id) = d.parent) → (∀ x ∈ p, x ∈ a.entries) →
    (s.map (·.declaration.id) = d.declaration.super) → (∀ x ∈ s, x ∈ a.entries) →
    Defaults d.declaration (p.map (·.declaration)) (s.map (·.declaration))
  constraints_resolved : ∀ d ∈ a.entries, ∀ c ∈ d.declaration.constraints,
    c.context = d.declaration.id ∧ c.Resolved a.Known

theorem AST.WellFormed.no_self_parent {a : AST} (h : a.WellFormed)
    (d : Located) (hd : d ∈ a.entries) : d.parent ≠ some d.declaration.id := by
  intro hp
  exact Nat.lt_irrefl _ (h.parent_depth d hd d hd hp)

theorem AST.WellFormed.no_self_super {a : AST} (h : a.WellFormed)
    (d : Located) (hd : d ∈ a.entries) : d.declaration.super ≠ some d.declaration.id := by
  obtain ⟨rank, hr⟩ := h.inheritance_rank
  intro hs
  exact Nat.lt_irrefl _ (hr d hd _ hs)

/-- Parent recursion on resolved occurrences is well-founded as well as tree recursion. -/
theorem AST.WellFormed.parent_wellFounded {a : AST} (h : a.WellFormed) :
    WellFounded (fun p d : a.Occurrence => (a.at d).parent = some (a.at p).declaration.id) := by
  apply Subrelation.wf (r := fun p d : a.Occurrence => (a.at p).depth < (a.at d).depth)
  · intro p d hp
    exact h.parent_depth _ (List.getElem_mem _) _ (List.getElem_mem _) hp
  · exact InvImage.wf (fun i : a.Occurrence => (a.at i).depth) Nat.lt_wfRel.wf

theorem AST.WellFormed.super_wellFounded {a : AST} (h : a.WellFormed) :
    WellFounded (fun s d : a.Occurrence =>
      (a.at d).declaration.super = some (a.at s).declaration.id) := by
  obtain ⟨rank, hr⟩ := h.inheritance_rank
  apply Subrelation.wf (r := fun s d : a.Occurrence =>
    rank (a.at s).declaration.id < rank (a.at d).declaration.id)
  · intro s d hs
    exact hr _ (List.getElem_mem _) _ hs
  · exact InvImage.wf (fun i : a.Occurrence => rank (a.at i).declaration.id) Nat.lt_wfRel.wf

end Clafer
