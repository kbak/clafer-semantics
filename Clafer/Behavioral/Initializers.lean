module

public import Clafer.Behavioral.InitializerClassification
public import Clafer.Behavioral.InitializerTransport
public import Clafer.Behavioral.Anchors

/-! # Hard declaration initializers

Behavioral §5 Definitions 3–5 / §6.1, T2/T7–T9, with the accepted #169–#172
initializer extension. Independent equations use original RHS observations;
elaboration introduces an outer birth anchor and an explicit original-context
observation frame. Classification never depends on a satisfying instance.
`Legacy` retains the historical strict implication/default-rejection profile.
-/

@[expose] public section
namespace Clafer.Behavioral.Initializers
universe u
open Transport

inductive Form where
  | constant | initial
  deriving DecidableEq

inductive Clock where
  | everyLive | instanceBirth | parentBirth | globalZero
  deriving DecidableEq

-- [impl->req~behavioral-initializer-contract~1]
/-- The resolved source declaration and original RHS survive inheritance.
The RHS parameter may be any frontend's resolved syntax, with a separate
observation adapter. No parser, name resolution or target backend is imported. -/
structure Obligation (C V : Type) where
  declaration : C
  origin : Transport.Origin
  clock : Clock
  rhs : V

/-- `=` keeps its aggregate every-live clock. Only `:=` invokes the accepted
supported-form classifier and abstract scalar admission. -/
def elaborate {C V : Type} (d : C) (form : Form) (metadata : Classification.Declaration)
    (scalar : Bool) (rhs : V) : Except Classification.Diagnostic (Obligation C V) :=
  let origin := if metadata.parented then Origin.parent else Origin.root
  match form with
  | .constant => .ok ⟨d, origin, .everyLive, rhs⟩
  | .initial => (Classification.classify metadata scalar).map fun clock =>
      ⟨d, origin, match clock with
        | .instanceBirth => .instanceBirth
        | .parentBirth => .parentBirth
        | .globalZero => .globalZero, rhs⟩

/-- Resolved collection/head observations. A collection always keeps the
original declaration view and context; refining it never partitions this view. -/
structure View (U : Type u) where
  contexts : Nat → Set U
  heads : Nat → U → Set U
  instances : Nat → Set U
  target : Nat → U → U

def View.targets {U : Type u} (v : View U) (t : Nat) (p : U) : Set U :=
  v.target t '' v.heads t p

-- [impl->req~behavioral-initializer-contract~1]
/-- Independent meaning: RHS is evaluated in its original enclosing context.
The independent declaration guard never demands an inactive RHS value. -/
def Meaning {C V : Type} {U : Type u} (τ : Trace C U) (v : View U)
    (source : V → Value U (Set U) 0) (o : Obligation C V) : Prop :=
  match o.clock with
  | .everyLive => Candidate.EveryLive τ v.contexts v.heads v.targets
      (fun t p => source o.rhs (.closed p) t)
  | .parentBirth => Candidate.CollectionBirths τ v.contexts v.heads v.targets
      (fun t p => source o.rhs (.closed p) t)
  | .globalZero => Candidate.Guarded (v.heads 0 τ.identities.root)
      (v.targets 0 τ.identities.root) (source o.rhs (.closed τ.identities.root) 0)
  | .instanceBirth => Candidate.SingleBirths τ v.instances v.target
      (fun t x => (original τ.identities o.origin x).bind
        (fun p => source o.rhs (.closed p) t))

/-- A small generated atom language. The source RHS is kept opaque to generated
binders and evaluated by its independent original-context adapter. -/
inductive Equation (V : Type) (_n : Nat) where
  | singleton (origin : Transport.Origin) (rhs : V)
  | aggregate (rhs : V)

-- [impl->req~behavioral-environments~1]
noncomputable def observation {C V : Type} {U : Type u} (τ : Trace C U) (v : View U)
    (source : V → Value U (Set U) 0) : PartialObservation (Equation V) (fun _ => Empty) U := by
  classical
  exact {
  atom a ρ t := match a with
    | .singleton origin rhs =>
        ((attach τ.identities origin Fin.elim0 ρ.this).bind
          (fun f => moved (source rhs) f t)).map (fun S => S = {v.target t ρ.this})
    | .aggregate rhs =>
        if (v.heads t ρ.this).Nonempty then
          (source rhs (.closed ρ.this) t).map (fun S => S = v.targets t ρ.this)
        else some True
  domain d := nomatch d }

def expansion {C V : Type} (o : Obligation C V) : Formula (Equation V) (fun _ => Empty) 0 :=
  match o.clock with
  | .everyLive => .atom (.aggregate o.rhs)
  | .instanceBirth => .initially (.atom (.singleton o.origin o.rhs))
  | .parentBirth | .globalZero => .initially (.atom (.aggregate o.rhs))

def attachments {C V : Type} {U : Type u} (τ : Trace C U) (v : View U)
    (o : Obligation C V) : Nat → Set U :=
  match o.clock with
  | .instanceBirth => v.instances
  | .globalZero => fun _ => {τ.identities.root}
  | .everyLive | .parentBirth => v.contexts

-- [proof->req~behavioral-reference-atoms~1]
theorem atom_satisfies {C : Type} {U : Type u} {A D : Nat → Type} {n : Nat}
    (τ : Trace C U) (O : PartialObservation A D U) (a : A n) (ρ : Environment U n) (t : Nat) :
    (Formula.atom a).Satisfies τ O true ρ t ↔ ∃ p, O.atom a ρ t = some p ∧ p := by
  cases h : O.atom a ρ t with
  | none => simp [Formula.Satisfies, Formula.Defined, h]
  | some p =>
    simp only [Formula.Satisfies, Formula.Defined, Formula.denote,
      PartialObservation.canonical, PartialObservation.complete, polarity, h,
      Option.some.injEq, Option.getD_some, ite_true]
    constructor
    · rintro ⟨_, hp⟩; exact ⟨p, rfl, hp⟩
    · rintro ⟨q, eq, hq⟩; subst q; exact ⟨⟨p, rfl⟩, hq⟩

private theorem map_equation {U : Type u} (r : Option (Set U)) (S : Set U) :
    (∃ p, r.map (fun T => T = S) = some p ∧ p) ↔ r = some S := by
  cases r with
  | none => simp
  | some T =>
    constructor
    · rintro ⟨p, eq, hp⟩
      have eq' : (T = S) = p := Option.some.inj eq
      subst p
      exact congrArg some hp
    · intro eq
      exact ⟨T = S, rfl, Option.some.inj eq⟩

-- [proof->req~behavioral-environments~1]
theorem singleton_observation {C V : Type} {U : Type u} (τ : Trace C U) (v : View U)
    (source : V → Value U (Set U) 0) (origin : Transport.Origin) (rhs : V) (x : U) (t : Nat) :
    (Formula.atom (.singleton origin rhs)).Satisfies τ (observation τ v source) true (.closed x) t ↔
      (original τ.identities origin x).bind (fun p => source rhs (.closed p) t) =
        some {v.target t x} := by
  rw [atom_satisfies]
  change (∃ p, (((attach τ.identities origin Fin.elim0 x).bind
    (fun f => moved (source rhs) f t)).map (fun S => S = {v.target t x})) = some p ∧ p) ↔ _
  rw [map_equation]
  simp only [attach, Option.bind_map, moved]
  rfl

theorem aggregate_observation {C V : Type} {U : Type u} (τ : Trace C U) (v : View U)
    (source : V → Value U (Set U) 0) (rhs : V) (p : U) (t : Nat) :
    (Formula.atom (.aggregate rhs)).Satisfies τ (observation τ v source) true (.closed p) t ↔
      Candidate.Guarded (v.heads t p) (v.targets t p) (source rhs (.closed p) t) := by
  classical
  rw [atom_satisfies]
  change (∃ q, (if (v.heads t p).Nonempty then
    (source rhs (.closed p) t).map (fun S => S = v.targets t p) else some True) = some q ∧ q) ↔ _
  by_cases present : (v.heads t p).Nonempty
  · rw [ite_eq_left present, map_equation, Candidate.nonempty_guard present]
  · rw [ite_eq_right present]
    constructor
    · intro _; exact fun h => (present h).elim
    · intro _; exact ⟨True, rfl, trivial⟩

-- [proof->req~behavioral-initializer-contract~1]
/-- The outer anchor uses the child for singles, original parent for collections,
and permanent root for globals. RHS attachment is unchanged in every case. -/
theorem expansion_agrees {C V : Type} {U : Type u} (τ : Trace C U) (v : View U)
    (source : V → Value U (Set U) 0) (o : Obligation C V)
    (rootLive : ∀ t, τ.identities.root ∈ τ.live t) :
    (expansion o).PartialAttached τ (observation τ v source) (attachments τ v o) ↔
      Meaning τ v source o := by
  cases o with
  | mk d origin clock rhs =>
    cases clock with
    | everyLive =>
      simp only [expansion, attachments, Meaning, Formula.PartialAttached,
        aggregate_observation, Candidate.EveryLive]
    | instanceBirth =>
      rw [show expansion (⟨d, origin, .instanceBirth, rhs⟩ : Obligation C V) =
        Formula.initially (.atom (.singleton origin rhs)) from rfl, Anchors.initially_at_births]
      simp only [Anchors.AtBirths, attachments, singleton_observation, Meaning,
        Candidate.SingleBirths]
    | parentBirth =>
      rw [show expansion (⟨d, origin, .parentBirth, rhs⟩ : Obligation C V) =
        Formula.initially (.atom (.aggregate rhs)) from rfl, Anchors.initially_at_births]
      simp only [Anchors.AtBirths, attachments, aggregate_observation, Meaning,
        Candidate.CollectionBirths]
    | globalZero =>
      rw [show expansion (⟨d, origin, .globalZero, rhs⟩ : Obligation C V) =
        Formula.initially (.atom (.aggregate rhs)) from rfl, Anchors.initially_at_births]
      change (∀ t p, p ∈ ({τ.identities.root} : Set U) → τ.Starts t p → _) ↔ _
      simp only [aggregate_observation]
      exact Candidate.permanent_context_iff τ τ.identities.root rootLive v.heads v.targets
        (fun t p => source rhs (.closed p) t)

-- [proof->req~behavioral-initializer-contract~1]
theorem ordinary_initial_supported {C V : Type} (d : C) (rhs : V) (g : GroupCard) :
    elaborate d .initial ⟨false, true, none, g⟩ false rhs =
      .ok ⟨d, .parent, .instanceBirth, rhs⟩ := by
  simp [elaborate, Classification.ordinary_default_single, Except.map]

/-- All obligations are hard constraints on one trace. Order never supplies an
assignment sequence or changes the values observed at simultaneous births. -/
def Bundle {C V : Type} {U : Type u} (τ : Trace C U) (views : C → View U)
    (source : V → Value U (Set U) 0) (obligations : List (Obligation C V)) : Prop :=
  ∀ o ∈ obligations, Meaning τ (views o.declaration) source o

-- [proof->req~behavioral-initializer-contract~1]
theorem bundle_append {C V : Type} {U : Type u} (τ : Trace C U) (views : C → View U)
    (source : V → Value U (Set U) 0) (own inherited : List (Obligation C V)) :
    Bundle τ views source (own ++ inherited) ↔
      Bundle τ views source own ∧ Bundle τ views source inherited := by
  simp [Bundle, List.mem_append, or_imp, forall_and]

theorem bundle_order {C V : Type} {U : Type u} (τ : Trace C U) (views : C → View U)
    (source : V → Value U (Set U) 0) (a b : List (Obligation C V)) (same : a.Perm b) :
    Bundle τ views source a ↔ Bundle τ views source b := by
  simp only [Bundle, same.mem_iff]

end Clafer.Behavioral.Initializers
