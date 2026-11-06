module

public import Clafer.Constraints.Support
public import DPGraph.Formula

/-!
# Typed resolved core constraints

SoSyM D.1/Figure 28, D.2, D.3.1–2; the Q3 disposition is in docs/sources.md.
These constructors certify sorts and lexical scope. Integer extraction has a
separate partial meaning in Integer.lean; no full evaluator or constraint-
preservation theorem is supplied here.
-/

@[expose] public section
namespace Clafer.Constraints
open CategoryTheory

inductive Collection (s : Support) where
  | objects (element : s.Vertex)
  | relation (source target : s.Vertex)
  deriving DecidableEq

inductive Ty (s : Support) where
  | boolean | integer
  | collection (shape : Collection s)
  deriving DecidableEq

structure Local (s : Support) where
  id : BinderId
  name : String
  element : s.Vertex

/-- A variable is a position in the lexical context, not a textual name.
The nearest binder is first; external boundary binders are outermost first. -/
inductive Var {s : Support} : List (Local s) → s.Vertex → Type where
  | here {b Γ} : Var (b :: Γ) b.element
  | there {b Γ x} : Var Γ x → Var (b :: Γ) x

/-- Primitive recursion remains kernel-reducible. Suppressing native code
generation avoids compiler-generated unsafe helpers for indexed recursion. -/
noncomputable def Var.index {s : Support} {Γ : List (Local s)} {x} (v : Var Γ x) : Nat :=
  Var.rec (motive := fun _ _ _ => Nat) 0 (fun _ n => n + 1) v

theorem Var.index_lt {s : Support} {Γ : List (Local s)} {x} (v : Var Γ x) :
    v.index < Γ.length := by
  induction v with
  | here => simp [index]
  | there v ih => simpa [index] using Nat.succ_lt_succ ih

/-- The position recovers the actual binder metadata and element class. -/
theorem Var.lookup {s : Support} {Γ : List (Local s)} {x} (v : Var Γ x) :
    ∃ b, Γ[v.index]? = some b ∧ b.element = x := by
  induction v with
  | @here b Γ => exact ⟨b, rfl, rfl⟩
  | @there b Γ x v ih => simpa [index] using ih

theorem Var.closed {s : Support} {x} : IsEmpty (@Var s [] x) := ⟨fun v => nomatch v⟩

inductive SetOp where | union | difference | intersection
  deriving DecidableEq, Repr
inductive Arithmetic where | add | subtract
  deriving DecidableEq, Repr

/-- Intrinsically typed deep syntax. A quantifier's variable denotes a singleton
of its domain's element class in the intended interpretation. That interpretation
is not supplied by the constructor. Names may shadow; resolved IDs are fresh. -/
inductive Expr (s : Support) : List (Local s) → Ty s → Type where
  | boolean {Γ} (value : Bool) : Expr s Γ .boolean
  | integer {Γ} (value : Int) : Expr s Γ .integer
  /-- Adopted empty-collection extension (#134) to SoSyM Appendix 4.
  Element-bottom instantiation retains the collection's arity and endpoints;
  it requires neither an object nor an inheritance edge. -/
  | empty {Γ} (shape : Collection s) : Expr s Γ (.collection shape)
  | this {Γ} : Expr s Γ (.collection (.objects s.context))
  /-- Resolved global class extent, including parentless abstract families.
  Appendix 6's global plaECU navigation cannot be a synthetic-root child. -/
  | extent {Γ} (x : s.Vertex) : Expr s Γ (.collection (.objects x))
  | var {Γ x} : Var Γ x → Expr s Γ (.collection (.objects x))
  | map {Γ} (e : s.Edge) : Expr s Γ
      (.collection (.relation (s.mapRef e).source (s.mapRef e).target))
  | and {Γ} : Expr s Γ .boolean → Expr s Γ .boolean → Expr s Γ .boolean
  | not {Γ} : Expr s Γ .boolean → Expr s Γ .boolean
  | equal {Γ t} : Expr s Γ t → Expr s Γ t → Expr s Γ .boolean
  | less {Γ} : Expr s Γ .integer → Expr s Γ .integer → Expr s Γ .boolean
  | arithmetic {Γ} : Arithmetic → Expr s Γ .integer → Expr s Γ .integer → Expr s Γ .integer
  /-- D.3–D.4 bridge: typing identifies the primitive class; runtime
  singleton/domain validity remains a separate obligation. -/
  | integerOf {Γ x} (primitive : s.integer x = true) :
      Expr s Γ (.collection (.objects x)) → Expr s Γ .integer
  | cardinality {Γ k} : Expr s Γ (.collection k) → Expr s Γ .integer
  | setOp {Γ k} : SetOp → Expr s Γ (.collection k) → Expr s Γ (.collection k) →
      Expr s Γ (.collection k)
  | subset {Γ k} : Expr s Γ (.collection k) → Expr s Γ (.collection k) → Expr s Γ .boolean
  | image {Γ x y} : Expr s Γ (.collection (.objects x)) →
      Expr s Γ (.collection (.relation x y)) → Expr s Γ (.collection (.objects y))
  | join {Γ x y z} : Expr s Γ (.collection (.relation x y)) →
      Expr s Γ (.collection (.relation y z)) → Expr s Γ (.collection (.relation x z))
  | widenObjects {Γ x y} : Widen s x y → Expr s Γ (.collection (.objects x)) →
      Expr s Γ (.collection (.objects y))
  | widenRelation {Γ x y x' y'} : Widen s x x' → Widen s y y' →
      Expr s Γ (.collection (.relation x y)) → Expr s Γ (.collection (.relation x' y'))
  | all {Γ} (b : Local s) (fresh : ∀ old ∈ Γ, old.id ≠ b.id)
      (domain : Expr s Γ (.collection (.objects b.element)))
      (body : Expr s (b :: Γ) .boolean) : Expr s Γ .boolean

/-- Explicit `some` elaboration, including the default on a bare navigation.
It is syntax, not a theorem asserting a semantic meaning for cardinality. -/
def Expr.some {s Γ k} (e : Expr s Γ (.collection k)) : Expr s Γ .boolean :=
  .less (.integer 0) (.cardinality e)

def Expr.no {s Γ k} (e : Expr s Γ (.collection k)) : Expr s Γ .boolean :=
  .equal (.cardinality e) (.integer 0)

def Expr.one {s Γ k} (e : Expr s Γ (.collection k)) : Expr s Γ .boolean :=
  .equal (.cardinality e) (.integer 1)

def Expr.lone {s Γ k} (e : Expr s Γ (.collection k)) : Expr s Γ .boolean :=
  .less (.cardinality e) (.integer 2)

def Expr.implies {s Γ} (p q : Expr s Γ .boolean) : Expr s Γ .boolean :=
  .not (.and p (.not q))

def Expr.iff {s Γ} (p q : Expr s Γ .boolean) : Expr s Γ .boolean :=
  .and (p.implies q) (q.implies p)

def Expr.ge {s Γ} (p q : Expr s Γ .integer) : Expr s Γ .boolean :=
  .not (.less p q)

/-- Each step adds a resolved map whose source is the previous endpoint. -/
inductive Path (s : Support) : s.Vertex → s.Vertex → Type where
  | nil (x) : Path s x x
  | cons {x y} (e : s.Edge) (source_eq : (s.mapRef e).source = x)
      (rest : Path s (s.mapRef e).target y) : Path s x y

/-- D.3.2 unary–binary join preserves navigation typing at every step. -/
noncomputable def Path.navigate {s Γ x y} (p : Path s x y)
    (start : Expr s Γ (.collection (.objects x))) : Expr s Γ (.collection (.objects y)) :=
  Path.rec (motive := fun x y _ =>
    Expr s Γ (.collection (.objects x)) → Expr s Γ (.collection (.objects y)))
    (fun _ e => e) (fun e h _ next initial => next (.image initial (h ▸ Expr.map e))) p start

@[simp] theorem Path.navigate_nil {s Γ x} (e : Expr s Γ (.collection (.objects x))) :
    (Path.nil x).navigate e = e := rfl

/-- A constraint carries its entire graph support. There is no independently
chosen arity that can silently drop a referenced map or an isolated vertex. -/
structure Constraint where
  support : Support
  locals : List (Local support)
  body : Expr support locals .boolean

/-- Typed domains for an externally supplied lexical context. Each domain is
checked before its binder enters scope; outer binders are introduced first. -/
inductive Domains (s : Support) : List (Local s) → Type where
  | nil : Domains s []
  | cons {Γ} (b : Local s) (outer : Domains s Γ)
      (fresh : ∀ old ∈ Γ, old.id ≠ b.id)
      (domain : Expr s Γ (.collection (.objects b.element))) : Domains s (b :: Γ)

/-- Explicit compiler input assumptions: resolved/defaulted AST, actual map
incidence, matching context/scope bags, and the outer lexical environment.
External binder domains are supplied by the caller, as in the #3 boundary. -/
structure Constraint.Input (q : Constraint) (a : AST) (c : ConstraintBoundary) : Prop where
  ast : a.WellFormed
  resolved : q.support.Resolved a
  boundary_resolved : c.Resolved a.Known
  boundary : Nonempty (q.support.Boundary c)
  locals_match : (q.locals.reverse.map (fun b => (b.id, b.name))) =
    (c.binders.map (fun b => (b.id, b.name)))
  domains : Nonempty (Domains q.support q.locals)

/-- Attach a body to the boundary's occurrence ID for a later compiler. -/
structure ResolvedConstraint (a : AST) where
  boundary : ConstraintBoundary
  expression : Constraint
  valid : expression.Input a boundary

/-- §6.2.2: syntax-only predicate signature for a selected family of constraints.
An interpretation must be supplied separately before satisfaction is meaningful. -/
def signature {ι : Type} (constraints : ι → Constraint) : DPGraph.Signature where
  Symbol := ι
  arity i := (constraints i).support.graph

def Constraint.formula {ι : Type} (constraints : ι → Constraint) (i : ι)
    {G : Quiv} (binding : (constraints i).support.graph ⥤q G) :
    DPGraph.Formula (signature constraints) G := ⟨i, binding⟩

theorem Constraint.formula_binding {ι : Type} (constraints : ι → Constraint) (i : ι)
    {G : Quiv} (binding : (constraints i).support.graph ⥤q G) :
    (Constraint.formula constraints i binding).binding = binding := rfl

end Clafer.Constraints
