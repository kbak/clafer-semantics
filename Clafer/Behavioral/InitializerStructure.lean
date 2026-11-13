module

public import Clafer.Behavioral.Initializers
public import Clafer.Behavioral.Modifiers

/-! # Initializers over valid resolved structural observations

Behavioral §5 Definitions 2–5 and §6.1; accepted #170/#171. The original
abstract declaration view determines scope; subtype refinement changes neither
clock nor RHS attachment. Reference coherence supplies the shared target.
-/

@[expose] public section
namespace Clafer.Behavioral.Initializers.Structure
universe u
open Semantics ReferenceObservation
variable {k : Nat} {U : Type u} (m : Structural.Core k) (τ : Trace (Fin k) U)

-- [impl->req~behavioral-initializer-contract~1]
def metadata (d : Fin k) (authored : Option DPGraph.Predicates.Range) :
    Classification.Declaration where
  abstract := m.authoredAbstract d
  parented := (m.family.parent d).isSome
  authored := authored
  parentGroup := match m.family.parent d with
    | none => .bounds unrestricted
    | some p => (m.family.group p).effective

/-- Entry point for an already resolved structural declaration. The caller
retains authored/default provenance and supplies independently justified scalar
admission; effective abstractness/group/parent data are read from the core. -/
def elaborate {V : Type} (d : Fin k) (form : Form)
    (authored : Option DPGraph.Predicates.Range) (scalar : Bool) (rhs : V) :
    Except Classification.Diagnostic (Obligation (Fin k) V) :=
  Initializers.elaborate d form (metadata m d authored) scalar rhs

def origin (d : Fin k) : Transport.Origin :=
  if (m.family.parent d).isSome then .parent else .root

def contexts (d : Fin k) (t : Nat) : Set U :=
  match m.family.parent d with
  | none => {τ.identities.root}
  | some p => (τ.raw m.toEffectiveCore t).head p

def heads (d : Fin k) (t : Nat) (p : U) : Set U :=
  match m.family.parent d with
  | none => (τ.raw m.toEffectiveCore t).head d
  | some _ => ReferenceObservation.heads (Structural.current m τ t) d p

/-- Chosen only from a proved unique reference, with an irrelevant fallback
outside the declaration's live heads. No initializer equation is a premise. -/
noncomputable def target (valid : Structural.Valid m τ) {d o : Fin k}
    (owner : InheritedReference.Owner m.family d o) (t : Nat) (x : U) : U :=
  by
  classical
  exact if h : x ∈ (τ.raw m.toEffectiveCore t).head d then
    (valid.inherited_reference owner h).choose else τ.identities.root

-- [proof->req~behavioral-reference-atoms~1]
theorem target_link (valid : Structural.Valid m τ) {d o : Fin k}
    (owner : InheritedReference.Owner m.family d o) (t : Nat) (x : U)
    (live : x ∈ (τ.raw m.toEffectiveCore t).head d) :
    InheritedReference.deref m.family (τ.raw m.toEffectiveCore t) d x
      (target m τ valid owner t x) := by
  simpa only [target, dite_eq_left live] using (valid.inherited_reference owner live).choose_spec.1

theorem target_singleton (valid : Structural.Valid m τ) {d o : Fin k}
    (owner : InheritedReference.Owner m.family d o) (t : Nat) (x : U)
    (live : x ∈ (τ.raw m.toEffectiveCore t).head d) :
    {y | (Structural.current m τ t).deref d x y} = {target m τ valid owner t x} := by
  ext y
  constructor
  · intro hy
    exact valid.refined_reference_agrees hy (target_link m τ valid owner t x live)
  · rintro rfl
    exact target_link m τ valid owner t x live

/-- Even refined reference owners observe one target for the shared identity. -/
theorem shared_target (valid : Structural.Valid m τ) {d e o q : Fin k}
    (od : InheritedReference.Owner m.family d o) (oe : InheritedReference.Owner m.family e q)
    (t : Nat) (x : U) (hd : x ∈ (τ.raw m.toEffectiveCore t).head d)
    (he : x ∈ (τ.raw m.toEffectiveCore t).head e) :
    target m τ valid od t x = target m τ valid oe t x :=
  valid.refined_reference_agrees (target_link m τ valid od t x hd)
    (target_link m τ valid oe t x he)

-- [impl->req~behavioral-initializer-contract~1]
noncomputable def view (valid : Structural.Valid m τ) {d o : Fin k}
    (owner : InheritedReference.Owner m.family d o) : View U where
  contexts := contexts m τ d
  heads := heads m τ d
  instances t := (τ.raw m.toEffectiveCore t).head d
  target := target m τ valid owner

-- [proof->req~behavioral-environments~1]
/-- Fixed ownership, obtained from actual containment, constructs the original
RHS frame. The theorem holds at every later observation time, including absence. -/
theorem parent_rhs {d : Fin k} {p x : U} {t : Nat}
    (owned : (τ.raw m.toEffectiveCore t).contains d p x)
    (rhs : Transport.Value U (Set U) 0) (j : Nat) :
    (Transport.attach τ.identities .parent Fin.elim0 x).bind
      (fun f => Transport.moved rhs f j) = rhs (.closed p) j :=
  Transport.attached_parent_observation τ.identities rhs Fin.elim0 x p owned.1.2.2 j

theorem head_mem {d : Fin k} {t : Nat} {p x : U} (h : x ∈ heads m τ d t p) :
    x ∈ (τ.raw m.toEffectiveCore t).head d := by
  unfold heads at h
  split at h
  · exact h
  · exact ⟨h.1.2.1, h.2.1⟩

/-- Connect the selected target function to the complete inherited target image.
For parentless abstracts this image spans all concrete realizations and parents. -/
theorem target_image (valid : Structural.Valid m τ) {d o : Fin k}
    (owner : InheritedReference.Owner m.family d o) (t : Nat) (p : U) :
    (view m τ valid owner).targets t p =
      {y | ∃ x ∈ heads m τ d t p, (Structural.current m τ t).deref d x y} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, target_link m τ valid owner t x (head_mem m τ hx)⟩
  · rintro ⟨x, hx, link⟩
    exact ⟨x, hx, valid.refined_reference_agrees
      (target_link m τ valid owner t x (head_mem m τ hx)) link⟩

-- [proof->req~behavioral-environments~1]
theorem fiber_origin {d : Fin k} {t : Nat} {p x : U}
    (hp : p ∈ contexts m τ d t) (hx : x ∈ heads m τ d t p) :
    Transport.original τ.identities (origin m d) x = some p := by
  cases parent : m.family.parent d with
  | none =>
    have eq : p = τ.identities.root := by simpa [contexts, parent] using hp
    subst p
    simp [origin, parent, Transport.original]
  | some c =>
    have owned : (τ.raw m.toEffectiveCore t).contains d p x := by
      simpa only [heads, parent, ReferenceObservation.heads, Structural.current, Set.mem_ofPred_eq, Structural.observed_contains] using hx
    simpa [origin, parent, Transport.original] using owned.1.2.2

theorem fibers_cover (valid : Structural.Valid m τ) {d : Fin k} {t : Nat} {x : U}
    (hx : x ∈ (τ.raw m.toEffectiveCore t).head d) :
    ∃ p, p ∈ contexts m τ d t ∧ x ∈ heads m τ d t p := by
  cases parent : m.family.parent d with
  | none => exact ⟨τ.identities.root, by simp [contexts, parent], by simpa [heads, parent]⟩
  | some c =>
    obtain ⟨p, owned, _⟩ := (valid.states t).parents d c parent x hx
    obtain ⟨_, c', parent', hp⟩ := (valid.states t).typed.1 d p x owned
    have eq : c' = c := Option.some.inj (parent'.symm.trans parent)
    subst c'
    exact ⟨p, by simpa [contexts, parent] using hp, by simpa only [heads, parent, ReferenceObservation.heads, Structural.current, Set.mem_ofPred_eq, Structural.observed_contains] using owned⟩

theorem contexts_live (valid : Structural.Valid m τ) (d : Fin k) (t : Nat) :
    contexts m τ d t ⊆ τ.live t := by
  intro p hp
  cases parent : m.family.parent d with
  | none =>
    have eq : p = τ.identities.root := by simpa [contexts, parent] using hp
    exact eq ▸ valid.root_live t
  | some c => exact (show p ∈ (τ.raw m.toEffectiveCore t).head c from
      by simpa [contexts, parent] using hp).1

/-- Original context equality is derived from the source fiber, rather than
postulated as equality between arbitrary RHS observation functions. -/
theorem single_fibers {V : Type} (valid : Structural.Valid m τ) {d o : Fin k}
    (owner : InheritedReference.Owner m.family d o)
    (source : V → Transport.Value U (Set U) 0) (rhs : V) :
    Meaning τ (view m τ valid owner) source ⟨d, origin m d, .instanceBirth, rhs⟩ ↔
      ∀ t p, p ∈ contexts m τ d t → ∀ x ∈ heads m τ d t p, τ.Starts t x →
        source rhs (.closed p) t = some {target m τ valid owner t x} := by
  constructor
  · intro h t p hp x hx birth
    have eq := h t x (head_mem m τ hx) birth
    change (Transport.original τ.identities (origin m d) x).bind _ = _ at eq
    simpa only [fiber_origin m τ hp hx, Option.bind_some, view] using eq
  · intro h t x hx birth
    obtain ⟨p, hp, owned⟩ := fibers_cover m τ valid hx
    change (Transport.original τ.identities (origin m d) x).bind _ = _
    rw [fiber_origin m τ hp owned, Option.bind_some]
    exact h t p hp x owned birth

-- [proof->req~behavioral-initializer-contract~1]
theorem every_fibers {V : Type} (valid : Structural.Valid m τ) {d o : Fin k}
    (owner : InheritedReference.Owner m.family d o)
    (source : V → Transport.Value U (Set U) 0) (rhs : V)
    (admission : ∀ t p, p ∈ contexts m τ d t →
      (heads m τ d t p).Subsingleton ∨
        ∀ S, source rhs (.closed p) t = some S → S.Subsingleton) :
    Meaning τ (view m τ valid owner) source ⟨d, origin m d, .everyLive, rhs⟩ ↔
      ∀ t x, x ∈ (τ.raw m.toEffectiveCore t).head d →
        (Transport.original τ.identities (origin m d) x).bind
          (fun p => source rhs (.closed p) t) = some {target m τ valid owner t x} := by
  have grouping (t : Nat) (p : U) (hp : p ∈ contexts m τ d t) :
      Candidate.Guarded (heads m τ d t p) ((view m τ valid owner).targets t p)
        (source rhs (.closed p) t) ↔
      ∀ x ∈ heads m τ d t p, source rhs (.closed p) t = some {target m τ valid owner t x} := by
    rcases admission t p hp with one | scalar
    · exact Bounds.aggregate_iff_singletons_of_head_bound _ _ _ one
    · exact Bounds.aggregate_iff_singletons _ _ _ scalar
  constructor
  · intro h t x hx
    obtain ⟨p, hp, owned⟩ := fibers_cover m τ valid hx
    rw [fiber_origin m τ hp owned, Option.bind_some]
    exact (grouping t p hp).mp (h t p hp (contexts_live m τ valid d t hp)) x owned
  · intro h t p hp _
    apply (grouping t p hp).mpr
    intro x hx
    have eq := h t x (head_mem m τ hx)
    simpa only [fiber_origin m τ hp hx, Option.bind_some] using eq

-- [proof->req~behavioral-initializer-contract~1]
/-- Effective inherited obligations retain their entire authored record. -/
def Effective {V : Type} (declared : Fin k → Set (Obligation (Fin k) V))
    (d : Fin k) (obligation : Obligation (Fin k) V) : Prop :=
  ∃ a, m.toEffectiveCore.Ancestor d a ∧ obligation ∈ declared a

theorem effective_own {V : Type} (declared : Fin k → Set (Obligation (Fin k) V))
    (d : Fin k) (o : Obligation (Fin k) V) (h : o ∈ declared d) :
    Effective m declared d o := ⟨d, .refl, h⟩

theorem effective_inherited {V : Type} (declared : Fin k → Set (Obligation (Fin k) V))
    {d a : Fin k} {o : Obligation (Fin k) V} (edge : m.family.super d = some a)
    (h : Effective m declared a o) : Effective m declared d o := by
  obtain ⟨b, path, hb⟩ := h
  exact ⟨b, path.head edge, hb⟩

/-- A parent replacement cannot reuse its predecessor's child identity, even
across absent intervals; each new child is initialized in its own fixed context. -/
theorem replacement_child_distinct {i j : Nat} {p q x y : U}
    (before : τ.ParentAt i p x) (after : τ.ParentAt j q y) (different : p ≠ q) : x ≠ y := by
  rintro rfl
  exact different (τ.parent_stable before after)

-- [proof->req~behavioral-initializer-contract~1]
/-- A live child of a newly born parent must itself be newly born. Fixed
ownership plus parent liveness excludes carrying a live child across replacement. -/
theorem child_birth_of_parent_birth (valid : Structural.Valid m τ) {t : Nat} {x p : U}
    (parent : τ.identities.parent x = some p) (child : x ∈ τ.live t)
    (birth : τ.Starts t p) : τ.Starts t x := by
  rcases birth.2 with zero | ⟨i, eq, absent⟩
  · subst t; exact (τ.starts_zero x).mpr child
  · subst t
    exact (τ.starts_succ i x).mpr ⟨child, fun h => absent (valid.parent_live i x p h parent)⟩

/-- Source/elaboration consequence at a fresh parent: the new child's equation
observes that parent's original context. `expansion_agrees` supplies this premise
from the generated initially formula without assuming RHS equality. -/
theorem parent_birth_initializes_child {V : Type} (valid : Structural.Valid m τ)
    {d o : Fin k} (owner : InheritedReference.Owner m.family d o)
    (source : V → Transport.Value U (Set U) 0) (rhs : V)
    (init : Meaning τ (view m τ valid owner) source ⟨d, origin m d, .instanceBirth, rhs⟩)
    {t : Nat} {p x : U} (context : p ∈ contexts m τ d t)
    (child : x ∈ heads m τ d t p) (owned : τ.identities.parent x = some p)
    (birth : τ.Starts t p) : source rhs (.closed p) t = some {target m τ valid owner t x} :=
  (single_fibers m τ valid owner source rhs).mp init t p context x child
    (child_birth_of_parent_birth m τ valid owned (head_mem m τ child).1 birth)

end Clafer.Behavioral.Initializers.Structure
