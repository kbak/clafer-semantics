module

public import Clafer.Compile.GroupSemantics
public import Clafer.Semantics.Abstracts
public import Clafer.Semantics.Bridge

/-!
# Selected inherited realization

SoSyM §5.3.4–5, §5.5 and Appendix 6, with the D2/D4/D6 clarification in
`docs/inherited-realization.md`. This extension retains authored provenance;
Authored realization and effective-core checking share #87 declaration disjointness.
-/

@[expose] public section
namespace Clafer.Semantics.Realization
open CategoryTheory MCS Compile DPGraph DPGraph.Predicates

structure Core (n : Nat) extends EffectiveCore n where
  explicitAbstract : Fin n → Bool

namespace Core
variable {n : Nat} (m : Core n)

/-- Only the combinations needed by Appendix 6. Explicit nested abstracts and
reference-super refinement are not admitted by this selected extension. -/
def Selected : Prop :=
  (∀ d, m.explicitAbstract d = true →
    m.family.isAbstract d = true ∧ m.family.parent d = none) ∧
  (∀ d, m.family.parent d = none → m.family.isAbstract d = true →
    m.explicitAbstract d = true) ∧
  (∀ d c, m.family.super d = some c →
    m.explicitAbstract c = true ∧ m.family.reference c = .basic) ∧
  (∀ d t, (m.family.reference d).target = some t → (m.family.parent d).isSome = true) ∧
  (∃ rank : Fin n → Nat,
    (∀ d c, m.explicitAbstract d = true → m.family.super c = some d → rank c < rank d) ∧
    (∀ d p, m.explicitAbstract d = false → m.family.parent d = some p → rank p < rank d))

/-- No recovery of authored provenance from the erased effective flag. -/
noncomputable def ofInput {a : AST} (i : Input a) : Core a.entries.length where
  toEffectiveCore := EffectiveCore.erase i
  explicitAbstract d := (a.at d).declaration.authoredAbstract

@[simp] theorem forget_input {a : AST} (i : Input a) :
    (ofInput i).toEffectiveCore = EffectiveCore.erase i := rfl

end Core

variable {n : Nat} {U : Type} (m : Core n) (s : Configuration (Fin n) U)

/-- Explicit subtype coverage and contextual field membership remain separate. -/
def Abstracts : Prop :=
  ∀ d, m.explicitAbstract d = true →
    (∀ x, x ∈ s.head d → ∃ c, m.family.super c = some d ∧ x ∈ s.head c) ∧
    (∀ c e, m.family.super c = some d → m.family.super e = some d → c ≠ e →
      ∀ x, ¬ (x ∈ s.head c ∧ x ∈ s.head e))

/-- Telematics.Structural effective abstractness does not suppress an ordinary field's
resolved group. Explicit abstract groups retain #65's template/override policy. -/
def Groups : Prop := ∀ d, m.explicitAbstract d = false → Compile.Groups.Holds m.family s d

-- [impl->req~clafer-inherited-realization~1]
def Satisfies : Prop :=
  s.Typed m.toEffectiveCore ∧ s.Rooted m.toEffectiveCore ∧
  s.LocalConditions m.toEffectiveCore ∧ Abstracts m s ∧ Groups m s ∧
  s.DeclarationDisjoint m.toEffectiveCore

theorem abstracts_generic (inh : s.Inherits m.toEffectiveCore) : Abstracts m s ↔
    ∀ d, m.explicitAbstract d = true →
      Cover (s.abstractFan m.toEffectiveCore inh d) ∧
      DPGraph.Predicates.Disjoint (s.abstractFan m.toEffectiveCore inh d) := by
  simp only [Abstracts, Configuration.abstract_cover_iff, Configuration.abstract_disjoint_iff]

theorem explicit_leaf_empty (h : Abstracts m s) (d : Fin n)
    (hd : m.explicitAbstract d = true) (leaf : ∀ c, m.family.super c ≠ some d) :
    s.head d = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨c, hc, _⟩ := (h d hd).1 x hx
  exact leaf c hc

theorem ancestor_subset (inh : s.Inherits m.toEffectiveCore) {q p : Fin n}
    (path : Compile.Groups.Ancestor m.family q p) : s.head q ⊆ s.head p := by
  induction path with
  | refl => exact fun _ h => h
  | @tail b c _ edge ih => exact fun x h => inh b c edge x (ih h)

/-- Contextual classification of existing objects, never a new occurrence. -/
def View (f q : Fin n) : Set U :=
  {x | x ∈ s.head f ∧ ∃ p, s.contains f p x ∧ p ∈ s.head q}

def Contains (f q : Fin n) (p x : U) : Prop :=
  p ∈ s.head q ∧ s.contains f p x

def Deref (f q : Fin n) (x t : U) : Prop :=
  x ∈ View s f q ∧ s.deref f x t

theorem view_subset (f q : Fin n) : View s f q ⊆ s.head f := fun _ h => h.1

theorem view_mono (f : Fin n) {q p : Fin n} (h : s.head q ⊆ s.head p) :
    View s f q ⊆ View s f p := by
  rintro x ⟨hx, y, hy, hq⟩
  exact ⟨hx, y, hy, h hq⟩

theorem same_parent_fiber (f q p : Fin n) (x : U)
    (hq : x ∈ s.head q) (hp : x ∈ s.head p) :
    Contains s f q x = Contains s f p x := by
  funext y
  exact propext (by simp [Contains, hq, hp])

/-- Unique ownership derives a partition only for disjoint parent alternatives.
No disjointness is imposed between ancestor and descendant views. -/
theorem disjoint_views (parents : s.Parents m.toEffectiveCore)
    {f p q r : Fin n} (hf : m.family.parent f = some p)
    (disj : _root_.Disjoint (s.head q) (s.head r)) :
    _root_.Disjoint (View s f q) (View s f r) := by
  rw [Set.disjoint_left] at disj ⊢
  rintro x ⟨hx, a, ha, hqa⟩ ⟨_, b, hb, hrb⟩
  have he := (parents f p hf x hx).unique ha hb
  exact disj hqa (he.symm ▸ hrb)

-- [proof->req~clafer-inherited-realization~1]
/-- Actual coverage of the parent's objects yields coverage of its fields.
No independent field-cover equivalence is accepted as an input. -/
theorem view_cover (typed : s.Typed m.toEffectiveCore)
    (parents : s.Parents m.toEffectiveCore) {f p : Fin n}
    (hf : m.family.parent f = some p) {I : Type} (contexts : I → Fin n)
    (cover : ∀ x, x ∈ s.head p → ∃ j, x ∈ s.head (contexts j)) :
    ∀ x, x ∈ s.head f → ∃ j, x ∈ View s f (contexts j) := by
  intro x hx
  obtain ⟨y, hy, _⟩ := parents f p hf x hx
  obtain ⟨_, c, hc, hcy⟩ := typed.1 f y x hy
  have he : c = p := Option.some.inj (hc.symm.trans hf)
  obtain ⟨j, hj⟩ := cover y (he ▸ hcy)
  exact ⟨j, hx, y, hy, hj⟩

theorem abstract_parent_cover (typed : s.Typed m.toEffectiveCore)
    (parents : s.Parents m.toEffectiveCore) (abs : Abstracts m s)
    {f p : Fin n} (hf : m.family.parent f = some p)
    (hp : m.explicitAbstract p = true) :
    ∀ x, x ∈ s.head f → ∃ c, m.family.super c = some p ∧ x ∈ View s f c := by
  intro x hx
  obtain ⟨y, hy, _⟩ := parents f p hf x hx
  obtain ⟨_, c, hc, hcy⟩ := typed.1 f y x hy
  have he : c = p := Option.some.inj (hc.symm.trans hf)
  obtain ⟨q, hq, hyq⟩ := (abs p hp).1 y (he ▸ hcy)
  exact ⟨q, hq, hx, y, hy, hyq⟩

/-- Scope transport for #68/#69 is parametric in the body predicate; it does
not assume or provide an expression evaluator. -/
theorem constraint_on_subtype (inh : s.Inherits m.toEffectiveCore)
    {q p : Fin n} (path : Compile.Groups.Ancestor m.family q p)
    (body : U → Prop) (h : ∀ x, x ∈ s.head p → body x) :
    ∀ x, x ∈ s.head q → body x := fun x hx => h x (ancestor_subset m s inh path hx)

theorem constraint_on_view (f q : Fin n) (body : U → Prop)
    (h : ∀ x, x ∈ s.head f → body x) :
    ∀ x, x ∈ View s f q → body x := fun x hx => h x hx.1

theorem context_parents (parents : s.Parents m.toEffectiveCore)
    {f p q : Fin n} (hf : m.family.parent f = some p) {x : U}
    (hx : x ∈ View s f q) : ∃! y, Contains s f q y x := by
  obtain ⟨y,hy,hq⟩ := hx.2
  exact ⟨y,⟨hq,hy⟩,fun z hz => (parents f p hf x hx.1).unique hz.2 hy⟩

theorem context_references (refs : s.References m.toEffectiveCore)
    {f t q : Fin n} (hf : (m.family.reference f).target = some t) {x : U}
    (hx : x ∈ View s f q) : ∃! y, Deref s f q x y := by
  obtain ⟨y,hy,hu⟩ := refs f t hf x hx.1
  exact ⟨y,⟨hx,hy⟩,fun z hz => hu z hz.2⟩

theorem context_multiplicity (inh : s.Inherits m.toEffectiveCore)
    (mult : s.Multiplicities m.toEffectiveCore) {f p q : Fin n}
    (hf : m.family.parent f = some p) (path : Compile.Groups.Ancestor m.family q p)
    (x : U) (hx : x ∈ s.head q) :
    InRange (m.family.multiplicity f) {y : U // Contains s f q x y} := by
  apply (inRange_iff _ (Equiv.subtypeEquivRight (fun y =>
    show Contains s f q x y ↔ s.contains f x y by simp [Contains,hx]))).mpr
  exact mult f p hf x (ancestor_subset m s inh path hx)

/-- Restrict the original containment LINKS by parent membership. Forgetting
this subtype is injective and retains both original endpoints. -/
def headView (f q : Fin n) : Span (s.head q) (View s f q) where
  Link := {l : (s.headMap m.toEffectiveCore f).Link //
    ((s.headMap m.toEffectiveCore f).source l).val ∈ s.head q}
  source l := ⟨l.val.val.1.val, l.property⟩
  target l := ⟨l.val.val.2.val, l.val.val.2.property,
    l.val.val.1.val, l.val.property, l.property⟩

def derefView (f q : Fin n) :
    Span (View s f q) (s.head ((m.family.reference f).target.getD f)) where
  Link := {l : (s.derefMap m.toEffectiveCore f).Link //
    ((s.derefMap m.toEffectiveCore f).source l).val ∈ View s f q}
  source l := ⟨l.val.val.1.val, l.property⟩
  target l := l.val.val.2

def parentView (f q : Fin n) := (headView m s f q).inverse

theorem view_inverse (f q : Fin n) :
    Inverse (headView m s f q) (parentView m s f q) := ⟨Span.Iso.refl _⟩

def targetView (f q : Fin n) := (headView m s f q).comp (derefView m s f q)

theorem head_links_injective (f q : Fin n) :
    Function.Injective (fun l : (headView m s f q).Link => l.val) := Subtype.val_injective

theorem deref_links_injective (f q : Fin n) :
    Function.Injective (fun l : (derefView m s f q).Link => l.val) := Subtype.val_injective

theorem view_commutes (f q : Fin n) :
    Commutation (headView m s f q) (derefView m s f q) (targetView m s f q) :=
  ⟨Span.Iso.refl _⟩

theorem head_view_relation (typed : s.Typed m.toEffectiveCore) (f q : Fin n)
    (p : s.head q) (x : View s f q) :
    (headView m s f q).red p x ↔ s.contains f p.val x.val := by
  constructor
  · rintro ⟨l, hp, hx⟩
    have hp' := congrArg Subtype.val hp
    have hx' := congrArg Subtype.val hx
    exact hp' ▸ hx' ▸ l.val.property
  · intro h
    obtain ⟨hx, c, hc, hp⟩ := typed.1 f p.val x.val h
    exact ⟨⟨⟨(⟨p.val, by simpa [hc] using hp⟩, ⟨x.val, hx⟩), h⟩, p.property⟩,
      rfl, rfl⟩

theorem deref_view_relation (f q : Fin n) (x : View s f q)
    (t : s.head ((m.family.reference f).target.getD f)) :
    (derefView m s f q).red x t ↔ s.deref f x.val t.val := by
  constructor
  · rintro ⟨l, hx, ht⟩
    have hx' := congrArg Subtype.val hx
    have ht' := congrArg Subtype.val ht
    exact hx' ▸ ht' ▸ l.val.property
  · intro h
    exact ⟨⟨⟨(⟨x.val, x.property.1⟩, t), h⟩, x.property⟩, rfl, rfl⟩

/-- Contextual references cannot select a different target from the original. -/
theorem deref_agrees (refs : s.References m.toEffectiveCore)
    {f q t : Fin n} (hf : (m.family.reference f).target = some t)
    {x y z : U} (hv : Deref s f q x y) (hz : s.deref f x z) : y = z :=
  (refs f t hf x hv.1.1).unique hv.2 hz

/-- Distinct realized owners cannot share an owned occurrence. -/
theorem owner_agrees (parents : s.Parents m.toEffectiveCore)
    {f p : Fin n} (hf : m.family.parent f = some p) {x y z : U}
    (hx : x ∈ s.head f) (hy : s.contains f y x) (hz : s.contains f z x) : y = z :=
  (parents f p hf x hx).unique hy hz

/-- Forget only the restriction proofs. The composable pair of original links
is retained; equal reference targets cannot collapse two occurrences (Q1). -/
def targetLink (f q : Fin n) (l : (targetView m s f q).Link) :
    (s.targetMap m.toEffectiveCore f).Link :=
  ⟨(l.val.1.val, l.val.2.val), Subtype.ext (congrArg (fun x : View s f q => x.val) l.property)⟩

theorem target_links_injective (f q : Fin n) :
    Function.Injective (targetLink m s f q) := by
  intro l k h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z => z.val.1) h
  · apply Subtype.ext
    exact congrArg (fun z => z.val.2) h

/-- The selected inherited child maps count the same existing objects. -/
theorem child_view_iff (q : Fin n) (x y : U) (hx : x ∈ s.head q) :
    Compile.Groups.ChildObjects m.family s q x y ↔
      ∃ a, Compile.Groups.Ancestor m.family q a ∧
        ∃ f, m.family.parent f = some a ∧ Contains s f q x y := by
  simp [Compile.Groups.ChildObjects, Contains, hx]

/-- Grounded realization excludes recursive orphan islands. Cover follows an
explicit subtype; an ordinary field follows its unique actual parent. -/
theorem reaches (wf : m.toEffectiveCore.WellFormed) (selected : m.Selected)
    (h : Satisfies m s) (x : U) : s.Reaches x := by
  obtain ⟨rank, subrank, parentrank⟩ := selected.2.2.2.2
  have go : ∀ k, ∀ d, rank d = k → ∀ y, y ∈ s.head d → s.Reaches y := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro d hd y hy
      cases hab : m.explicitAbstract d with
      | true =>
        obtain ⟨c,hc,hcy⟩ := (h.2.2.2.1 d hab).1 y hy
        exact ih (rank c) (hd ▸ subrank d c hab hc) c rfl y hcy
      | false =>
        by_cases hr : d = m.family.root
        · subst d
          have he := (h.2.1.1 y).mp hy
          subst y
          exact .refl
        · cases hp : m.family.parent d with
          | none =>
            have he := selected.2.1 d hp (wf.1.parentless_abstract d hp hr)
            simp [hab] at he
          | some p =>
            obtain ⟨z,hz,_⟩ := h.2.2.1.2.1 d p hp y hy
            obtain ⟨_,c,hc,hcz⟩ := h.1.1 d z y hz
            have he : c = p := Option.some.inj (hc.symm.trans hp)
            exact (ih (rank p) (hd ▸ parentrank d p hab hp) p rfl z (he ▸ hcz)).tail ⟨d,hz⟩
  rcases h.2.1.2.2 x with he | ⟨d,_,hx⟩
  · subst x; exact .refl
  · exact go (rank d) d rfl x hx

end Clafer.Semantics.Realization
