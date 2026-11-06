module

public import Clafer.Verification.Import

/-!
# Effective import representation and semantic preservation

The relation is fieldwise over compiler UIDs, bounds and modes. Its uniqueness
is proved independently of satisfaction, and then composed with #50's checker
and interpreted structural semantics. The external JSON/capture boundary remains
unproved; see docs/resolved-import.md.
-/

@[expose] public section
namespace Clafer.Verification.Import
open Semantics MCS DPGraph.Predicates

private theorem rangeData_injective : Function.Injective rangeData := by
  intro a b h
  rcases a with ⟨al, au⟩
  rcases b with ⟨bl, bu⟩
  cases au <;> cases bu <;> simp_all [rangeData]
  all_goals omega

private theorem option_uid_injective {r : Input} (h : Function.Injective r.uid)
    {a b : Option r.Index} (he : a.map r.uid = b.map r.uid) : a = b := by
  cases a <;> cases b <;> simp_all
  apply h
  assumption

private theorem reference_injective {r : Input} (h : Function.Injective r.uid)
    {a b : ReferenceTo r.Index}
    (mode : modeName a = modeName b)
    (target : a.target.map r.uid = b.target.map r.uid) : a = b := by
  cases a <;> cases b <;> simp_all [modeName, ReferenceTo.target]
  all_goals apply h; assumption

/-- A fieldwise representation determines the semantic core uniquely. This
uses injectivity of original UIDs, not any injectivity property of names. -/
theorem representation_unique {r : Input} (unique : Function.Injective r.uid)
    {m n : EffectiveCore r.rows.length} (hm : Represents r m) (hn : Represents r n) : m = n := by
  have hi : m.id = n.id := funext fun i => (hm.ids i).trans (hn.ids i).symm
  have hg : m.group = n.group := funext fun i => rangeData_injective ((hm.group i).trans (hn.group i).symm)
  have hp : m.family.parent = n.family.parent := funext fun i =>
    option_uid_injective unique ((hm.parent i).trans (hn.parent i).symm)
  have hs : m.family.super = n.family.super := funext fun i =>
    option_uid_injective unique ((hm.super i).trans (hn.super i).symm)
  have hr : m.family.reference = n.family.reference := funext fun i =>
    reference_injective unique ((hm.mode i).trans (hn.mode i).symm)
      ((hm.target i).trans (hn.target i).symm)
  have ho : m.family.origin = n.family.origin := funext fun i => (hm.origin i).trans (hn.origin i).symm
  have ha : m.family.isAbstract = n.family.isAbstract := funext fun i => (hm.abstract i).trans (hn.abstract i).symm
  have hname : m.family.name = n.family.name := funext fun i => (hm.name i).trans (hn.name i).symm
  have hc : m.family.multiplicity = n.family.multiplicity := funext fun i =>
    rangeData_injective ((hm.card i).trans (hn.card i).symm)
  have hfg : m.family.group = n.family.group := by
    funext i
    rw [hm.familyGroup, hn.familyGroup, hg]
  have hroot : m.family.root = n.family.root := hm.root.trans hn.root.symm
  cases m with | mk mf mi mg =>
    cases n with | mk nf ni ng =>
      cases mf
      cases nf
      simp_all

/-- Every field-correct interpretation has exactly the normalized structural
meaning, for arbitrary configurations (including violating configurations). -/
theorem normalization_correspondence {r : Input} (a : Accepted r)
    (m : EffectiveCore r.rows.length) (hm : Represents r m)
    {U : Type} (s : Configuration r.Index U) :
    StructuralSatisfies r.normalize s ↔ StructuralSatisfies m s := by
  rw [representation_unique a.bindings.1 a.represents hm]

-- [proof->req~clafer-resolved-import~1]
/-- Admission derives both semantic preconditions; the caller supplies neither
well-formedness nor a desired semantic equivalence. -/
theorem imported_check_correct {r : Input} (a : Accepted r)
    (m : EffectiveCore r.rows.length) (hm : Represents r m) (c : Candidate r.rows.length) :
    check r.normalize c = true ↔ StructuralSatisfies m (realize c) := by
  exact (check_correct _ c a.wellFormed a.supported).trans
    (normalization_correspondence a m hm _)

theorem imported_verify_correct {r : Input} (a : Accepted r)
    (m : EffectiveCore r.rows.length) (hm : Represents r m) (c : RawCandidate)
    (tables : TablesValid r.normalize c)
    (typed : (realize (c.decode r.normalize tables.root)).Typed r.normalize) :
    verify r.normalize c = .satisfies ↔
      StructuralSatisfies m (realize (c.decode r.normalize tables.root)) := by
  exact (verify_correct _ a.wellFormed a.supported tables typed).trans
    (normalization_correspondence a m hm _)

/-- Reference heads remain separate even when their dereferenced targets agree:
UID indexing does not change object labels or reference-table tuples. -/
theorem imported_reference_occurrences {r : Input} (a : Accepted r)
    (c : RawCandidate) (tables : TablesValid r.normalize c)
    (d e : r.Index) (x y t u : Fin c.objects.length)
    (h : (r.normalize.id d, c.objects[x], c.objects[t]) =
         (r.normalize.id e, c.objects[y], c.objects[u])) :
    d = e ∧ x = y ∧ t = u := tuple_identity _ a.wellFormed tables d e x t y u h


/-- The finite index returned by UID lookup denotes that exact compiler UID. -/
theorem lookup_sound (r : Input) {uid : String} {i : r.Index}
    (h : r.lookup uid = some i) : r.uid i = uid := by
  simpa only [beq_iff_eq] using List.find?_some h

def ClassRepresents (r : Input) (uid : String) (id : DeclId) : Prop :=
  ∃ i : r.Index, id = ⟨i.val⟩ ∧ r.uid i = uid

theorem classId_represents (r : Input) {uid : String} {id : DeclId}
    (h : r.classId uid = .ok id) : ClassRepresents r uid id := by
  unfold Input.classId at h
  cases hl : r.lookup uid with
  | none => simp [hl] at h
  | some i =>
    simp only [hl, Except.ok.injEq] at h
    exact ⟨i, h.symm, lookup_sound r hl⟩

private theorem mapM_represents {α β : Type} {f : α → Except String β}
    {R : α → β → Prop} (hf : ∀ x y, f x = .ok y → R x y)
    {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys) : List.Forall₂ R xs ys := by
  induction xs generalizing ys with
  | nil =>
    have he : [] = ys := Except.ok.inj h
    subst ys
    exact .nil
  | cons x xs ih =>
    cases hx : f x with
    | error e => simp [List.mapM_cons, hx, Bind.bind, Except.bind] at h
    | ok y =>
      cases ht : xs.mapM f with
      | error e => simp [List.mapM_cons, hx, ht, Bind.bind, Except.bind] at h
      | ok tail =>
        simp [List.mapM_cons, hx, ht, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
        subst ys
        exact .cons (hf x y hx) (ih ht)

structure CandidateRepresents (r : Input) (source : UidCandidate) (target : RawCandidate) : Prop where
  objects : target.objects = source.objects
  root : target.root = source.root
  members : List.Forall₂ (fun a b => ClassRepresents r a.1 b.1 ∧ a.2 = b.2)
    source.members target.members
  containment : List.Forall₂ (fun a b => ClassRepresents r a.1 b.1 ∧ a.2 = b.2)
    source.containment target.containment
  references : List.Forall₂ (fun a b => ClassRepresents r a.1 b.1 ∧ a.2 = b.2)
    source.references target.references

private theorem member_represents (r : Input) (a : String × Nat) (b : DeclId × Nat)
    (h : r.member a = .ok b) : ClassRepresents r a.1 b.1 ∧ a.2 = b.2 := by
  unfold Input.member at h
  cases hc : r.classId a.1 with
  | error e => simp [hc, Bind.bind, Except.bind] at h
  | ok id =>
    simp [hc, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
    subst b
    exact ⟨classId_represents r hc, rfl⟩

private theorem link_represents (r : Input) (a : String × Nat × Nat) (b : DeclId × Nat × Nat)
    (h : r.link a = .ok b) : ClassRepresents r a.1 b.1 ∧ a.2 = b.2 := by
  unfold Input.link at h
  cases hc : r.classId a.1 with
  | error e => simp [hc, Bind.bind, Except.bind] at h
  | ok id =>
    simp [hc, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
    subst b
    exact ⟨classId_represents r hc, rfl⟩

/-- Every successful UID candidate translation preserves all rows in order,
including repeated-target reference occurrences, endpoints and object labels. -/
theorem translate_represents (r : Input) (c : UidCandidate) (raw : RawCandidate)
    (h : c.translate r = .ok raw) : CandidateRepresents r c raw := by
  unfold UidCandidate.translate at h
  cases hm : c.members.mapM r.member with
  | error e => simp [hm, Bind.bind, Except.bind] at h
  | ok ms =>
    cases hp : c.containment.mapM r.link with
    | error e => simp [hm, hp, Bind.bind, Except.bind] at h
    | ok ps =>
      cases hr : c.references.mapM r.link with
      | error e => simp [hm, hp, hr, Bind.bind, Except.bind] at h
      | ok rs =>
        simp [hm, hp, hr, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
        subst raw
        exact ⟨rfl, rfl, mapM_represents (member_represents r) hm,
          mapM_represents (link_represents r) hp, mapM_represents (link_represents r) hr⟩

end Clafer.Verification.Import
