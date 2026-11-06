module

public import Clafer.Compile.Groups
public import DPGraph.Predicates.Finite

/-! # Group generation correspondence and its finite specialization

The #50 configuration supplies head/containment relations. This module adds
inherited inventories without extending #50's guarded checker. No realization
of inherited fields or commuting restrictions is inferred from AST metadata.
-/

@[expose] public section
namespace Clafer.Compile.Groups
open CategoryTheory MCS DPGraph DPGraph.Predicates Semantics

variable {n : Nat} {U : Type} (m : EffectiveCore n) (s : Configuration (Fin n) U)

theorem head_relation (typed : s.Typed m) {p c : Fin n}
    (present : (m.family.shape c).hasParent = true) (x y : U)
    (e : m.family.canonicalRoles.Arrow p c)
    (he : e.val = .ordinary c ⟨.head, present⟩) :
    (∃ l : ((s.interpret m).map e).Link,
      (((s.interpret m).map e).source l).val = x ∧
      (((s.interpret m).map e).target l).val = y) ↔ s.contains c x y := by
  rcases e with ⟨e, hs, ht⟩
  change e = _ at he
  subst e
  cases hs
  change (∃ l : (s.headMap m c).Link,
    ((s.headMap m c).source l).val = x ∧
    ((s.headMap m c).target l).val = y) ↔ _
  constructor
  · rintro ⟨⟨⟨a, b⟩, h⟩, rfl, rfl⟩; exact h
  · intro h
    obtain ⟨hy, p, hp, hx⟩ := typed.1 c x y h
    exact ⟨⟨(⟨x, by simpa [hp] using hx⟩, ⟨y, hy⟩), h⟩, rfl, rfl⟩

/-- Proved representation bridge for every selected map, not a supplied
assumption of group satisfaction. Typedness controls relation endpoints only. -/
theorem objects_interpret (typed : s.Typed m) (p : Fin n) (x y : U) :
    Objects m.family ((binding m.family p).comp (s.interpret m)) x y ↔
      ChildObjects m.family s p x y := by
  constructor
  · rintro ⟨c, hl⟩
    exact ⟨c.1.val, c.1.property, c.2.val, c.2.property,
      (head_relation m s typed (by simp [Family.shape, c.2.property]) x y (headArrow m.family c) rfl).mp hl⟩
  · rintro ⟨a, ha, c, hc, h⟩
    let k : Child m.family p := ⟨⟨a, ha⟩, ⟨c, hc⟩⟩
    exact ⟨k, (head_relation m s typed (by simp [k, Family.shape, hc]) x y (headArrow m.family k) rfl).mpr h⟩

-- [proof->req~clafer-compile-groups~1]
theorem satisfies_iff (typed : s.Typed m) (p : Id m.family) :
    (interpretation m.family U).Satisfies (s.interpret m) (formula m.family p) ↔
      Holds m.family s p.val := by
  unfold Interpretation.Satisfies formula interpretation meaning Holds
  apply forall_congr'
  intro x
  apply inRange_iff
  exact Equiv.subtypeEquivRight (fun y => objects_interpret m s typed p.val x.val y)

/-- The selected cardinal semantics is reused from #50, including the empty
case. Finiteness is required of the counted set, not silently assumed. -/
theorem finite_bounds (p : Fin n)
    [∀ x : s.head p, Fintype {y : U // ChildObjects m.family s p x.val y}] :
    Holds m.family s p ↔ ∀ x : s.head p,
      CountInRange (m.family.group p).effective.range
        (Fintype.card {y : U // ChildObjects m.family s p x.val y}) := by
  exact forall_congr' (fun _ => inRange_card _ _)

/-- On #50's direct-only inventory, the two child-object sets coincide. -/
theorem direct_child_iff (p : Fin n)
    (noInherited : ∀ a, Ancestor m.family p a → a ≠ p → ∀ c, m.family.parent c ≠ some a)
    (x y : U) : ChildObjects m.family s p x y ↔ s.Child m p x y := by
  constructor
  · rintro ⟨a, ha, c, hc, h⟩
    have he : a = p := by
      by_contra hn
      exact noInherited a ha hn c hc
    exact ⟨c, he ▸ hc, h⟩
  · rintro ⟨c, hc, h⟩; exact ⟨p, .refl, c, hc, h⟩

/-- Empty inventories have zero children, even with a positive lower bound. -/
theorem empty_children (p : Fin n) (empty : IsEmpty (Child m.family p)) (x y : U) :
    ¬ ChildObjects m.family s p x y := by
  rintro ⟨a, ha, c, hc, _⟩
  exact empty.false ⟨⟨a, ha⟩, ⟨c, hc⟩⟩

theorem empty_holds_iff (p : Fin n) (empty : IsEmpty (Child m.family p)) :
    Holds m.family s p ↔
      ∀ _x : s.head p, CountInRange (m.family.group p).effective.range 0 := by
  unfold Holds
  apply forall_congr'
  intro x
  let e : {y : U // ChildObjects m.family s p x.val y} ≃ Fin 0 :=
    { toFun := fun y => (empty_children m s p empty _ _ y.property).elim
      invFun := Fin.elim0
      left_inv := fun y => (empty_children m s p empty _ _ y.property).elim
      right_inv := fun x => Fin.elim0 x }
  exact (inRange_iff _ e).trans (inRange_card _ _)

end Clafer.Compile.Groups

namespace Clafer.Compile
open CategoryTheory MCS DPGraph DPGraph.Predicates Semantics
variable {a : AST} (i : Input a) {U : Type}
variable (authored : Interpretation (Constraints.signature i.constraint) (semanticGraph U))

noncomputable def descendGroups (s : Configuration a.Occurrence U) :
    (gluedGroups i).carrier ⥤q semanticGraph U :=
  (groupUnlabel i).comp (s.interpret (EffectiveCore.erase i))

theorem descendGroups_reduct (s : Configuration a.Occurrence U) :
    (groupLabel i).comp (descendGroups i s) = s.interpret (EffectiveCore.erase i) := by
  erw [descendGroups, ← Prefunctor.comp_assoc, group_label_unlabel, Prefunctor.id_comp]

theorem generated_group_iff (s : Configuration a.Occurrence U)
    (typed : s.Typed (EffectiveCore.erase i)) (p : Groups.Id (family i)) :
    (groupInterpretation i U authored).Satisfies (s.interpret (EffectiveCore.erase i))
      (generatedGroup i p) ↔ Groups.Holds (family i) s p.val :=
  Groups.satisfies_iff (EffectiveCore.erase i) s typed p

/-- Every glued group is evaluated on the exact reduct. A realization equation
is required; this theorem does not invent #66's inherited model bridge. -/
theorem glued_group_iff (s : Configuration a.Occurrence U)
    (typed : s.Typed (EffectiveCore.erase i))
    (m : (gluedGroups i).carrier ⥤q semanticGraph U)
    (realizes : (groupLabel i).comp m = s.interpret (EffectiveCore.erase i))
    (p : Groups.Id (family i)) :
    (groupInterpretation i U authored).Satisfies m
      ((generatedGroup i p).translate (groupLabel i)) ↔ Groups.Holds (family i) s p.val := by
  erw [Interpretation.satisfies_translate, realizes]
  exact generated_group_iff i authored s typed p

theorem descended_group_iff (s : Configuration a.Occurrence U)
    (typed : s.Typed (EffectiveCore.erase i)) (p : Groups.Id (family i)) :
    (groupInterpretation i U authored).Satisfies (descendGroups i s)
      ((generatedGroup i p).translate (groupLabel i)) ↔ Groups.Holds (family i) s p.val :=
  glued_group_iff i authored s typed _ (descendGroups_reduct i s) p

-- [proof->req~clafer-gluing-declarations~1]
theorem descended_model_iff (s : Configuration a.Occurrence U)
    (typed : s.Typed (EffectiveCore.erase i)) :
    (groupInterpretation i U authored).IsModel (gluedGroups i).toDPGraph (descendGroups i s) ↔
      (∀ q, (groupInterpretation i U authored).Satisfies (s.interpret (EffectiveCore.erase i))
        (promote i (formula i q))) ∧
      (∀ p : Groups.Id (family i), Groups.Holds (family i) s p.val) := by
  erw [glued_model_iff, descendGroups_reduct]
  exact and_congr Iff.rfl (forall_congr' (generated_group_iff i authored s typed))

end Clafer.Compile
