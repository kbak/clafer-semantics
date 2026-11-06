module

public import Clafer.Behavioral.InheritedReference

/-! S9/T8: nearest ownership, current targets and shared inherited occurrences.
These are observation fixtures, not complete richer-model admission witnesses. -/

@[expose] public section
namespace Clafer.Behavioral.InheritedReferenceExamples
open Semantics MCS InheritedReference

def family : Family (Fin 5) where
  root := 0
  parent d := if d = 0 ∨ d = 1 then none else some 0
  reference d := if d = 1 then .bag 3 else if d = 4 then .set 3 else .basic
  super d := if d = 2 then some 1 else if d = 4 then some 2 else none
  origin d := if d = 0 then .syntheticRoot else .user
  isAbstract d := d == 1
  name _ := ""
  multiplicity _ := unrestricted

theorem inherited_owner : Owner family 2 1 :=
  .inherited (by simp [family]) (by simp [family]) (.declared (by simp [family]))

-- [utest->req~behavioral-inherited-reference-observation~1]
theorem owner_unique (o : Fin 5) (h : Owner family 2 o) : o = 1 :=
  h.unique inherited_owner

theorem owner_is_not_target : ¬ Owner family 2 3 := by
  intro h
  have bad := h.unique inherited_owner
  contradiction

theorem nearer_declaration_wins : Owner family 4 4 ∧ ¬ Owner family 4 1 := by
  have own : Owner family 4 4 := .declared (by simp [family])
  exact ⟨own, fun h => by have bad := h.unique own; contradiction⟩

/-- At times 0/1 both bag heads survive and share the current target; at time
2 the heads disappear. No subtype dereference relation is separately allocated. -/
def state (t : Nat) : Configuration (Fin 5) (Fin 5) where
  root := 0
  head d := if d = 1 ∨ d = 2 then {x | t < 2 ∧ (x = 1 ∨ x = 2)}
    else if d = 3 then {3, 4} else {0}
  contains d p x := p = 0 ∧ d = 2 ∧ t < 2 ∧ (x = 1 ∨ x = 2)
  deref d x y := d = 1 ∧ t < 2 ∧ (x = 1 ∨ x = 2) ∧ y = if t = 0 then 3 else 4

theorem two_heads_one_target :
    deref family (state 0) 2 1 3 ∧ deref family (state 0) 2 2 3 ∧
    (1 : Fin 5) ≠ 2 := by
  simp only [deref_owner inherited_owner]
  simp [state]

theorem current_target :
    deref family (state 1) 2 1 4 ∧ ¬ deref family (state 1) 2 1 3 := by
  simp only [deref_owner inherited_owner]
  simp [state]

theorem disappears (x y : Fin 5) : ¬ deref family (state 2) 2 x y := by
  rw [deref_owner inherited_owner]
  simp [state]

theorem owner_view_agreement {t : Nat} {x : Fin 5}
    (hx : t < 2 ∧ (x = 1 ∨ x = 2)) (y : Fin 5) :
    deref family (state t) 2 x y ↔ deref family (state t) 1 x y := by
  exact shared_head inherited_owner (.declared (by simp [family]))
    (by simpa [state] using hx) (by simpa [state] using hx) y

end Clafer.Behavioral.InheritedReferenceExamples
