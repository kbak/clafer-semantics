module

public import Clafer.Constraints.IntegerNavigation

/-! # Integer extraction and Appendix 6 navigation witnesses

SoSyM Appendix 6 PDF p.34; these realize the selected navigation fragment, not all
constraints of the telematics product line. Five structural objects coexist with
all Int values. Versions and arithmetic are never restricted to a finite range.
-/

@[expose] public section
namespace Clafer.Constraints.IntegerExamples
open CategoryTheory DPGraph.Predicates VersionNavigation

abbrev U := Sum (Fin 5) Int
def atom (n : Fin 5) : U := Sum.inl n

def integers : IntegerRealization U where
  encode := ⟨Sum.inr, Sum.inr_injective⟩
  /- The off-domain value is deliberately 99: extraction must never use it. -/
  decode | .inl _ => 99 | .inr n => n
  decode_encode _ := rfl

def objects : Fin 6 → Set U
  | 0 => {atom 1}
  | 1 => {atom 0}
  | 2 => {atom 0, atom 1}
  | 3 => {atom 2, atom 3}
  | 4 => {atom 4}
  | 5 => integers.domain

def display : objects 0 := ⟨atom 1, rfl⟩
def ecu : objects 1 := ⟨atom 0, rfl⟩
def displayComp : objects 2 := ⟨atom 1, Or.inr rfl⟩
def ecuComp : objects 2 := ⟨atom 0, Or.inl rfl⟩
def displayRef : objects 3 := ⟨atom 3, Or.inr rfl⟩
def ecuRef : objects 3 := ⟨atom 2, Or.inl rfl⟩
def serverRef : objects 4 := ⟨atom 4, rfl⟩

def toVersion (c : objects 2) : objects 3 :=
  if c.val = atom 1 then displayRef else ecuRef

def fromVersion (e d : Int) (v : objects 3) : objects 5 :=
  ⟨integers.encode (if v.val = atom 3 then d else e), ⟨_, rfl⟩⟩

def displayInc (x : objects 0) : objects 2 := ⟨x.val, Or.inr x.property⟩
def ecuInc (x : objects 1) : objects 2 := ⟨x.val, Or.inl x.property⟩

def maps (e d : Int) (i : support.Edge) : DPGraph.Span
    (objects (support.mapRef i).source) (objects (support.mapRef i).target) :=
  match i with
  | 0 => .ofFunction displayInc
  | 1 => .ofFunction ecuInc
  | 2 => .ofFunction toVersion
  | 3 => .ofFunction (fromVersion e d)
  | 4 => .ofFunction (fun _ => serverRef)
  | 5 => .ofFunction (fun _ => ecu)

def modelMap (e d : Int) : support.graph ⥤q semanticGraph.{0,0} U where
  obj := objects
  map {x y} a := by
    obtain ⟨i, hs, ht⟩ := a
    subst x; subst y
    exact maps e d i

def model (e d : Int) : Model.{0,0} U where
  realization := integers
  model := modelMap e d
  same_id := by
    intro x y h
    have he : x = y := by fin_cases x <;> fin_cases y <;> simp_all [support]
    subst y; rfl
  inclusion := by
    intro i hi
    fin_cases i
    · exact ⟨Function.bijective_id, fun _ => rfl⟩
    · exact ⟨Function.bijective_id, fun _ => rfl⟩
    all_goals cases hi
  integer_domain := by
    intro x hx
    fin_cases x <;> simp_all [support]
    rfl
  version_head := function_one toVersion
  version_dref := function_one (fromVersion e d)
  server_head := function_one (fun _ : objects 0 => serverRef)
  server_dref := function_one (fun _ : objects 4 => ecu)

theorem display_objects (e d : Int) :
    (model e d).versionObjects {display.val} = {integers.encode d} := by
  change navigationImage (.ofFunction (fromVersion e d))
    (navigationImage (.ofFunction toVersion) {displayComp.val}) = _
  rw [navigationImage_function, navigationImage_function]
  rfl

theorem server_objects (e d : Int) : (model e d).serverObjects display = {ecu.val} := by
  change navigationImage (.ofFunction (fun _ : objects 4 => ecu))
    (navigationImage (.ofFunction (fun _ : objects 0 => serverRef)) {display.val}) = _
  rw [navigationImage_function, navigationImage_function]

-- [proof->req~clafer-version-navigation~1]
theorem server_version_objects (e d : Int) :
    (model e d).versionObjects ((model e d).serverObjects display) = {integers.encode e} := by
  rw [server_objects]
  change navigationImage (.ofFunction (fromVersion e d))
    (navigationImage (.ofFunction toVersion) {ecuComp.val}) = _
  rw [navigationImage_function, navigationImage_function]
  rfl

-- [proof->req~clafer-representative-coverage~1]
/-- Actual head/dereference navigation followed by the integer comparison. -/
theorem comparison_value (e d : Int) :
    compareVersions integers ((model e d).versionObjects {display.val})
      ((model e d).versionObjects ((model e d).serverObjects display)) =
        some (decide (e ≤ d)) := by
  rw [display_objects, server_version_objects, compareVersions_encoded]

theorem greater :
    compareVersions integers ((model 2 3).versionObjects {display.val})
      ((model 2 3).versionObjects ((model 2 3).serverObjects display)) = some true :=
  comparison_value 2 3

theorem equal :
    compareVersions integers ((model 2 2).versionObjects {display.val})
      ((model 2 2).versionObjects ((model 2 2).serverObjects display)) = some true :=
  comparison_value 2 2

theorem lower :
    compareVersions integers ((model 3 2).versionObjects {display.val})
      ((model 3 2).versionObjects ((model 3 2).serverObjects display)) = some false :=
  comparison_value 3 2

theorem negative_unbounded (n : Int) : integers.extract {integers.encode (n - 1)} = some (n - 1) :=
  integers.extract_encoded _

-- [proof->req~clafer-integer-extraction~1]
theorem empty : integers.extract ∅ = none := integers.extract_empty

theorem empty_navigation (e d : Int) :
    integers.extract ((model e d).versionObjects ∅) = none := by
  change integers.extract (navigationImage (.ofFunction (fromVersion e d))
    (navigationImage (.ofFunction toVersion) ∅)) = none
  rw [navigationImage_empty, navigationImage_empty]
  exact integers.extract_empty

theorem multiple : integers.extract {integers.encode 2, integers.encode 3} = none :=
  integers.extract_multiple (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    (by decide)

theorem wrong_domain : integers.extract {atom 0} = none := by
  apply integers.extract_wrong_domain
  rintro ⟨n, hn⟩
  cases hn

/-- Neither missing servers nor wrong-domain objects pass the scalar comparison. -/
theorem empty_server : compareVersions integers {integers.encode 3} ∅ = none := by
  simp [compareVersions, integers.extract_encoded, integers.extract_empty]

theorem multiple_server :
    compareVersions integers {integers.encode 3} {integers.encode 2, integers.encode 3} = none := by
  simp [compareVersions, integers.extract_encoded, multiple]

theorem wrong_domain_server : compareVersions integers {integers.encode 3} {atom 0} = none := by
  simp [compareVersions, integers.extract_encoded, wrong_domain]

/-- Typing itself permits a collection expression; its runtime cardinality is
not determined by the result sort. The interpreter must use partial extraction. -/
def potentiallyEmpty : Expr support [] .integer :=
  .integerOf rfl (.setOp .difference
    (.image (.image (.widenObjects displayWiden .this) (.map 2)) (.map 3))
    (.image (.image (.widenObjects displayWiden .this) (.map 2)) (.map 3)))

theorem wrong_sort_rejected : True := by
  fail_if_success
    have _ : Expr support [] .integer := .integerOf rfl (.map 3)
  fail_if_success
    have _ : Expr support [] .integer := .integerOf rfl (.this)
  trivial

/-- A fabricated annotation cannot turn the version reference object into Int. -/
abbrev badSupport : Support := { support with integer := fun v => v == 3 }

theorem forged_primitive_rejected : ¬ badSupport.Resolved fragment := by
  intro h
  have bad := h.integers 3 rfl
  simp [fragment_entries, rootDecl, intDecl, compDecl,
    versionDecl, ecuDecl, displayDecl, serverDecl] at bad

end Clafer.Constraints.IntegerExamples
