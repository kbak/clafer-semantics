module

public import DPGraph.Predicates.FunctionalKey

/-!
# Functional-key boundaries and repeated marriages

Finite witness motivated by Diskin et al. (2000), §3.3 pp. 353–354 / Figure 1
and §3.5 p. 356, using the unchanged SoSyM Table 3 / Figure 21c bag-sensitive
key. This checks two marriages of the same spouses on different dates; it
does not assert an unrestricted real-world marriage identity rule.
-/

@[expose] public section

universe u v w

namespace DPGraph.Predicates.Examples

theorem function_empty_source {n : Nat} {B : Fin n → Type v}
    (f : ∀ i, Empty → B i) : Key (fun i => Span.ofFunction (f i)) :=
  (key_ofFunction_iff f).mpr (fun a => Empty.elim a)

theorem function_subsingleton_source {A : Type u} [Subsingleton A]
    {n : Nat} {B : Fin n → Type v} (f : ∀ i, A → B i) :
    Key (fun i => Span.ofFunction (f i)) :=
  (key_ofFunction_iff f).mpr (fun _ _ _ => Subsingleton.elim _ _)

theorem empty_tuple_unit :
    Function.Injective (fun (_ : Unit) (i : Fin 0) => (Fin.elim0 i : Empty)) :=
  (tuple_injective_zero_iff _).mpr inferInstance

theorem empty_tuple_bool_fails :
    ¬ Function.Injective (fun (_ : Bool) (i : Fin 0) => (Fin.elim0 i : Empty)) := by
  intro h
  exact Bool.false_ne_true (@Subsingleton.elim _ ((tuple_injective_zero_iff _).mp h)
    false true)

/-- Exercise the span criterion with a head lifted independently of both endpoints. -/
def liftedFunction {A : Type u} {B : Type v} (f : A → B) :
    Span.{u,v,max u w} A B where
  Link := ULift.{w} A
  source := ULift.down
  target l := f l.down

theorem liftedFunction_total {A : Type u} {B : Type v} (f : A → B) :
    Total (liftedFunction.{u,v,w} f) := fun a => ⟨⟨a⟩, rfl⟩

theorem liftedFunction_singleValued {A : Type u} {B : Type v} (f : A → B) :
    SingleValued (liftedFunction.{u,v,w} f) := fun _ _ h => ULift.ext h

theorem liftedFunction_key_iff {A : Type u} {n : Nat} {B : Fin n → Type v}
    (f : ∀ i, A → B i) : Key (fun i => liftedFunction.{u,v,w} (f i)) ↔
      Function.Injective (fun a i => f i a) := by
  rw [key_total_singleValued_iff _
    (fun i => liftedFunction_total (f i)) (fun i => liftedFunction_singleValued (f i))]
  have values : (fun a i => targetValue (liftedFunction.{u,v,w} (f i))
      (liftedFunction_total (f i)) (liftedFunction_singleValued (f i)) a) =
      (fun a i => f i a) := by
    funext a i
    exact targetValue_eq_of_source (liftedFunction.{u,v,w} (f i)) _ _ (ULift.up a) rfl
  rw [values]

namespace Remarriage

inductive Marriage where
  | first | second
  deriving DecidableEq

inductive Person where
  | wife | husband
  deriving DecidableEq

inductive Date where
  | earlier | later
  deriving DecidableEq

def wife : Marriage → Person := fun _ => .wife
def husband : Marriage → Person := fun _ => .husband
def date : Marriage → Date
  | .first => .earlier
  | .second => .later

theorem same_spouses_different_dates :
    wife .first = wife .second ∧ husband .first = husband .second ∧
      date .first ≠ date .second := ⟨rfl, rfl, by decide⟩

def spouseValue : Fin 2 → Marriage → Person := Fin.cases wife (fun _ => husband)
def spouses (i : Fin 2) : Span Marriage Person := Span.ofFunction (spouseValue i)

def TripleTarget : Fin 3 → Type := Fin.cases Person (Fin.cases Person (fun _ => Date))
def tripleValue : (i : Fin 3) → Marriage → TripleTarget i :=
  Fin.cases wife (Fin.cases husband (fun _ => date))
-- [impl->req~predicate-key-functional~1]
def spouseDate (i : Fin 3) : Span Marriage (TripleTarget i) :=
  Span.ofFunction (tripleValue i)

theorem spouses_total (i : Fin 2) : Total (spouses i) := ofFunction_total _
theorem spouses_singleValued (i : Fin 2) : SingleValued (spouses i) :=
  ofFunction_singleValued _
theorem spouseDate_total (i : Fin 3) : Total (spouseDate i) := ofFunction_total _
theorem spouseDate_singleValued (i : Fin 3) : SingleValued (spouseDate i) :=
  ofFunction_singleValued _

theorem spouses_not_key : ¬ Key spouses := by
  intro h
  have equal : Marriage.first = Marriage.second := (key_ofFunction_iff spouseValue).mp h
    (funext (fun i => Fin.cases rfl (fun _ => rfl) i))
  cases equal

theorem date_injective : Function.Injective date := by
  intro a b h
  cases a <;> cases b <;> simp_all [date]

-- [proof->req~predicate-key-functional~1]
theorem spouseDate_key : Key spouseDate := by
  apply (key_ofFunction_iff tripleValue).mpr
  intro a b h
  exact date_injective (congrFun h 2)

end Remarriage
end DPGraph.Predicates.Examples
