module

public import Clafer.Examples.Telematics.Expressions
public import Clafer.Constraints.DenotationInvariance

-- [impl->req~clafer-appendix-f-expressions~1]

/-!
# Expression environments on the inherited structural fixture

SoSyM Appendix 6 (PDF p.34).

The nonprimitive objects and links are the shared identities of #66's
structural projection. Its finite primitive placeholder is replaced by the
complete mathematical integer domain for constraint interpretation. This is
an expression environment, not a new whole-model Compile correspondence (#69).
-/

@[expose] public section
namespace Clafer.Examples.Telematics.ExpressionEnvironment
open Clafer.Constraints Telematics.Expressions CategoryTheory DPGraph.Predicates

abbrev U := Sum (Fin 25) Int
abbrev atom (n : Fin 25) : U := Sum.inl n

def integers : IntegerRealization U where
  encode := ⟨Sum.inr,Sum.inr_injective⟩
  decode | .inl _ => 99 | .inr i => i
  decode_encode _ := rfl

/-- Source declaration IDs → the delivered structural fixture's preorder. -/
def position : Fin 28 → Fin 28 :=
  ![0,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,1,2,3,4,5,6,7,8,9,10,11,12]

theorem position_id (d : Fin 28) :
    Telematics.Structural.core.id (position d) = ⟨d.val⟩ := by
  fin_cases d <;> rfl

def objects (d : Fin 28) : Set U :=
  if d = 27 then integers.domain else Sum.inl '' Telematics.Structural.config.head (position d)

/-- Integer operands may vary without changing the finite nonprimitive carrier.
Version heads 8/9 belong to displays and 6/7 belong to ECUs. -/
def links (ecuVersion displayVersion : Int) (i : Fin 34) (x y : U) : Prop :=
  match (maps i).kind with
  | .inclusion => x = y
  | .head => ∃ a b, x = atom a ∧ y = atom b ∧
      Telematics.Structural.config.contains (position ⟨(maps i).owner.value, by
        fin_cases i <;> decide⟩) a b
  | .parent => ∃ a b, x = atom a ∧ y = atom b ∧
      Telematics.Structural.config.contains (position ⟨(maps i).owner.value, by
        fin_cases i <;> decide⟩) b a
  | .dereference =>
      if (maps i).owner = ⟨9⟩ then
        ∃ a, x = atom a ∧ y = integers.encode
          (if a = 8 ∨ a = 9 then displayVersion else ecuVersion)
      else if (maps i).owner = ⟨6⟩ then False
      else ∃ a b, x = atom a ∧ y = atom b ∧
        Telematics.Structural.config.deref (position ⟨(maps i).owner.value, by
          fin_cases i <;> decide⟩) a b
  | .target => False

def span (e d : Int) (i : Fin 34) : DPGraph.Span
    (objects (maps i).source) (objects (maps i).target) :=
  .ofRelation (fun a b => links e d i a.val b.val)

def graphMap (c : Fin 28) (e d : Int) : (support c).graph ⥤q semanticGraph U where
  obj := objects
  map := by
    rintro x y ⟨i,hs,ht⟩
    subst x; subst y
    exact span e d i

theorem inclusion_subset (i : Fin 34) (h : (maps i).kind = .inclusion) :
    objects (maps i).source ⊆ objects (maps i).target := by
  fin_cases i <;> try { cases h }
  all_goals simp [objects,maps,position,Telematics.Structural.config,Telematics.Structural.heads,
    Set.subset_def]

def model (c : Fin 28) (e d : Int) : IntegerBinding (support c) U where
  realization := integers
  model := graphMap c e d
  same_id := by
    intro x y h
    have he : x = y := Fin.ext (congrArg DeclId.value h)
    subst y; rfl
  inclusion := by
    intro i hi
    change Inclusion (span e d i)
    unfold span
    have he : (fun (a : objects (maps i).source) (b : objects (maps i).target) =>
        links e d i a.val b.val) = (fun a b => a.val = b.val) := by
      funext a b
      simp [links, show (maps i).kind = .inclusion from hi]
    rw [he]
    exact (Semantics.identity_inclusion_iff _ _).mpr (inclusion_subset i hi)
  integer_domain := by
    intro x hx
    have he : x = 27 := by simpa [support] using hx
    subst x; change objects 27 = integers.domain; simp [objects]

@[simp] theorem model_objects (c : Fin 28) (e d : Int) (x : Fin 28) :
    (model c e d).model.obj x = objects x := rfl

/-- Every nonprimitive object extent comes from the delivered inherited model. -/
theorem shared_extent (c : Fin 28) (e d : Int) (x : Fin 28) (hx : x ≠ 27) :
    (model c e d).model.obj x = Sum.inl '' Telematics.Structural.config.head (position x) := by
  simp [model,graphMap,objects,hx]

theorem reduced_map (c : Fin 28) (e d : Int) (i : Fin 34) :
    ambientRelation ((model c e d).model.map ((support c).arrow i)) =
      {p | p.1 ∈ objects (maps i).source ∧ p.2 ∈ objects (maps i).target ∧
        links e d i p.1 p.2} := by
  ext p
  constructor
  · rintro ⟨⟨⟨a,b⟩,h⟩,hs,ht⟩
    exact ⟨hs ▸ a.property,ht ▸ b.property,hs ▸ ht ▸ h⟩
  · rintro ⟨ha,hb,h⟩
    exact ⟨⟨(⟨p.1,ha⟩,⟨p.2,hb⟩),h⟩,rfl,rfl⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem map_identity_unique : ∀ i j : Fin 34,
    (maps i).owner = (maps j).owner → (maps i).kind = (maps j).kind → i = j := by
  decide

theorem model_coherent (c : Fin 28) (e d : Int) : (model c e d).Coherent := by
  intro i j ho hk
  have he := map_identity_unique i j ho hk
  subst j
  exact ⟨⟨Equiv.refl _,fun _ => rfl,fun _ => rfl⟩⟩

theorem objects_finite (x : Fin 28) (hx : x ≠ 27) : (objects x).Finite := by
  unfold objects
  rw [ite_eq_right hx]
  exact (Set.toFinite _).image Sum.inl

theorem closed_admissible (c : Fin 28) (e d : Int) (x : U) (hx : x ∈ objects c) :
    (Environment.closed x).Admissible (model c e d) :=
  ⟨hx,fun _ v => nomatch v⟩

/-- The five enclosing classes used by c01–c12 have admissible sample contexts;
all nonprimitive extents remain finite independently of integer values. -/
theorem example_contexts (e d : Int) (i : Fin 5) :
    (Environment.closed ((![atom 12,atom 4,atom 4,atom 19,atom 0] : Fin 5 → U) i)).Admissible
      (model ((![1,11,15,19,0] : Fin 5 → Fin 28) i) e d) := by
  apply closed_admissible
  fin_cases i <;> simp [objects,position,Telematics.Structural.config,Telematics.Structural.heads]

end Clafer.Examples.Telematics.ExpressionEnvironment
