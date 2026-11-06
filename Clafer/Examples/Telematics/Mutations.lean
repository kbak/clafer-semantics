module

public import Clafer.Examples.Telematics.ExpressionExamples

/-!
# Sensitive telematics constraint candidates

SoSyM Appendix 6 (PDF p.34).

Typed expression environments need not satisfy every structural or authored
constraint. This candidate moves both existing displays to ECU1, preserving
head/parent inversion and their object identities. It deliberately violates
ECU2's display bound and the moved display's server=parent constraint. It is
used to test truth and falsity of the actual expression combinations, not as
a claimed whole-model realization.
-/

@[expose] public section
namespace Clafer.Examples.Telematics.Mutations
open Clafer.Constraints Telematics.Expressions Telematics.ExpressionEnvironment CategoryTheory DPGraph.Predicates

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def movedLinks (i : Fin 34) (x y : U) : Prop :=
  if i = 9 then x = atom 2 ∧ (y = atom 4 ∨ y = atom 5)
  else if i = 33 then y = atom 2 ∧ (x = atom 4 ∨ x = atom 5)
  else links 2 3 i x y

def movedSpan (i : Fin 34) : DPGraph.Span (objects (maps i).source) (objects (maps i).target) :=
  .ofRelation (fun a b => movedLinks i a.val b.val)

def movedGraph (c : Fin 28) : (support c).graph ⥤q semanticGraph U where
  obj := objects
  map := by
    rintro x y ⟨i,hs,ht⟩
    subst x; subst y
    exact movedSpan i

def movedModel (c : Fin 28) : IntegerBinding (support c) U where
  realization := integers
  model := movedGraph c
  same_id := by
    intro x y h
    have he : x = y := Fin.ext (congrArg DeclId.value h)
    subst y; rfl
  inclusion := by
    intro i hi
    have h9 : i ≠ 9 := by intro he; subst i; cases hi
    have h33 : i ≠ 33 := by intro he; subst i; cases hi
    have he : (fun (a : objects (maps i).source) (b : objects (maps i).target) =>
        movedLinks i a.val b.val) = (fun a b => a.val = b.val) := by
      funext a b
      simp [movedLinks,h9,h33,links,show (maps i).kind = .inclusion from hi]
    change Inclusion (DPGraph.Span.ofRelation _)
    rw [he]
    exact (Semantics.identity_inclusion_iff _ _).mpr (inclusion_subset i hi)
  integer_domain := by
    intro x hx
    have he : x = 27 := by simpa [support] using hx
    subst x
    change objects 27 = integers.domain
    simp [objects]

theorem moved_coherent (c : Fin 28) : (movedModel c).Coherent := by
  intro i j ho hk
  have he := map_identity_unique i j ho hk
  subst j
  exact ⟨⟨Equiv.refl _,fun _ => rfl,fun _ => rfl⟩⟩

theorem moved_image (c : Fin 28) (i : Fin 34) (S : Set U) :
    relationalImage S (ambientRelation ((movedModel c).model.map ((support c).arrow i))) =
      {y | ∃ x, x ∈ S ∧ x ∈ objects (maps i).source ∧
        y ∈ objects (maps i).target ∧ movedLinks i x y} := by
  have hr : ambientRelation ((movedModel c).model.map ((support c).arrow i)) =
      {p | p.1 ∈ objects (maps i).source ∧ p.2 ∈ objects (maps i).target ∧
        movedLinks i p.1 p.2} := by
    ext p
    constructor
    · rintro ⟨⟨⟨a,b⟩,h⟩,hs,ht⟩
      exact ⟨hs ▸ a.property,ht ▸ b.property,hs ▸ ht ▸ h⟩
    · rintro ⟨ha,hb,h⟩
      exact ⟨⟨(⟨p.1,ha⟩,⟨p.2,hb⟩),h⟩,rfl,rfl⟩
  rw [hr]
  rfl

theorem two_displays :
    displays1.denote (movedModel 19) (.closed (atom 19)) = some {atom 4,atom 5} := by
  simp only [displays1,head15,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  rw [moved_image]
  change some {y | ∃ x, x ∈ objects 16 ∧ _} = _
  simp [movedLinks,maps,objects,position,Telematics.Structural.config,Telematics.Structural.heads,Set.ext_iff]

theorem extra_present :
    (head23 (Expr.this : Expr (support 19) [] _)).denote
      (movedModel 19) (.closed (atom 19)) = some {atom 22} := by
  simp only [head23,Expr.denote,lift₂,Option.bind_some,Option.map_some]
  rw [moved_image]
  simp [movedLinks,links,maps,objects,position,Telematics.Structural.config,Telematics.Structural.heads,
    Telematics.Structural.ownership,Environment.closed]

-- [proof->req~clafer-constraint-semantic-laws~1]
theorem c06_accepts_two : c06.Holds (movedModel 19) (.closed (atom 19)) := by
  have he := denotes_some _ _ _ _ extra_present (Set.finite_singleton _)
  have hc : (exactlyTwo displays1).denote (movedModel 19) (.closed (atom 19)) = some ⟨True⟩ := by
    simp [exactlyTwo,Expr.denote,two_displays,lift₂,finiteCard,atom]
  have h := denotes_iff _ _ _ _ _ _ he hc
  simpa [Expr.Holds,c06] using h

-- [proof->req~clafer-appendix-f-expressions~1]
/-- A false equality is detected on the actual server=parent expansion. -/
theorem c04_rejects_wrong_owner : ¬ c04.Holds (movedModel 15) (.closed (atom 5)) := by
  simp only [c04,parent15,dereference12,head12,Expr.Holds,Expr.denote,lift₂,
    Option.bind_some,Option.map_some]
  rw [moved_image,moved_image,moved_image]
  simp [movedLinks,links,maps,objects,position,Telematics.Structural.config,Telematics.Structural.heads,
    Telematics.Structural.ownership,Telematics.Structural.targets,Environment.closed,Set.ext_iff,atom]

end Clafer.Examples.Telematics.Mutations
