module

public import FormalCD.Metamodel.Examples

/-!
[impl->req~formalcd-metamodel-examples~1]
[proof->req~formalcd-formula-identity~1]
[proof->req~formalcd-metamodel-disciplines~1]
[proof->req~formalcd-metamodel-examples~1]
-/

/-!
# Finite discipline interpretations

The repeated-argument fragment is an actual model of ad, literal key and total
args under the extended interpretation. It has one formula and two argument
occurrences, so args is not set-valued. This is not a whole Figure 21c instance
or a self-description theorem. The naming witnesses separately exercise nd.
-/

@[expose] public section

namespace FormalCD.Metamodel.Examples
open CategoryTheory DPGraph DPGraph.Predicates

def one (s : String) : Set String := {s}
def point (s : String) : one s := ⟨s, rfl⟩

instance (s : String) : Subsingleton (one s) := by
  constructor
  rintro ⟨a,ha⟩ ⟨b,hb⟩
  exact Subtype.ext (ha.trans hb.symm)

def constant (I : Type) (a b : String) : Span (one a) (one b) :=
  ⟨I, fun _ => point a, fun _ => point b⟩

def constantFiber (I : Type) (a b : String) (f : one a) :
    (constant I a b).toFamily.Index f ≃ I where
  toFun l := l.val
  invFun i := ⟨i, Subsingleton.elim _ _⟩
  left_inv _ := rfl
  right_inv _ := rfl

inductive SingleVertex where | v
instance : Quiver SingleVertex := ⟨fun _ _ => Unit⟩
def singleGraph : Quiv := Quiv.of SingleVertex

def repeatSignature : Signature where
  Symbol := Unit
  arity _ := loops

def repeatFormula : Formula repeatSignature singleGraph :=
  ⟨(), {obj := fun _ => .v, map := fun _ => ()}⟩

def loopEdges : ArrowData loops ≃ Bool where
  toFun e := e.2.2
  invFun b := ⟨.point,.point,b⟩
  left_inv := by rintro ⟨a,b,e⟩; cases a; cases b; rfl
  right_inv _ := rfl

def repeatDiagram : arityShape ⥤q semanticGraph String where
  obj | .formula => one "#F" | .signature => one "#P"
      | .map => one "#M" | .class => one "#C"
  map | .args => constant Bool "#F" "#M"
      | .pred => constant Unit "#F" "#P"
      | .so | .ta => constant Unit "#M" "#C"

def repeatArityContext : ArityContext repeatSignature singleGraph String where
  symbol := ⟨fun _ => "#P", by intro a b _; cases a; cases b; rfl⟩
  vertex := ⟨fun _ => "#C", by intro a b _; cases a; cases b; rfl⟩
  arrow := ⟨fun _ => "#M", by
    rintro ⟨a,b,e⟩ ⟨c,d,f⟩ _; cases a; cases b; cases c; cases d; cases e; cases f; rfl⟩

def repeatDescriptor : ArityDescriptor (σ := repeatSignature) (G := singleGraph) repeatDiagram where
  candidate _ := some (Candidate.ofFormula repeatFormula)
  index _ _ l := some ⟨.point,.point,l.val⟩

def repeatIndex (f : (objects repeatDiagram .formula)) :
    (repeatDiagram.map ArityEdge.args).toFamily.Index f ≃ ArrowData loops :=
  (constantFiber Bool "#F" "#M" f).trans loopEdges.symm

theorem repeat_discipline : ArityDiscipline repeatArityContext repeatDiagram repeatDescriptor where
  classes := by
    ext x; constructor
    · intro h; exact ⟨SingleVertex.v, h.symm⟩
    · rintro ⟨_,rfl⟩; rfl
  maps := by
    ext x; constructor
    · intro h; exact ⟨⟨SingleVertex.v,SingleVertex.v,()⟩, h.symm⟩
    · rintro ⟨_,rfl⟩; rfl
  symbols := by
    ext x; constructor
    · intro h; exact ⟨(),h.symm⟩
    · rintro ⟨_,rfl⟩; rfl
  sources _ _ _ := rfl
  targets _ _ _ := rfl
  formulas f := ⟨Candidate.ofFormula repeatFormula, rfl, Candidate.ofFormula_valid _,
    ⟨repeatIndex f, fun _ => rfl, fun _ => rfl⟩,
    ⟨⟨(),Subsingleton.elim (α := one "#F") _ _⟩⟩, fun _ => rfl⟩

/-- Reusing one occurrence index loses a slot, even though endpoints are valid. -/
def duplicateIndex : ArityDescriptor (σ := repeatSignature) (G := singleGraph) repeatDiagram :=
  { repeatDescriptor with index := fun _ _ _ => some ⟨.point,.point,false⟩ }

theorem duplicate_index_rejected : ¬ duplicateIndex.ValidAt repeatArityContext (point "#F") := by
  rintro ⟨c, hc, _, ⟨e, he, _⟩, _⟩
  have hc' : Candidate.ofFormula repeatFormula = c := Option.some.inj hc
  subst c
  have h0 := he ⟨false,rfl⟩
  have h1 := he ⟨true,rfl⟩
  have hi := e.injective ((Option.some.inj h0).symm.trans (Option.some.inj h1))
  cases hi

theorem missing_candidate_rejected :
    ¬ (ArityDescriptor.missing repeatDiagram).ValidAt repeatArityContext (point "#F") := by
  rintro ⟨c,h,_⟩; cases h

noncomputable def repeatContext : Context registry repeatSignature singleGraph String where
  names := ⟨Function.Embedding.refl _, fun _ => "User", fun _ => none⟩
  arities := repeatArityContext
  describe d := by
    classical
    exact if h : d = repeatDiagram then h.symm ▸ repeatDescriptor else ArityDescriptor.missing d

def fragmentAd : Formula vocabulary.signature arityShape := ⟨.inr .ad, Prefunctor.id _⟩

def fragmentKeyBinding : Arity.fanOut 2 ⥤q arityShape where
  obj | .center => .formula | .member i => if i = 0 then .map else .signature
  map
    | .edge i => by
      change ArityEdge .formula (if i = 0 then .map else .signature)
      by_cases h : i = 0
      · rw [ite_eq_left h]; exact ArityEdge.args
      · rw [ite_eq_right h]; exact ArityEdge.pred

def fragmentKey : Formula vocabulary.signature arityShape :=
  vocabulary.embed ⟨.key 2, fragmentKeyBinding⟩
def fragmentTotal : Formula vocabulary.signature arityShape :=
  vocabulary.embed ⟨.total, arrowBinding ArityEdge.args⟩

def fragment : DPGraph vocabulary.signature where
  carrier := arityShape
  declarations := {f | f = fragmentAd ∨ f = fragmentKey ∨ f = fragmentTotal}

theorem extended_ad_satisfied : (interpretation repeatContext).Satisfies repeatDiagram fragmentAd := by
  change ArityDiscipline repeatArityContext repeatDiagram (repeatContext.describe repeatDiagram)
  simpa [repeatContext] using repeat_discipline

theorem extended_key_satisfied : (interpretation repeatContext).Satisfies repeatDiagram fragmentKey := by
  change Key _
  intro a b _
  exact Subsingleton.elim (α := one "#F") a b

theorem extended_total_satisfied : (interpretation repeatContext).Satisfies repeatDiagram fragmentTotal := by
  change Total (constant Bool "#F" "#M")
  intro f; exact ⟨false, Subsingleton.elim _ _⟩

def fragmentModel : (interpretation repeatContext).Model fragment :=
  ⟨repeatDiagram, by
    intro f hf
    rcases hf with rfl | rfl | rfl
    · exact extended_ad_satisfied
    · exact extended_key_satisfied
    · exact extended_total_satisfied⟩

theorem extended_args_not_setValued : ¬ SetValued (repeatDiagram.map ArityEdge.args) := by
  intro h
  have he := h (a₁ := false) (a₂ := true) rfl
  cases he

end FormalCD.Metamodel.Examples
