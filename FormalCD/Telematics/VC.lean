module

public import FormalCD.Telematics.Basic
public import FormalCD.Integer
public import DPGraph.Predicates.Relational

/-!
# Corrected, guarded VC interpretation

SoSyM Figure 8 line 9, its §4.2.3 discussion (and §4.3 configuration context),
Figure 21a–b / §6.1.2 and Appendix 6.
The accepted Q7 direction is display.version ≥ server.version; the adjacent
reversed prose is not adopted. The comparison is guarded by the presence of a
server link, as in Figure 21a. An absent server satisfies the comparison vacuously.
This FormalCD extension leaves all built-in meanings unchanged.

For U : Type u, vertices of semanticGraph are Set U and links are in
Type (max u w). Integer realization is explicit local interpretation data;
it is not a global primitive-domain framework or an all-universes SetMap.
-/

@[expose] public section

universe u w
namespace FormalCD.Telematics
open CategoryTheory DPGraph.Predicates

export FormalCD (IntegerRealization)

namespace IntegerRealization
export FormalCD.IntegerRealization (domain)
end IntegerRealization

/-- Follow an inclusion link then a version link, retaining both link witnesses. -/
def InheritedVersion {U : Type u} (R : IntegerRealization U) {A C B : Set U}
    (inc : DPGraph.Span.{u,u,max u w} A C) (version : DPGraph.Span.{u,u,max u w} C B)
    (a : A) (n : Int) : Prop :=
  ∃ i v, inc.source i = a ∧ version.source v = inc.target i ∧
    R.decode (version.target v).val = n

-- [impl->req~formalcd-vc-semantics~1]
/-- Quantify over actual server links. An empty server fiber imposes no comparison. -/
def VCMeaning {U : Type u} (R : IntegerRealization U)
    (d : vcShape ⥤q semanticGraph.{u,w} U) : Prop :=
  d.obj .int = R.domain ∧
  ∀ s : (d.map VCEdge.server).Link, ∀ nd ne : Int,
    InheritedVersion R (d.map VCEdge.i2) (d.map VCEdge.version)
      ((d.map VCEdge.server).source s) nd →
    InheritedVersion R (d.map VCEdge.i1) (d.map VCEdge.version)
      ((d.map VCEdge.server).target s) ne → ne ≤ nd

def vcInterpretation {U : Type u} (R : IntegerRealization U) :
    DPGraph.Interpretation extraSignature (semanticGraph.{u,w} U) where
  meaning | .vc => VCMeaning R

def interpretation {U : Type u} (R : IntegerRealization U) :
    DPGraph.Interpretation vocabulary.signature (semanticGraph.{u,w} U) :=
  Vocabulary.extendInterpretation (DPGraph.Predicates.interpretation U) (vcInterpretation R)

theorem builtins_unchanged {U : Type u} (R : IntegerRealization U) :
    vocabulary.restrict (interpretation.{u,w} R) = DPGraph.Predicates.interpretation U :=
  Vocabulary.restrict_extend _ _

theorem satisfies_vc {U : Type u} (R : IntegerRealization U)
    (m : graph ⥤q semanticGraph.{u,w} U) :
    (interpretation R).Satisfies m vc ↔ VCMeaning R (vcBinding.comp m) := Iff.rfl

/-- The 1..1 notation gives total and single-valued maps in the existing link semantics. -/
theorem one_one_total_single {A B : Type u} (q : DPGraph.Span.{u,u,max u w} A B)
    (h : TargetMultiplicity ⟨1, .finite 1⟩ q) : Total q ∧ SingleValued q :=
  (DPGraph.Predicates.one_iff_total_single q).mp h

/-- The 0..1 notation gives single-valuedness without totality. -/
theorem zero_one_single {A B : Type u} (q : DPGraph.Span.{u,u,max u w} A B)
    (h : TargetMultiplicity ⟨0, .finite 1⟩ q) : SingleValued q := by
  apply (singleValued_fibers q).mpr
  intro a
  obtain ⟨_, ⟨hi⟩⟩ := h a
  exact ⟨fun l k => hi.injective (Subsingleton.elim _ _)⟩

/-- Literal inclusion changes membership evidence while preserving the ambient object. -/
def asComponent {U : Type u} {A C : Set U} {inc : DPGraph.Span.{u,u,max u w} A C}
    (h : Inclusion inc) (a : A) : C := ⟨a.val, inclusion_subset h a.property⟩

noncomputable def versionValue {U : Type u} (R : IntegerRealization U) {C B : Set U}
    (version : DPGraph.Span.{u,u,max u w} C B) (h : Total version) (c : C) : Int :=
  R.decode (version.target (Classical.choose (h c))).val

theorem versionValue_link {U : Type u} (R : IntegerRealization U) {C B : Set U}
    (version : DPGraph.Span.{u,u,max u w} C B) (ht : Total version)
    (hs : SingleValued version) (l : version.Link) :
    versionValue R version ht (version.source l) = R.decode (version.target l).val := by
  unfold versionValue
  rw [hs (Classical.choose_spec (ht (version.source l)))]

/-- Inclusion and 1..1 version links justify functional integer navigation. -/
theorem inherited_iff_value {U : Type u} (R : IntegerRealization U) {A C B : Set U}
    (inc : DPGraph.Span.{u,u,max u w} A C) (version : DPGraph.Span.{u,u,max u w} C B)
    (hi : Inclusion inc) (ht : Total version) (hs : SingleValued version) (a : A) (n : Int) :
    InheritedVersion R inc version a n ↔
      n = versionValue R version ht (asComponent hi a) := by
  constructor
  · rintro ⟨i,v,ha,hv,hn⟩
    have hc : inc.target i = asComponent hi a := Subtype.ext ((hi.2 i).trans (congrArg Subtype.val ha))
    rw [← hc, ← hv, versionValue_link R version ht hs, hn]
  · intro hn
    obtain ⟨i,ha⟩ := hi.1.2 a
    have hc : inc.target i = asComponent hi a := Subtype.ext ((hi.2 i).trans (congrArg Subtype.val ha))
    obtain ⟨v,hv⟩ := ht (inc.target i)
    refine ⟨i,v,ha,hv,?_⟩
    rw [hn, ← hc, ← hv, versionValue_link R version ht hs]

/-- A served display must compare with each server; an unserved display is vacuous. -/
def GuardedComparison {U : Type u} (m : graph ⥤q semanticGraph.{u,w} U)
    (h1 : Inclusion (m.map Edge.i1)) (h2 : Inclusion (m.map Edge.i2))
    (value : Subtype (m.obj .comp) → Int) : Prop :=
  ∀ d e, (m.map Edge.server).red d e →
    value (asComponent h1 e) ≤ value (asComponent h2 d)

-- [proof->req~formalcd-vc-semantics~1]
/-- Under the actual inclusion/version declarations, VC is exactly the guarded
integer comparison. No inverse, cover or server-totality assumption is needed. -/
theorem satisfies_vc_iff_guarded {U : Type u} (R : IntegerRealization U)
    (m : graph ⥤q semanticGraph.{u,w} U) (domain : m.obj .int = R.domain)
    (h1 : Inclusion (m.map Edge.i1)) (h2 : Inclusion (m.map Edge.i2))
    (hv : TargetMultiplicity ⟨1, .finite 1⟩ (m.map Edge.version)) :
    (interpretation R).Satisfies m vc ↔
      GuardedComparison m h1 h2
        (versionValue R (m.map Edge.version) (one_one_total_single _ hv).1) := by
  let ht := (one_one_total_single _ hv).1
  let hs := (one_one_total_single _ hv).2
  change (m.obj .int = R.domain ∧ _) ↔ _
  constructor
  · intro h d e ⟨s,hd,he⟩
    apply h.2 s
    · apply (inherited_iff_value R _ _ h2 ht hs _ _).mpr
      exact congrArg (fun x => versionValue R (m.map Edge.version) ht (asComponent h2 x)) hd.symm
    · apply (inherited_iff_value R _ _ h1 ht hs _ _).mpr
      exact congrArg (fun x => versionValue R (m.map Edge.version) ht (asComponent h1 x)) he.symm
  · intro h
    refine ⟨domain, ?_⟩
    intro s nd ne hd he
    rw [(inherited_iff_value R _ _ h2 ht hs _ _).mp hd,
      (inherited_iff_value R _ _ h1 ht hs _ _).mp he]
    exact h _ _ ⟨s,rfl,rfl⟩

-- [proof->req~formalcd-figure21-example~1]
/-- The same correspondence stated directly in terms of the example's typed
inclusion and multiplicity declarations. -/
theorem declared_vc_iff_guarded {U : Type u} (R : IntegerRealization U)
    (m : graph ⥤q semanticGraph.{u,w} U) (domain : m.obj .int = R.domain)
    (h1 : (interpretation R).Satisfies m (declaration .i1))
    (h2 : (interpretation R).Satisfies m (declaration .i2))
    (hv : (interpretation R).Satisfies m (declaration .versionMult)) :
    (interpretation R).Satisfies m (declaration .vc) ↔
      GuardedComparison m h1 h2
        (versionValue R (m.map Edge.version) (one_one_total_single _ hv).1) :=
  satisfies_vc_iff_guarded R m domain h1 h2 hv

end FormalCD.Telematics
