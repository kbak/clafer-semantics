module

public import Clafer.Examples.VersionCompilation
public import Clafer.Constraints.Predicate
public import Clafer.Constraints.DenotationDefined

-- [proof->req~clafer-constraint-preservation~1]

/-!
# Actual generated/glued Appendix 6 version predicate

SoSyM Appendix 6 c02, §6.2.2–5 and D.4. Local generated predicates establish
the scalar-navigation hypotheses. They do not establish the version inequality.
-/

@[expose] public section
namespace Clafer.Examples.VersionPreservation
open CategoryTheory DPGraph DPGraph.Predicates Constraints Compile VersionCompilation

variable {U : Type} (R : IntegerRealization U)

noncomputable def authored := predicateInterpretation input.constraint
  (fun _ => Domains.nil) R

noncomputable def interpretation := groupInterpretation input U (authored R)

theorem coherent (m : glued.carrier ⥤q semanticGraph U) (hm : LocalHolds m)
    (hd : (navigation m).obj (5 : VersionNavigation.support.Vertex) = R.domain) :
    (versionModel m hm R hd).toIntegerBinding.Coherent := by
  intro e f ho hk
  have he : e = f := by
    fin_cases e <;> fin_cases f <;> simp_all [VersionNavigation.support]
  subst f
  exact ⟨⟨Equiv.refl _, fun _ => rfl, fun _ => rfl⟩⟩

/-- This is the exact attached c02 formula, translated along its generated
label, with local multiplicities/inclusions extracted by `versionModel`. -/
theorem generated_version_iff (m : glued.carrier ⥤q semanticGraph U)
    (hm : LocalHolds m)
    (hd : (navigation m).obj (5 : VersionNavigation.support.Vertex) = R.domain) :
    (interpretation R).Satisfies m
      ((promote input (formula input (.inr q))).translate (groupLabel input)) ↔
      ∀ d : Subtype ((navigation m).obj (0 : VersionNavigation.support.Vertex)),
        VersionNavigation.comparison.Holds (versionModel m hm R hd).toIntegerBinding
          (.closed d.val) := by
  erw [Interpretation.satisfies_translate]
  change (navigation m) ∈ (authored R).meaning q ↔ _
  erw [predicate_meaning_iff input.constraint (fun _ => Domains.nil) R q
    (versionModel m hm R hd).toIntegerBinding rfl (coherent R m hm hd)]
  constructor
  · intro h d
    exact h d.val d.property
  · intro h x hx
    exact h ⟨x, hx⟩

/-- A defined false comparison remains a failed predicate. Definedness follows
from actual local formulas and the explicit primitive-domain interpretation. -/
theorem generated_operands_defined (m : glued.carrier ⥤q semanticGraph U)
    (hm : LocalHolds m)
    (hd : (navigation m).obj (5 : VersionNavigation.support.Vertex) = R.domain)
    (d : Subtype ((navigation m).obj (0 : VersionNavigation.support.Vertex))) :
    VersionNavigation.comparison.Defined (versionModel m hm R hd).toIntegerBinding
      (.closed d.val) :=
  VersionNavigation.denotation_defined (versionModel m hm R hd) d

end Clafer.Examples.VersionPreservation
