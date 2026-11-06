module

public import Clafer.Constraints.Predicate
public import Clafer.Constraints.DenotationSupport
public import Clafer.Examples.Telematics.Mutations
public import Clafer.Examples.VersionCompilation

/-!
[impl->req~clafer-constraint-preservation-witnesses~1]
[proof->req~clafer-constraint-preservation-witnesses~1]
-/

/-!
# Truth-sensitive source predicate examples

SoSyM Appendix 6 c02/c04/c06, D.4 and B.5. These exercise predicate
satisfaction on the complete support diagrams, not only body evaluation.
Structural compilation success is a separate assertion.
-/

@[expose] public section
namespace Clafer.Examples.ConstraintPredicates
open CategoryTheory DPGraph DPGraph.Predicates Clafer.Constraints
open Telematics.Expressions Telematics.ExpressionEnvironment Telematics.ExpressionExamples Telematics.Mutations

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def single (s : Support) (body : Expr s [] .boolean) (_ : Unit) : Constraint :=
  ⟨s, [], body⟩

noncomputable def interpreted (s : Support) (body : Expr s [] .boolean) :=
  predicateInterpretation (single s body) (fun _ => Domains.nil) integers

def formula (s : Support) (body : Expr s [] .boolean) :
    Formula (signature (single s body)) s.graph := ⟨(), Prefunctor.id s.graph⟩

theorem satisfies_iff (s : Support) (body : Expr s [] .boolean)
    (m : IntegerBinding s U) (hr : m.realization = integers) (hc : m.Coherent) :
    (interpreted s body).Satisfies m.model (formula s body) ↔
      ∀ x, (m.model.obj s.context : Set U) x → body.Holds m (.closed x) := by
  change (Prefunctor.id s.graph).comp m.model ∈
    (interpreted s body).meaning () ↔ _
  rw [Prefunctor.id_comp]
  exact predicate_meaning_iff (single s body) (fun _ => Domains.nil) integers () m hr hc

theorem moved_coherent (c : Fin 28) : (movedModel c).Coherent := by
  intro e f ho hk
  have he := map_identity_unique e f ho hk
  subst f
  exact ⟨⟨Equiv.refl _, fun _ => rfl, fun _ => rfl⟩⟩

/-- The existing one-display-per-ECU candidate fails the generated meaning of
the two-display equivalence, despite successful structural compilation. -/
theorem display_count_rejected :
    ¬ (interpreted (support 19) c06).Satisfies (model 19 2 3).model
      (formula (support 19) c06) := by
  rw [satisfies_iff _ _ _ rfl (model_coherent _ _ _)]
  intro h
  exact actual_c06_rejects_one_display (h (atom 19) (by
    change atom 19 ∈ objects 19
    simp [objects, position, Telematics.Structural.config, Telematics.Structural.heads]))

theorem display_count_accepted :
    (interpreted (support 19) c06).Satisfies (movedModel 19).model
      (formula (support 19) c06) := by
  rw [satisfies_iff _ _ _ rfl (moved_coherent _)]
  intro x hx
  have he : x = atom 19 := by
    change x ∈ objects 19 at hx
    simpa [objects, position, Telematics.Structural.config, Telematics.Structural.heads] using hx
  subst x
  exact c06_accepts_two

/-- Negating the actual typed body changes the meaning on the same complete
binding; assigning every fresh symbol True would fail this assertion. -/
theorem changed_count_body_accepted :
    (interpreted (support 19) (.not c06)).Satisfies (model 19 2 3).model
      (formula (support 19) (.not c06)) := by
  rw [satisfies_iff _ _ _ rfl (model_coherent _ _ _)]
  intro x hx
  have he : x = atom 19 := by
    change x ∈ objects 19 at hx
    simpa [objects, position, Telematics.Structural.config, Telematics.Structural.heads] using hx
  subst x
  have he := denotes_some _ _ _ _ (extra_value 2 3) (Set.finite_singleton _)
  have hc : (exactlyTwo displays1).denote (model 19 2 3) (.closed (atom 19)) = some ⟨False⟩ := by
    simp [exactlyTwo, Expr.denote, displays1_value, lift₂, finiteCard]
  have hv := denotes_iff _ _ _ _ _ _ he hc
  have hf : c06.denote (model 19 2 3) (.closed (atom 19)) = some ⟨False⟩ := by
    simpa [c06] using hv
  simp [Expr.Holds, denote_not, hf]

theorem wrong_server_parent_rejected :
    ¬ (interpreted (support 15) c04).Satisfies (movedModel 15).model
      (formula (support 15) c04) := by
  rw [satisfies_iff _ _ _ rfl (moved_coherent _)]
  intro h
  exact c04_rejects_wrong_owner (h (atom 5) (by
    change atom 5 ∈ objects 15
    simp [objects, position, Telematics.Structural.config, Telematics.Structural.heads]))

theorem server_parent_accepted :
    (interpreted (support 15) c04).Satisfies (model 15 2 3).model
      (formula (support 15) c04) := by
  rw [satisfies_iff _ _ _ rfl (model_coherent _ _ _)]
  intro x hx
  have hh : x = atom 4 ∨ x = atom 5 := by
    change x ∈ objects 15 at hx
    simpa [objects, position, Telematics.Structural.config, Telematics.Structural.heads] using hx
  rcases hh with rfl | rfl
  · exact actual_c04
  · simp only [c04, parent15, dereference12, head12, Expr.Holds, Expr.denote,
      lift₂, Option.bind_some, Option.map_some, image_reduced]
    simp [links, maps, objects, position, Telematics.Structural.config, Telematics.Structural.heads,
      Telematics.Structural.ownership, Telematics.Structural.targets, Environment.closed]

/-- Source version direction is preserved; the offending display alone is
enough to refute universal satisfaction. -/
theorem lower_version_rejected :
    ¬ (interpreted (support 11) c02).Satisfies (model 11 3 2).model
      (formula (support 11) c02) := by
  rw [satisfies_iff _ _ _ rfl (model_coherent _ _ _)]
  intro h
  exact actual_c02_lower (h (atom 4) (by
    change atom 4 ∈ objects 11
    simp [objects, position, Telematics.Structural.config, Telematics.Structural.heads]))

theorem version_value_at_every_display (e d : Int) (x : U) (hx : x ∈ objects 11) :
    c02.denote (model 11 e d) (.closed x) = some ⟨e ≤ d⟩ := by
  have hh : x = atom 4 ∨ x = atom 5 := by
    simpa [objects, position, Telematics.Structural.config, Telematics.Structural.heads] using hx
  rcases hh with rfl | rfl
  · exact actual_c02_value e d
  · apply denotes_ge
    · have hv : (dereference9 (head9 (.widenObjects inclusion11
          (Expr.this : Expr (support 11) [] _)))).denote (model 11 e d)
          (.closed (atom 5)) = some {integers.encode d} := by
        simp only [dereference9, head9, Expr.denote, lift₂, Option.bind_some,
          Option.map_some, image_reduced]
        simp [objects, maps, position, links, Telematics.Structural.config, Telematics.Structural.heads,
          Telematics.Structural.ownership, Environment.closed,
          FormalCD.IntegerRealization.domain, integers, Set.ext_iff]
      simp only [version, denote_integerOf, hv, Option.bind_some]
      exact congrArg (Option.map ULift.up) (integers.extract_encoded d)
    · have hv : (dereference9 (head9 (.widenObjects inclusion10
          (dereference12 (head12 (Expr.this : Expr (support 11) [] _)))))).denote
          (model 11 e d) (.closed (atom 5)) = some {integers.encode e} := by
        simp only [dereference9, head9, dereference12, head12, Expr.denote,
          lift₂, Option.bind_some, Option.map_some, image_reduced]
        simp [objects, maps, position, links, Telematics.Structural.config, Telematics.Structural.heads,
          Telematics.Structural.ownership, Telematics.Structural.targets, Environment.closed,
          FormalCD.IntegerRealization.domain, integers, Set.ext_iff]
      simp only [version, denote_integerOf, hv, Option.bind_some]
      exact congrArg (Option.map ULift.up) (integers.extract_encoded e)

theorem version_predicate_iff (e d : Int) :
    (interpreted (support 11) c02).Satisfies (model 11 e d).model
      (formula (support 11) c02) ↔ e ≤ d := by
  rw [satisfies_iff _ _ _ rfl (model_coherent _ _ _)]
  constructor
  · intro h
    have hv := h (atom 4) (by
      change atom 4 ∈ objects 11
      simp [objects, position, Telematics.Structural.config, Telematics.Structural.heads])
    simpa [Expr.Holds, actual_c02_value] using hv
  · intro h x hx
    simp [Expr.Holds, version_value_at_every_display e d x hx, h]

theorem version_order_sensitive :
    (interpreted (support 11) c02).Satisfies (model 11 2 3).model
        (formula (support 11) c02) ∧
    (interpreted (support 11) c02).Satisfies (model 11 2 2).model
        (formula (support 11) c02) ∧
    ¬ (interpreted (support 11) c02).Satisfies (model 11 3 2).model
        (formula (support 11) c02) := by
  simp [version_predicate_iff]

def external : Local (support 19) := ⟨⟨41⟩, "ecu", 17⟩
def externallyBound : Constraint := ⟨support 19, [external], .boolean false⟩
def liveDomain : Domains (support 19) [external] :=
  .cons external .nil (by simp) (.extent 17)
def emptyDomain : Domains (support 19) [external] :=
  .cons external .nil (by simp) (.setOp .difference (.extent 17) (.extent 17))

/-- External-binder handling evaluates its domain. An empty domain gives the
usual universal vacuity; the existing ECU2 object witnesses failure otherwise. -/
theorem external_domains_sensitive :
    externallyBound.Holds emptyDomain (model 19 2 3) ∧
      ¬ externallyBound.Holds liveDomain (model 19 2 3) := by
  constructor
  · intro x hx
    simp [externallyBound, emptyDomain, Domains.close, Expr.Holds, Expr.denote,
      lift₂, collectionOp, universal]
  · intro h
    have hh := h (atom 19) (by
      change atom 19 ∈ objects 19
      simp [objects, position, Telematics.Structural.config, Telematics.Structural.heads])
    simp [externallyBound, liveDomain, Domains.close, Expr.Holds, Expr.denote,
      universal, model, graphMap, objects, position, Telematics.Structural.config, Telematics.Structural.heads] at hh

/-- A context object cannot be substituted merely because the body is well
typed: c02's context is display, while an ECU is outside that class. -/
theorem wrong_context_rejected :
    ¬ (Environment.closed (atom 2)).Admissible (model 11 2 3) := by
  intro h
  have hc := h.1
  change atom 2 ∈ objects 11 at hc
  simp [objects, position, Telematics.Structural.config, Telematics.Structural.heads, atom] at hc

/-- Even a true version predicate at all displays cannot license evaluation
at an ECU object: the display-to-server path is then empty. -/
theorem wrong_context_body_rejected :
    ¬ c02.Holds (model 11 2 3) (.closed (atom 2)) := by
  simp only [c02, Expr.ge, version, dereference9, head9, dereference12, head12,
    Expr.Holds, Expr.denote, lift₂, Option.bind_some, Option.map_some, image_reduced]
  simp [objects, maps, position, links, Telematics.Structural.config, Telematics.Structural.heads,
    Telematics.Structural.ownership, Telematics.Structural.targets, Environment.closed, atom]

/-- Every inventory body has actual source navigation. Positive support is not
obtained by inventing a dummy edge for an otherwise vertex-only constraint. -/
theorem inventory_positive (q : Fin 12) : 0 < (inventory q).support.mapCount := by
  fin_cases q <;> decide

/-- The exact arity carries an arrow argument for every Appendix 6 occurrence,
which is the source-side witness used by Compile's total-args proof. -/
theorem inventory_total_args (q : Fin 12) :
    Nonempty (FormalCD.Metamodel.ArrowData (inventory q).support.graph) := by
  let e : (inventory q).support.Edge := ⟨0, inventory_positive q⟩
  exact ⟨⟨_, _, (inventory q).support.arrow e⟩⟩

theorem inventory_observes_map (q : Fin 12) : (inventory q).body.maps.Nonempty := by
  fin_cases q
  all_goals simp [inventory, Expr.maps, c01, c02, c03, c04, c05, c06, c07,
    c08, c09, c10, c11, c12, Expr.implies, Expr.iff, Expr.ge, Expr.some, Expr.no,
    exactlyTwo, displays1, displays2, inheritedCache, allSizes, version,
    head2, head3, head4, head5, head6, head7, head9, head12, head13, head15,
    head20, head22, head23, head24, head25, head26, dereference9, dereference12,
    parent15]

theorem structural_success_does_not_discharge_constraints :
    MCS.Valid (Compile.compile VersionCompilation.input).labels
      (Compile.compile VersionCompilation.input).formulas ∧
    ¬ (interpreted (support 11) c02).Satisfies (model 11 3 2).model
      (formula (support 11) c02) :=
  ⟨Compile.wellFormed _, lower_version_rejected⟩

end Clafer.Examples.ConstraintPredicates
