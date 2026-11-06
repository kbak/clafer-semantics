module

public import Clafer.Constraints.DenotationDefined
public import Clafer.Constraints.DenotationInvariance
public import Clafer.Constraints.IntegerExamples

/-! # Sensitive kernel-checked denotation examples

SoSyM D.4/Figure 28 and Appendix 6. Assertions exercise the actual typed
constructors. Positive and negative results distinguish intersection from
union/difference, joins from projections, and all from Option.some.
-/

@[expose] public section
namespace Clafer.Constraints.DenotationExamples
open IntegerExamples VersionNavigation

abbrev m := (IntegerExamples.model 2 3).toIntegerBinding
abbrev env : Environment support U [] := .closed display.val

def comp : Expr support [] (.collection (.objects 2)) := .extent 2
def self : Expr support [] (.collection (.objects 2)) := .widenObjects displayWiden .this

theorem intersection_common :
    (Expr.setOp .intersection comp self).denote m env = Option.some {atom 1} := by
  simp [Expr.denote, comp,self,env,m,model,modelMap,objects,lift₂,collectionOp,display,Environment.closed]

theorem difference_other :
    (Expr.setOp .difference comp self).denote m env = Option.some {atom 0} := by
  simp [Expr.denote, comp,self,env,m,model,modelMap,objects,lift₂,collectionOp,display,Environment.closed,atom]

-- [proof->req~clafer-constraint-semantic-laws~1]
theorem intersection_is_not_difference :
    (Expr.setOp .intersection comp self).denote m env ≠
      (Expr.setOp .difference comp self).denote m env := by
  rw [intersection_common,difference_other]
  simp [atom]

def empty : Expr support [] (.collection (.objects 2)) := .setOp .difference comp comp

theorem empty_denotes : empty.denote m env = Option.some ∅ := by
  simp [empty,Expr.denote,comp,lift₂,collectionOp]

theorem no_empty : empty.no.Holds m env := by
  unfold Expr.Holds
  rw [denotes_no m env empty ∅ empty_denotes Set.finite_empty]
  simp

theorem some_empty_fails : ¬ empty.some.Holds m env := by
  unfold Expr.Holds
  rw [denotes_some m env empty ∅ empty_denotes Set.finite_empty]
  simp

-- Both joins, using the actual server head and dereference maps.
def joinedServer : Expr support [] (.collection (.objects 1)) :=
  .image .this (.join (.map 4) (.map 5))

-- [proof->req~clafer-appendix-f-expressions~1]
theorem joined_server : joinedServer.denote m env = Option.some {ecu.val} := by
  change Option.some (relationalImage {display.val}
    (relationalJoin (ambientRelation (maps 2 3 4)) (ambientRelation (maps 2 3 5)))) = _
  have h := (congrArg (relationalImage {display.val})
    (join_span (maps 2 3 4) (maps 2 3 5))).trans
      (image_span ((maps 2 3 4).comp (maps 2 3 5)) {display.val})
  refine (congrArg Option.some h).trans ?_
  change Option.some (navigationImage ((DPGraph.Span.ofFunction (fun _ : objects 0 => serverRef)).comp
    (DPGraph.Span.ofFunction (fun _ : objects 4 => ecu))) {display.val}) = _
  congr 1
  ext y
  constructor
  · rintro ⟨l,_,ht⟩
    exact ht.symm
  · intro hy
    exact ⟨⟨(display,serverRef),rfl⟩,rfl,hy.symm⟩

theorem joined_server_not_reference_head :
    joinedServer.denote m env ≠ Option.some {serverRef.val} := by
  rw [joined_server]
  simp [ecu,serverRef,atom]

def outer : Local support := ⟨⟨1⟩,"x",2⟩
def inner : Local support := ⟨⟨2⟩,"x",2⟩

def allSelf : Expr support [] .boolean :=
  .all outer (by simp) comp (.equal (.var .here) (.widenObjects displayWiden .this))

theorem universal_detects_counterexample : allSelf.denote m env = Option.some ⟨False⟩ := by
  simp [allSelf,Expr.denote,comp,universal,Environment.push,lift₂,
    m,model,modelMap,objects,env,Environment.closed,display,atom,outer]

def vacuous : Expr support [] .boolean := .all outer (by simp) empty (.boolean false)

theorem empty_universal : vacuous.Holds m env := by
  change (empty.denote m env).bind
    (fun S => universal S (fun _ => some ⟨(false : Bool) = true⟩)) = some ⟨True⟩
  rw [empty_denotes]
  exact universal_empty _

/-- The inner domain reads the outer variable before entering the inner scope. -/
def shadow : Expr support [] .boolean :=
  .all outer (by simp) comp
    (.all inner (by simp [outer,inner]) (.var .here)
      (.equal (.var .here) (.var (.there .here))))

theorem nested_shadowing : shadow.Holds m env := by
  simp [Expr.Holds,shadow,Expr.denote,universal,lift₂,Environment.push,
    comp,outer,inner]

/-- Same names do not capture the outer variable: the two lexical positions
can select distinct objects. -/
def shadowCounterexample : Expr support [] .boolean :=
  .all outer (by simp) comp
    (.all inner (by simp [outer,inner]) (.widenObjects displayWiden .this)
      (.equal (.var .here) (.var (.there .here))))

theorem shadow_does_not_capture : shadowCounterexample.denote m env = Option.some ⟨False⟩ := by
  simp [shadowCounterexample,Expr.denote,universal,lift₂,Environment.push,
    comp,m,model,modelMap,objects,env,Environment.closed,display,atom,outer,inner]

theorem arithmetic_negative :
    (Expr.arithmetic .subtract (.integer (-3)) (.integer 4) : Expr support [] .integer).denote m env =
      Option.some ⟨-7⟩ := rfl

theorem greater_version : comparison.Holds m env := by
  have h := comparison_agrees (model 2 3) display 3 2 (display_objects 2 3)
    (server_version_objects 2 3)
  simpa [Expr.Holds,m,env] using h

theorem equal_version :
    comparison.Holds (IntegerExamples.model 2 2).toIntegerBinding (.closed display.val) := by
  have h := comparison_agrees (model 2 2) display 2 2 (display_objects 2 2)
    (server_version_objects 2 2)
  simpa [Expr.Holds] using h

theorem lower_version_fails :
    ¬ comparison.Holds (IntegerExamples.model 3 2).toIntegerBinding (.closed display.val) := by
  have h := comparison_agrees (model 3 2) display 2 3 (display_objects 3 2)
    (server_version_objects 3 2)
  simp [Expr.Holds,h]

/-- The second occurrence remains in the syntax; set union is idempotent. -/
theorem repeated_map_union :
    (Expr.setOp .union (.map 4) (.map 4) : Expr support [] _).denote m env =
      (Expr.map 4).denote m env := by
  simp [Expr.denote,lift₂,collectionOp]

/-- Cardinality of an infinite integer extent is undefined, never zero. -/
theorem infinite_integer_cardinality :
    finiteCard (Set.univ : Set Int) = none := by
  exact finiteCard_infinite _ Set.infinite_univ

/-- Two different reference heads remain two counted objects, while their
common dereferenced target is one element of a navigation result. -/
def referenceHeads : Set Int := {10,11}
def bagDeref : Set (Int × Int) := {(10,42),(11,42)}

theorem head_count : finiteCard referenceHeads = some ⟨2⟩ := by
  simp [finiteCard,referenceHeads]

theorem target_image : relationalImage referenceHeads bagDeref = {42} := by
  ext x
  simp [relationalImage,referenceHeads,bagDeref]

theorem reduced_target_count : finiteCard (relationalImage referenceHeads bagDeref) = some ⟨1⟩ := by
  rw [target_image]
  simp [finiteCard]

/-- The actual span still carries both reference occurrences at equal targets. -/
abbrev occurrenceSpan : DPGraph.Span Unit Int where
  Link := Fin 2
  source _ := ()
  target _ := 42

theorem occurrence_links_distinct :
    (0 : occurrenceSpan.Link) ≠ 1 ∧ occurrenceSpan.target 0 = occurrenceSpan.target 1 := by
  decide

theorem occurrence_fiber_count :
    Nat.card (occurrenceSpan.toFamily.Index ()) = 2 := by
  simp [DPGraph.Span.toFamily,occurrenceSpan]

/-- Extraction failure propagates through Boolean comparison and a quantifier
on a nonempty domain, while an empty domain does not inspect its body. -/
def emptyIntegers {Γ} : Expr support Γ (.collection (.objects 5)) :=
  .setOp .difference (.extent 5) (.extent 5)

def undefinedComparison {Γ} : Expr support Γ .boolean :=
  .less (.integerOf rfl emptyIntegers) (.integer 0)

theorem empty_extraction :
    (Expr.integerOf rfl emptyIntegers : Expr support [] _).denote m env = none := by
  simp [emptyIntegers,Expr.denote,lift₂,collectionOp]

theorem comparison_undefined {Γ} (ρ : Environment support U Γ) :
    undefinedComparison.denote m ρ = none := by
  simp [undefinedComparison,emptyIntegers,Expr.denote,lift₂,collectionOp]

theorem nonempty_undefined_quantifier :
    (Expr.all outer (by simp) comp undefinedComparison).denote m env = none := by
  change universal (objects 2)
    (fun x => undefinedComparison.denote m (env.push outer x)) = none
  exact universal_undefined _ _ (atom 0) (by simp [objects]) (comparison_undefined _)

theorem empty_undefined_quantifier :
    (Expr.all outer (by simp) empty undefinedComparison).Holds m env := by
  change (empty.denote m env).bind
    (fun S => universal S (fun x => undefinedComparison.denote m (env.push outer x))) = some ⟨True⟩
  rw [empty_denotes]
  exact universal_empty _

end Clafer.Constraints.DenotationExamples
