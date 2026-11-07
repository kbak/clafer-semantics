# Behavioral semantic qualification

`impl~behavioral-qualification-contract~1`

The [behavioral profile](behavioral-profile.md) defines independent infinite-trace
meaning for resolved structural declarations, strict partial observations,
effective modifiers, transitions, scoped patterns, assertions and scenarios.
Qualification composes those meanings and records their exact correspondence
with finite checking. Source meaning remains independent of the finite evaluator,
compiler frontend and Alloy backend. This document describes the accepted profile's
mathematical contract; acceptance and source-matched execution evidence belong
to the [qualification issue](https://github.com/kbak/clafer-semantics/issues/129)
and its PR.

Covers:
- `req~behavioral-qualification~1`
- `req~behavioral-source-correspondence~1`

## Full model and strict partial core

[Composition](../Clafer/Behavioral/Composition.lean) proves
`Properties.Model.behavioral_core_iff` for the entire source model: structural
well-formedness and trace validity, all effective inherited modifiers and every
attached constraint. `Modifiers.CoreHolds` expands every effective modifier,
including both parts of final. `Constraint.CoreHolds` retains the exact context
selector and evaluates the original attachment through all inner binders.

[PartialLowering](../Clafer/Behavioral/PartialLowering.lean) introduces
`CheckedAtom.value`, `atomDefined` and `domainDefined`. `domainFormula` translates
the original source tree's strict domain; `checkedCore` conjoins that translation
with signed normalization/lowering of truth. `domainFormula_agrees` and
`checkedCore_agrees` prove equivalence with independent `Formula.Defined` and
`Formula.Satisfies`, for every constructor, environment, time and sign.
There is no assumed preservation predicate.

The domain translation checks both sides of Boolean operations, all branches of
conditionals, every quantified member even for some/no/one/lone, and the entire
remaining active parent interval for F/G/U/W. An early eventuality witness does
not erase a later undefined observation. Next checks only its active next state;
inactive anchors and observations after parent cancellation have no domain
obligation. Captured sets and the original attachment survive each step. Missing
domains cannot become empty-domain vacuity. These are the accepted
[strict D3 rules](behavioral-structure.md#captured-static-atoms-and-partial-temporal-composition),
not new short-circuit semantics. Source negation and classical assertion failure
remain distinct.

The source translation is mathematical and noncomputable, as is the existing
normalizer. `Formula.Program` contains ordinary core syntax plus proofs of exact
equality to the domain and signed-value translations. Executable clients supply
that syntax; runtime checking does not call a noncomputable normalizer. A parser
or executable elaborator must prove its own representation equality.

## Finite composition and its boundaries

[FinitePartial](../Clafer/Behavioral/FinitePartial.lean) supplies executable
`Option Bool` atoms and `Option (Finset identity)` domains. Its `Agrees` contract
preserves values **and missingness**, for every captured environment and absolute
time on the lasso unfolding. `checked_agrees` constructs the existing total-core
adapter for both value and domain atoms. `Program.check_satisfied`,
`check_undefined` and `check_violated` distinguish strict satisfaction, missing
domain and defined falsehood. No missing value becomes a source Boolean result.
The arbitrary completion used internally is guarded by the proved domain.

[FiniteComposition](../Clafer/Behavioral/FiniteComposition.lean) adds exact finite
context selectors and finite constraint bundles. `Constraint.Finite.holds_iff`
and `FiniteBundle.holds_iff` prove implicit-always agreement for every selected
live context. `bodyCheck_correct` composes all constraints and all effective
modifier expansions into `Model.behavioral.Satisfies`, assuming independently
established richer structural admission. The modifier inventory must equal
`modifierConstraints`; omitting an inherited modifier cannot meet this premise.
`commonCheck_correct` additionally executes S6's structural lasso checks on the
historical guarded common fragment. `Transitions.Chain.finite_agrees` and
`Patterns.finite_agrees` connect the surface meanings directly to this strict
finite interface for both signs, including all thirty pattern/scope cases.

Finite observation restrictions are representation obligations, not restrictions
on the infinite source language:

- The supplied identity carrier is finite and fixed across the whole trace.
  Context and captured-domain sets enumerate identities, preserving repeated
  bag heads at equal targets. No per-state renaming is permitted.
- Values and missingness must depend on the history-aware finite clock and
  captured environment as certified by `Agrees`. Arbitrary absolute-time or
  unbounded-history observations have no automatic adapter. Merely sampling
  stored frames does not establish that proof.
- The concrete total set adapter is provided. Additional structural/primitive
  adapters must establish exact current-reference and partial-domain agreement.
  The all-Int `IntegerRealization` used by the independent primitive semantics
  cannot be embedded injectively into `Fin size`; this finite-carrier interface
  is not an executable adapter for that entire primitive universe. Mathematical
  arithmetic and finite observed integer sets retain their independent source
  theorems. A downstream finite integer representation needs its own adequacy
  and range proofs, including intermediate operations.
- Richer structural admission remains separately proved; `commonCheck` executes
  admission only under the unchanged `EffectiveCore` well-formedness/support and
  effective-group agreement guards. Its Boolean result means satisfaction of
  this supplied candidate, not general source unsatisfiability.

The [S6 contract](behavioral-verification.md) supplies finite-orbit completeness
for one lasso, including initial history, loop-edge births/deaths and cancellation
without resumption. None of these results proves completeness over all infinite
traces, inferred scopes, a solver, source parsing, or Haskell/Alloy preservation.
Those are explicit downstream obligations in the [ownership contract](behavioral-profile.md#ownership-and-proposed-module-boundaries).

## Exact static common fragment

`Model.common_iff` proves that the full behavioral model with no modifiers or
constraints agrees exactly with `Trace.Valid` on the guarded static fragment.
`Model.common_snapshot` derives historical `StructuralSatisfies` on the live
carrier. `Model.constant_iff` proves the converse iff for an existing static
configuration with an explicit `StaticCorrespondence`: fixed direct types,
actual parents, complete inherited head extents and containment correspondence.
It does not infer that witness from arbitrary overlapping extents.

Well-formedness, `Supported`, and agreement of the effective group table with
the family remain explicit. The [static atom bridge](behavioral-structure.md)
separately retains captured-environment, live-this and definedness hypotheses;
the common-fragment theorem does not silently identify the paper's snapshot-pair
environment with D1's current navigation. Generic DPGraph/FormalCD models, static
Compile/gluing, structural checker behavior and historical oracle pins are unchanged.

## Complete source and witness inventory

`impl~behavioral-source-qualification-inventory~1`

The [B01–B32 source matrix](behavioral-profile.md#feature-disposition-matrix)
owns each exact paper/erratum/CheatSheet locator. The table below closes its
source-side accounting with actual declarations and distinguishing witnesses.
The composition assumptions are stated above and in the
[composition proofs](../Clafer/Behavioral/Composition.lean). Source feature accounting is separate from maintainer
acceptance and downstream frontend/encoding qualification.

| Rows | Actual source meaning and proof | Positive / negative evidence and retained boundary |
| --- | --- | --- |
| B01 | `Structural.Core.WellFormed`, `Structural.Valid`, `valid_iff_common` | `StructuralExamples.admitted`, ordinary inherited fields and concrete supers / direct authored-abstract, wrong-group and conflicting-refinement rejection; richer admission is separate from old guards |
| B02–B03 | `Identities.Valid`, `Trace.Valid`, `parent_stable`, `Starts`, `Ends`, `snapshot_structural` | `Examples.cycling_valid`, constant bag/inheritance witnesses / orphan, switched-parent and switched-type rejection; identities persist through gaps |
| B04–B05 | `Structural.Keys`, `Structural.Groups`, `InheritedReference.deref`, group/head observation bridges | `inherited_bag_changes_target`, `inherited_group_counts_occurrences` / `set_duplicates_rejected`, `inherited_group_overflow_rejected`, `dead_target_rejected`; groups count head identities |
| B06 | `SetExpr.eval`, `Structural.observed`, `InheritedReference.Owner.unique`, full `StructuralBinding.Resolution` | `absent_this_and_parent`, `captured_deref`, inherited owner witnesses / dead-head and conflicting-refinement rejection; resolved views, no name resolution theorem |
| B07–B08 | `Environment.push`, `CapturedStatic.agrees`, `Formula.extension_agrees`, `PrimitiveExpression` | `capture_survives_absence`, `current_reference_not_snapshot`, `captured_bag_heads`, `nested_capture` / strict partial and wrong-domain witnesses; D1/D3 are explicit departures |
| B09–B14 | `Formula.denote`, `normalize_agrees`, `normalize_lower_agrees`, `persistent_eventually_consistent` | `FormulaExamples` next/F/G/U/W, both signs, counting barriers and Boolean cases / late-negation, source-death and persistent-parent rejection; no classical complement claim for source signs |
| B15 | `Formula.PartialAttached`, `Constraint.Finite.holds_iff`, `Anchors.root_recurrence` | Full replaceable cancellation model / stable-parent rejection; anchored existence versus recurrence in `AnchorExamples`, plus `PatternExamples.root_attachment_not_initially` |
| B16–B19 | `Modifiers.Effective`, `Initial`, `Final`, `FinalRef`, `FinalTarget`, `expand_agrees`, `enumLiteral` | Inherited initial/final references, fixed heads, target swaps and dynamic enum / missing rebirth, per-head swap and inherited-reference mutation; `ModifierBoundaryExamples` adds combined direct/inherited obligations, independent failures, head replacement, exact-three-head target multiplicities and lifetime resets. D5 image semantics is corrected after the historical pin by `b2875f3`; all modifiers are retained by `8a12ae7` ([revision comparison](sources.md#pr113-modifier-and-pattern-revisions)) |
| B20–B21 | `Anchors.AtBirths`, `AtDeaths`, `initially_at_births`, `finally_at_deaths` | Time zero, repeated birth and never-ending finality / second-birth omission and post-death event; finite clock retains first-visit history |
| B22–B25 | `Transitions.Chain.meaning`, `required`, `expand_agrees`, `finite_agrees` | Three-state guarded chains, parent cancellation, reappearance / missing middle, subsequent guard, source disappearance and nested-implication bug; first source alone is conditional |
| B26 | `Patterns.meaning`, `expand_agrees`, `response_interval`, `first_opener`, `finite_agrees` | `all_thirty_positive`, `all_thirty_negative`, `all_thirty_opposite_signs`, boundary witnesses / pinned response-between and later-opener regressions; both D2 regressions retained, plus root attachment versus initially. Errors at `af858ec` are corrected by `b2875f3` ([revision comparison](sources.md#pr113-modifier-and-pattern-revisions)) |
| B27–B28 | `Model.Asserts`, `Counterexample`, `Possible`, `withScenario`, `counterexample_iff`, `possible_iff` | Two valid traces separate possible from universal; nested sibling and negative-scenario witnesses reject vacuous alternatives; failure negates the whole interpreted judgment |
| B29 | Resolved `Formula`, `Chain`, `Pattern`/`Scope`, source expansion and normalization interfaces | Source alias/attachment meaning is explicit; production parsing, precedence, resolution and source-position preservation remain compiler C7 obligations, not a claimed upstream parser |
| B30 | `Lasso.unfold`, `valid_iff_unfold`, `Core.finite_agrees`, `Program.check_satisfied` | Nonzero prefix, loop-edge birth, first-entry history, capture and cancellation / invalid loop, empty trace, metadata switch; exact supplied lassos only |
| B31 | `IntegerObservation.coerce`, `Arithmetic.Binary.apply`, `Aggregate.Fold.eval`, `PrimitiveExpression`, `Formula.Defined` | Empty-to-zero versus presence, distinct targets versus repeated folds, arbitrary Int / zero divisors, infinite/wrong-domain sets and undefined operands; finite representation limits above remain explicit |
| B32 | `Initializers.constant`, `every_live_state`, `default_rejected`, adopted effective defaults | Constant equations persist beyond birth / `:=` explicitly rejected; frontend defaults and temporal birth remain separate |

The [T1–T13 disposition table](behavioral-profile.md#errata-coverage-and-deliberate-departures)
is exhaustive: T1/T13 map to B02–B03/B30, T2 to signed meaning and composition,
T3/T4 to transition attachment/chains, T5/T6 to properties/scenarios, T7 to
anchors, T8 to inherited modifiers, T9 to implicit recurrence, T10/T11 to the
structural prerequisites, and T12 to the explicit downstream syntax obligation.
The [D1–D5 register](behavioral-profile.md#decisions-requiring-contract-review)
retains every adopted semantic departure; none is reclassified as compiler equality.

Covers:
- `req~behavioral-source-correspondence~1`

## Source disposition and acceptance

The immutable profile remains `behavioral-0.5.7-candidate/v1` at
`gsdlab/clafer@af858ec0fe3ce2ceacb7fd120947c058233086d6`, with the reviewed D1–D5
dispositions. The [source ledger](sources.md#behavioral-profile-sources) supplies
exact blob hashes and licenses. This is an independently defined source profile,
not a claim that the Haskell compiler implements all accepted corrections.

The [PR113 modifier/pattern comparison](sources.md#pr113-modifier-and-pattern-revisions)
records corrections after that historical pin: `b2875f3` corrects response-between,
first-opener precedence-after and parent-scoped finaltarget; `8a12ae7` retains all
reference modifiers. The exact-three-head witnesses retain direct/inherited
conjunctions, independent failures, multiplicities, replacement and lifetime
resets. The root assertion witness distinguishes implicit always from initially.
The later singleton fixture and temporal explicit-output patches are comparison
context; reading them supplies no new Haskell execution or toolchain adoption.
Historical mutants, pins and receipts remain unchanged.

The compared later candidate
[`b6c38617b203c17f57b994546172801ddaaf88c2`](https://github.com/gsdlab/clafer/commit/b6c38617b203c17f57b994546172801ddaaf88c2)
adds five commits. In the reference-file delta, both errata documents and
`Desugarer.hs` are unchanged; `CheatSheet.md` adds static `clafer` and empty
`noclafer`, and `AlloyLtl.hs` adds the empty-set case. Other changes include UID
generation, explicit-model printing, resolution and regression outputs. This
bounded comparison does not qualify those frontend/backend changes or replace
the source pin. The source [release PR](https://github.com/gsdlab/clafer/pull/113)
was still open when this immutable comparison was prepared.

The [later comparison disposition](sources.md#pr113-root-binding-and-final-comparison-disposition)
records the accepted downstream `c7a2fb7` profile, its retained discrepancies and
the inspected two-commit delta through `8cfa0f3`. It preserves the primary source
identity and makes no claim of final-release qualification.

The immutable prerelease profile with D1–D5 is accepted; its qualification
evidence and acceptance record remain on the [qualification issue](https://github.com/kbak/clafer-semantics/issues/129).
A later source-profile change still requires explicit delta review and acceptance.
Main integration requires the concrete candidate's full validation, independent
review and merge authorization under the [ordered release gates](behavioral-profile.md#integration-and-acceptance).
Historical IntentBond exit-4 evidence retains its original review-pending status;
acceptance is recorded separately.
