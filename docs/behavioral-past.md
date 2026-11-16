# Past-time formulas and core lowering

The past-time foundation defines previous, once, historically, since and triggered
within the **original attachment's parent's current lifetime**. A child may look
back before its own birth while that parent remains continuously live. A parent
gap excludes the earlier lifetime, even when the same identity reappears. The
synthetic root supplies an always-present guard. Quantification captures an
identity without changing attachment.

This extends the behavioral paper §5 Definitions 3–5 / §6.1, following the
[selected source and lifetime decision](sources.md#past-time-extension).
Independent interval laws, source formulas, signed normalization, strict partial
domains and initializer lowering are exposed through `Clafer.Behavioral`. The
[formula/core integration](https://github.com/kbak/clafer-semantics/issues/188)
adds exact finite evaluation through history-carrying machines. Downstream parser
and backend adoption and Haskell comparison qualification remain separate.

## Independent meanings and ordinary encoding

[`Past.lean`](../Clafer/Behavioral/Past.lean) uses `Signal := Nat → Prop` and the
existing inclusive interval `Lifetime.Through P j t`: the parent is present at
every state from `j` through `t`. Ordinary `Temporal` operators have unrestricted
natural-number history; `Lifetime` operators supply independent guarded meanings.

| Operator | Independent lifetime meaning at time `t` |
| --- | --- |
| Previous `a` | At time zero, false; at `t + 1`, `P t ∧ a t` |
| Weak previous `a` | At time zero, true; at `t + 1`, `P t → a t` |
| Once `a` | Some `j ≤ t` has `Through P j t` and `a j` |
| Historically `a` | Every `j ≤ t` with `Through P j t` has `a j` |
| `a` since `b` | Some `j ≤ t` has `Through P j t` and `b j`, with `a` at every `j < k ≤ t` |
| `a` triggered `b` | For every `j ≤ t` with `Through P j t`, if `a` is false throughout `j < k ≤ t`, then `b j` |

Since includes its right operand at the witness and its left operand strictly
after it. Triggered uses the conventional dual of since, including the current
state. Weak previous is the internal dual needed for negative strong previous;
this foundation adds no surface keyword.

The six `*_lower` theorems prove agreement with ordinary encodings:

| Lifetime operation | Ordinary past expression |
| --- | --- |
| Previous `a` | `previous (P ∧ a)` |
| Weak previous `a` | `¬ previous (P ∧ ¬a)` |
| Once `a` | `P since (P ∧ a)` |
| Historically `a` | `¬ (P since (P ∧ ¬a))` |
| `a` since `b` | `(P ∧ a) since (P ∧ b)` |
| `a` triggered `b` | `¬ ((P ∧ ¬a) since (P ∧ ¬b))` |

These pointwise laws hold over arbitrary signals, without a finite-trace
assumption or restriction to current-state atoms. Separate duality and
permanent-parent laws establish the ordinary meanings. Gap and reset laws exclude
earlier witnesses. At an absent current parent, once/since are false and
historically/triggered are vacuous. Previous tests the preceding state; current
presence belongs to attachment and is not silently added to its equation.

## Initializer birth tests

[`InitializerPast.lean`](../Clafer/Behavioral/InitializerPast.lean) proves
`birth_iff_not_previous` for a current head `x`. Its hypotheses require a stable
declaration view: at every time, membership is exactly a time-independent
selection predicate conjoined with liveness. Head membership must imply the
selected enclosing presence guard. These hypotheses exclude arbitrary sets
filtered by a changing constraint, where entering the set need not be birth.

Under those hypotheses, `Trace.Starts t x` is equivalent to the captured head
having no preceding membership. `equations_agree` lifts that result to all
per-instance initializer equations, matching `Candidate.SingleBirths`. The RHS
remains the same partial observation in its original resolved parent/root
environment; use the existing [transport contract](behavioral-initializers.md#production-transport-and-proof-domain)
to construct it. No equality between independently re-resolved RHS expressions
is assumed. The result includes time zero, disappearance and rebirth.

`enclosing_guard_agrees` proves that replacing one enclosing presence guard with
another implied by the head does not change this birth test. General past
formulas still distinguish parent lifetime from context lifetime.

The implication in these equations is a **declaration guard**. The
[accepted definedness policy](behavioral-initializers.md#guard-collection-and-inheritance-meanings)
does not demand an RHS value at inactive births. Ordinary source implication
remains strict. `strict_implication_requires_rhs` and its witness show that an
undefined RHS fails even under a false ordinary antecedent. Consequently the
birth-test theorem alone does not justify emitting a plain source implication
for arbitrary partial RHSs. `InitializerLowering.lowerCore` preserves the guard and its domain separately.
`expandAnchors` replaces starts with `present ∧ ¬ previous present` and ends with
`present ∧ next ¬present`. `lowerCore_agrees` relates the result to independent
initializer equations for all four clocks, assuming the root remains live. The
RHS stays in its original resolved frame. The result covers arbitrary partial
observations; a finite implementation still needs a certified observation adapter.

## Verification boundary

[`PastExamples.lean`](../Clafer/Behavioral/PastExamples.lean) checks all six initial
boundaries, history before child birth, parent gaps and rebirth, and the strict
initializer-domain distinction. It also gives a one-state lasso whose existing
predecessor-bearing clock is equal at times one and two while two nested previous
operators differ. The [finite evaluator](behavioral-verification.md) therefore uses a composed
machine state containing the necessary history. `Core.machine_agrees` proves
equality with infinite meaning at every absolute time. Future search detects
repetition of the complete state, and quantifiers/lets retain captured values.
The certified cardinality bound supplies termination fuel; the evaluator inspects
each reachable state before recursing, so it does not allocate a continuation
chain proportional to that potentially enormous bound.
`PastIntegrationExamples` checks this distinction through mixed operators,
parent gaps, captures, partial observations and guarded initializer lowering.

`Formula` retains all six operators. Both signs normalize before lifetime
guards are inserted; negative previous becomes weak previous, once/historically
and since/triggered are signed dual pairs. Completion independence and strict
partial checking extend to every constructor. Previous demands its operand only
at an available predecessor; other past operators demand every operand throughout
the active history, including now, regardless of an earlier truth witness.
`Core` needs only ordinary previous and since, with classical derived forms.

Opaque observations remain subject to all-time finite agreement. A temporal RHS
condition whose truth differs at equal base clocks cannot be supplied as an
unproved clock-only atom; clients must expose its temporal syntax or provide a
separately justified finite representation.
