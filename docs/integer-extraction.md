# Integer operands from navigation

The typed core uses `Expr.integerOf` to turn a unary collection at an explicitly
annotated integer vertex into an integer expression. `Support.Resolved.integers`
checks that the vertex's resolved declaration ID has primitive integer origin.
Names do not determine primitive types. A reference object must first be
navigated through its dereference map. Existing explicit inheritance widening
and lexical contexts are retained.

The [requirements](spec.md#integer-extraction-from-primitive-navigation) define
this extension separately from the original typing/support promises. Its source
correspondence is recorded in the [source map](sources.md#integer-extraction-and-appendix-f-version-operands).
[Integer realization](../FormalCD/Integer.lean) supplies extraction and its proofs;
the [Clafer binding](../Clafer/Constraints/Integer.lean) adds resolved support and
inclusion obligations.

## Domain and extraction

[`FormalCD.IntegerRealization U`](../FormalCD/Integer.lean) supplies an injective `Int → U` encoding
and a decoder satisfying `decode (encode n) = n`. Its domain is the encoding's
range. `IntegerRealization.objectEquiv` proves correspondence with all mathematical
integers. The decoder may have arbitrary values outside that domain; extraction
never uses them. The examples deliberately set an off-domain decoder value to 99
and prove that such objects are rejected.

For a navigation result set `S`, `Extracts R S n` means exactly
`S = {R.encode n}`. `extract R S = some n` is equivalent to that relation.
Equivalently, extraction is defined iff there exists an object `x` such that
`S = {x}` and `x` belongs to the integer domain. The returned integer is unique.
Empty, multiple-object and wrong-domain results return `none`; no object is
chosen from an invalid result and there is no numeric fallback. This is a
noncomputable semantic function over arbitrary sets, not a finite-search runtime
implementation. Its use of classical choice selects only a proved unique value.

`IntegerBinding` binds the entire support graph to the bounded graph of subsets
and spans. Equal resolved IDs have equal object sets, inclusion edges satisfy
literal inclusion, and annotated integer vertices denote the realization's
complete domain. `widen_subset` proves that every allowed widening preserves
ambient objects. A typed result supplies domain membership but can still be empty
or contain multiple objects. These remain explicit obligations of the [constraint denotation](constraint-denotation.md).

`navigationImage` existentially follows actual span links and returns a set of
ambient target objects. Duplicate links with an equal target contribute one set
element. Link-sensitive multiplicity remains separate: the 1..1 hypotheses count
links and are sufficient to prove singleton object images. This extension does
not interpret every bag operation in the core.

<a id="appendix-f"></a>

## Appendix 6

`VersionNavigation` gives a well-formed resolved fragment containing comp, ECU,
display, version and server reference declarations, and the primitive integer
class. The support retains both inheritance inclusions, both heads and both
dereferences. Its typed expression is `not (displayVersion < serverVersion)`,
expressing the accepted display >= server direction without adding a syntax
operator for >=.

`Model.operands_defined` derives both integer operands' well-definedness for each
display from the actual defaulted 1..1 version/server head bounds, 1..1
dereferences, inheritance inclusions and integer-domain binding. It does not
assume singleton operands or the desired inequality. `comparison_defined` then
shows that the selected partial comparison returns a Boolean; false is a defined
result. `IntegerExamples.comparison_value` evaluates the actual navigation for
arbitrary ECU/display integer versions; greater/equal pass and lower fails.

Figure 21's server has multiplicity 0..1 and its VC formula has a nonempty-server
guard. Appendix 6's server is mandatory and its comparison is unguarded. An empty
server navigation therefore gives `none` in this partial comparison, not vacuous
truth. It cannot arise for a display satisfying the selected Appendix 6 bounds.

These conditional structural-semantic results are consumed by the
[general core denotation](constraint-denotation.md). Its full resolved Appendix 6
inventory includes inherited navigation, `server = parent` and the other c01–c12
bodies, using the [inherited structure contract](inherited-realization.md).
[VersionCompilation](../Clafer/Examples/VersionCompilation.lean) attaches the selected
typed version comparison, compiles/glues it, and derives its navigation hypotheses
from emitted local formulas, with the integer-domain assumption explicit. The
[coverage matrix](representative-models.md) separates that conditional result
from full Appendix 6 satisfaction. The [selected preservation bridge](constraint-preservation.md)
connects compiled diagrams to expression meanings, and the
[complete fixture](telematics.md) proves combined whole-model satisfaction.

No parser, string/Boolean conversion, automatic
coercion insertion or finite-bitwidth arithmetic is supplied. Finite structural
objects in the examples coexist with the full integer domain; they do not bound
arithmetic.
