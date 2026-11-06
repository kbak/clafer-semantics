module

public import Mathlib.CategoryTheory.Category.Quiv

/-!
# Signatures for diagram predicates

Published SoSyM article, Appendix 2, Definitions 6–7 (PDF p.31).
Legacy subsection aliases such as B.4 follow docs/sources.md.
A graph is Mathlib's `Quiv`, whose arrows form a `Quiver`. There are no
identity/composition operations on carrier arrows. The paper's total edge set
is represented by `Σ x y : G, (x ⟶ y)`; the two projections give its endpoints.
-/

@[expose] public section

universe s va ua

namespace DPGraph

-- [impl->req~dpgraph-core~1]
/-- A symbol type with a graph-valued arity (SoSyM B.4, Definition 7).
No dependencies or inference-closure axioms are part of this signature. -/
structure Signature where
  Symbol : Type s
  arity : Symbol → CategoryTheory.Quiv.{va, ua}

end DPGraph
