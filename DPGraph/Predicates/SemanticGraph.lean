module

public import DPGraph.Signature
public import DPGraph.Span

/-!
# A bounded semantic graph of sets and mappings

SoSyM §6.1.1 (PDF pp.18–19), A.1/B.1 (PDF pp.28–30), B.4 Definition 6.
Vertices are subsets of one ambient U, so shared objects retain their identity.
For U : Type u and a bound w, links live in Type (max u w), vertices in Type u
and arrows in Type (max u w + 1). This is a quiver, with no category instance
on span arrows and no assertion of an all-universes SetMap.
-/

@[expose] public section

universe u w

namespace DPGraph.Predicates

-- [impl->req~setmap-semantic-graph~1]
/-- Keep the concrete vertex/arrow carriers visible to elaboration of model
environments. This is the same bounded quiver of subsets and spans. -/
abbrev semanticGraph (U : Type u) : CategoryTheory.Quiv.{max u w + 1, u} :=
  @CategoryTheory.Quiv.of (Set U) ⟨fun A B => Span.{u, u, max u w} A B⟩

end DPGraph.Predicates
