module

public import DPGraph.Formula
public import Mathlib.Data.Set.Defs

-- [impl->req~dpgraph-core~1]

/-! # DP-graphs (SoSyM B.4, Definition 9) -/

@[expose] public section

universe s va ua v u

/-- A carrier graph with a set of declared well-typed formulas. Neither the
carrier nor the declarations require finiteness or decidable equality. -/
structure DPGraph (σ : DPGraph.Signature.{s, va, ua}) where
  carrier : CategoryTheory.Quiv.{v, u}
  declarations : Set (DPGraph.Formula σ carrier)

