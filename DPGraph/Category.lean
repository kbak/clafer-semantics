module

public import DPGraph.Morphism

/-!
[impl->req~dpgraph-category~1]
[proof->req~dpgraph-category~1]
-/

/-!
# The category of DP-graphs over a fixed signature

SoSyM B.4, Definitions 9–10. Objects in each category have fixed carrier
universes. The existing `Hom` also supports maps between different universes.
This category gives no identity or composition operations to carrier arrows.
-/

@[expose] public section

universe s va ua v u

namespace DPGraph

/-- The category operations are exactly the declaration-preserving maps and
operations of Definition 10. Extensionality is `Hom.ext` / `Hom.ext_of_obj_map`. -/
instance category (σ : Signature.{s, va, ua}) :
    CategoryTheory.Category (DPGraph.{s, va, ua, v, u} σ) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

end DPGraph
