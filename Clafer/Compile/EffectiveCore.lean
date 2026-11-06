module

public import Clafer.Compile.Basic
public import Clafer.Semantics.EffectiveCore

/-! # Effective erasure of resolved Compile inputs

SoSyM §§6.2.2–5. This adapter projects supplied effective fields; it does not
reconstruct authored/default provenance or change the guarded core domain.
-/

@[expose] public section
namespace Clafer.Semantics.EffectiveCore
open MCS DPGraph.Predicates

-- [impl->req~clafer-effective-core~1]
/-- Projection from the existing resolved Compile input. Only effective fields
are read; this is not an elaborator or a lifting of imported data to an AST. -/
noncomputable def erase {a : AST} (i : Compile.Input a) : EffectiveCore a.entries.length where
  family := Compile.family i
  id := Compile.sourceId a
  group d := (a.at d).declaration.group.effective.range

-- [proof->req~clafer-effective-core~1]
theorem erase_wellFormed {a : AST} (i : Compile.Input a) : (erase i).WellFormed :=
  ⟨Compile.family_wellFormed i, Compile.sourceId_injective i.ast,
    fun _d => (i.ast.valid_bounds _ (List.getElem_mem _)).2⟩

@[simp] theorem erase_shape {a : AST} (i : Compile.Input a) (d : a.Occurrence) :
    ((erase i).family.shape d) = (a.at d).shape := by
  have hp := congrArg Option.isSome (Compile.parent_ids i d)
  have hp' : ((Compile.family i).parent d).isSome = (a.at d).parent.isSome := by
    simpa only [Option.isSome_map] using hp
  change (⟨_, _, _, _⟩ : Shape) = (⟨_, _, _, _⟩ : Shape)
  congr 1
  · exact Compile.reference_kind _ _
end Clafer.Semantics.EffectiveCore
