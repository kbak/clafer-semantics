module

public import Clafer.Semantics.Structural

/-!
# Independent effective group meaning

SoSyM §4.2.1, §6.2.2 and Appendix 3, with the accepted D6 rule:
count the union of own and inherited child heads at the same parent object.
The behavioral 0.5.7 profile retains this rule through static S3/S4 and T11.
These definitions do not depend on Compile or on finite verification.
-/

@[expose] public section
namespace Clafer.Semantics.Groups
open MCS DPGraph.Predicates

universe u
variable {C : Type} (f : Family C)

/-- Reflexive super hierarchy, selected from resolved identities. -/
def Ancestor (p s : C) : Prop :=
  Relation.ReflTransGen (fun c s => f.super c = some s) p s

-- [impl->req~clafer-compile-groups~1]
/-- Set union of containment fibers at one actual parent. Distinct bag heads
remain distinct; multiple inherited paths to one head count it only once. -/
def ChildObjects {U : Type u} (s : Configuration C U) (p : C) (x y : U) : Prop :=
  ∃ a, Ancestor f p a ∧ ∃ c, f.parent c = some a ∧ s.contains c x y

def Holds {U : Type u} (s : Configuration C U) (p : C) : Prop :=
  ∀ x : s.head p,
    InRange (f.group p).effective.range {y : U // ChildObjects f s p x.val y}

end Clafer.Semantics.Groups
