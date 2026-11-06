module

public import FormalCD
public import Clafer.Shape.Diagram
public import Clafer.MCS.Metamodel
public import Clafer.MCS.Gluing.Origins
public import Clafer.Constraints.IntegerNavigation
public import Clafer.Compile.Basic
public import Clafer.Compile.GroupSemantics
public import Clafer.Compile.Realization
public import Clafer.Compile.ConstraintMeaning
public import Clafer.Semantics.RealizationCompatibility
public import Clafer.Semantics.Abstracts
public import Clafer.Semantics.Reachability
public import Clafer.Verification.Representation
public import Clafer.Verification.ProtocolProofs
public import Clafer.Constraints.CollectionMeaning
public import Clafer.Constraints.DenotationLaws
public import Clafer.Constraints.DenotationInvariance
public import Clafer.Constraints.DenotationSupport
public import Clafer.Constraints.DenotationRenaming
public import Clafer.Constraints.DenotationDefined
public import Clafer.Constraints.Empty

/-!
# Structural 2014 Clafer

Resolved deep syntax, typed core constraints, a binder/context boundary and
individual Shapes over FormalCD and DPGraph, with the Figure 23 MCS structural
disciplines, structural Compile, resolved-referent gluing and verified finite
structural satisfaction for the guarded effective core. The resolved core has independent
partial denotation, explicit model environments and Appendix 6 expansions;
selected predicate preservation connects these meanings to Compile and gluing.
See docs/architecture.md. Acceptance examples are
checked separately.
-/
