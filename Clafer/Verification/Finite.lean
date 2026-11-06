module

public import Clafer.Semantics.Structural
public import DPGraph.Predicates.Finite

/-!
# Finite candidates and structural decision procedure

Finite carriers are local to this boundary. Semantic cardinalities use the
embedding-based A.1 predicates; this executable checker counts finite fibers.
Native evaluation is computation, not a new kernel proof certificate.
-/

@[expose] public section
namespace Clafer.Verification
open Semantics DPGraph.Predicates

/-- Canonical finite object IDs, with an independent membership bit per class.
The reference head is its occurrence identity; target pairs are never deduplicated.
Relations deliberately allow missing and multiple parent/target values. -/
structure Candidate (n : Nat) where
  size : Nat
  root : Fin size
  head : Fin n → Fin size → Bool
  contains : Fin n → Fin size → Fin size → Bool
  deref : Fin n → Fin size → Fin size → Bool

def realize {n : Nat} (c : Candidate n) : Configuration (Fin n) (Fin c.size) where
  root := c.root
  head d := {x | c.head d x = true}
  contains d p x := c.contains d p x = true
  deref d x t := c.deref d x t = true

export DPGraph.Predicates (CountInRange inRange_card)

variable {n : Nat}

def multiplicityChecks (m : EffectiveCore n) (c : Candidate n) : Prop :=
  ∀ d p, m.family.parent d = some p → ∀ x, c.head p x = true →
    CountInRange (m.family.multiplicity d)
      (Fintype.card {y : Fin c.size // c.contains d x y = true})

def groupChecks (m : EffectiveCore n) (c : Candidate n) : Prop :=
  ∀ d, m.family.isAbstract d = false → ∀ p, c.head d p = true →
    CountInRange (m.group d)
      (Fintype.card {x : Fin c.size //
        ∃ e, m.family.parent e = some d ∧ c.contains e p x = true})

def Checks (m : EffectiveCore n) (c : Candidate n) : Prop :=
  (realize c).Typed m ∧ (realize c).Rooted m ∧ (realize c).Inherits m ∧
  (realize c).Abstracts m ∧ (realize c).Parents m ∧ (realize c).References m ∧
  (realize c).Keys m ∧ multiplicityChecks m c ∧ groupChecks m c ∧ (realize c).DeclarationDisjoint m

instance (m : EffectiveCore n) (c : Candidate n) : Decidable ((realize c).Typed m) := by
  unfold Configuration.Typed realize 
  simp only [Set.mem_ofPred_eq]
  infer_instance

instance (m : EffectiveCore n) (c : Candidate n) : Decidable ((realize c).Rooted m) := by
  unfold Configuration.Rooted realize 
  simp only [Set.mem_ofPred_eq]
  infer_instance

instance (m : EffectiveCore n) (c : Candidate n) : Decidable ((realize c).Inherits m) := by
  unfold Configuration.Inherits realize 
  simp only [Set.mem_ofPred_eq]
  infer_instance

instance (m : EffectiveCore n) (c : Candidate n) : Decidable ((realize c).DeclarationDisjoint m) := by
  unfold Configuration.DeclarationDisjoint realize
  simp only [Set.mem_ofPred_eq]
  infer_instance

instance (m : EffectiveCore n) (c : Candidate n) : Decidable ((realize c).Abstracts m) := by
  unfold Configuration.Abstracts realize 
  simp only [Set.mem_ofPred_eq]
  infer_instance

instance (m : EffectiveCore n) (c : Candidate n) : Decidable ((realize c).Parents m) := by
  unfold Configuration.Parents realize ExistsUnique
  simp only [Set.mem_ofPred_eq]
  infer_instance

instance (m : EffectiveCore n) (c : Candidate n) : Decidable ((realize c).References m) := by
  unfold Configuration.References realize ExistsUnique
  simp only [Set.mem_ofPred_eq]
  infer_instance

instance (m : EffectiveCore n) (c : Candidate n) : Decidable ((realize c).Keys m) := by
  unfold Configuration.Keys realize
  infer_instance

instance (m : EffectiveCore n) (c : Candidate n) : Decidable (multiplicityChecks m c) := by
  unfold multiplicityChecks
  infer_instance

instance (m : EffectiveCore n) (c : Candidate n) : Decidable (groupChecks m c) := by
  unfold groupChecks
  infer_instance

instance (m : EffectiveCore n) (c : Candidate n) : Decidable (Checks m c) := by
  unfold Checks
  infer_instance

-- [impl->req~clafer-finite-checker~1]
/-- Terminating finite decision procedure. Core validity and the supported
fragment are explicit hypotheses of the public correctness theorem below. -/
def check (m : EffectiveCore n) (c : Candidate n) : Bool := decide (Checks m c)

theorem checks_iff (m : EffectiveCore n) (c : Candidate n) :
    Checks m c ↔ StructuralSatisfies m (realize c) := by
  unfold Checks StructuralSatisfies
  unfold multiplicityChecks groupChecks Configuration.Multiplicities Configuration.Groups
    Configuration.Child realize
  simp only [inRange_card, Set.mem_ofPred_eq]

-- [proof->req~clafer-finite-checker~1]
/-- The theorem's domain is a valid, supported core and a supplied finite
candidate. Ill-typed candidates are handled by `malformed_rejected` separately;
no caller-supplied equivalence between algorithms and semantics is assumed. -/
theorem check_correct (m : EffectiveCore n) (c : Candidate n)
    (_valid : m.WellFormed) (_supported : m.Supported) :
    check m c = true ↔ StructuralSatisfies m (realize c) := by
  simp only [check, decide_eq_true_eq, checks_iff]

theorem malformed_rejected (m : EffectiveCore n) (c : Candidate n)
    (h : ¬ (realize c).Typed m) : check m c = false := by
  apply Bool.eq_false_iff.mpr
  intro hc
  exact h ((checks_iff m c).mp (of_decide_eq_true hc)).1

end Clafer.Verification
