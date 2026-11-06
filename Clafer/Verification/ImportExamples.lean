module

public import Clafer.Verification.ImportProofs

/-! Kernel and native witnesses for the pinned effective import boundary.
The fixtures are typed decoded data; the separate Python suite exercises actual
compiler JSON/capture. SoSyM §5.3 reference occurrences and §5.5 shared identity. -/

@[expose] public section
namespace Clafer.Verification.Import.Examples
open Semantics

def target : Row := ⟨"c0_target", "same", "root", false, none, "basic", none,
  [1, 1], [0, -1], 1, 1, false⟩
def heads (mode : String) : Row := ⟨"c0_heads", "same", "root", false, none,
  mode, some "c0_target", [2, 2], [0, -1], 1, 1, false⟩
def repeated (mode : String) : Input := ⟨[target, heads mode]⟩

def bagAccepted : Accepted (repeated "bag") := ⟨by decide, by decide, by decide⟩
def setAccepted : Accepted (repeated "set") := ⟨by decide, by decide, by decide⟩

def repeatedCandidate : RawCandidate :=
  ⟨[0, 1, 2, 3], 0, [(⟨0⟩, 0), (⟨1⟩, 1), (⟨2⟩, 2), (⟨2⟩, 3)],
   [(⟨1⟩, 0, 1), (⟨2⟩, 0, 2), (⟨2⟩, 0, 3)], [(⟨2⟩, 2, 1), (⟨2⟩, 3, 1)]⟩

theorem repeated_names_separate :
    (repeated "bag").normalize.family.name ⟨1, by decide⟩ =
      (repeated "bag").normalize.family.name ⟨2, by decide⟩ ∧
    (repeated "bag").normalize.id ⟨1, by decide⟩ ≠
      (repeated "bag").normalize.id ⟨2, by decide⟩ := by decide

theorem repeated_bag_satisfies :
    verify (repeated "bag").normalize repeatedCandidate = .satisfies := by decide

theorem repeated_set_violates :
    verify (repeated "set").normalize repeatedCandidate = .violates := by decide

def uidCandidate : UidCandidate :=
  ⟨[0, 1, 2, 3], 0, [("root", 0), ("c0_target", 1), ("c0_heads", 2), ("c0_heads", 3)],
    [("c0_target", 0, 1), ("c0_heads", 0, 2), ("c0_heads", 0, 3)],
    [("c0_heads", 2, 1), ("c0_heads", 3, 1)]⟩

theorem uid_translation_exact : uidCandidate.translate (repeated "bag") = .ok repeatedCandidate := by rfl

theorem repeated_candidate_represented : CandidateRepresents (repeated "bag") uidCandidate repeatedCandidate :=
  translate_represents _ _ _ uid_translation_exact

theorem duplicate_uid_rejected :
    ¬ (Input.mk [target, target]).bindingChecks := by decide

theorem dangling_target_rejected :
    ¬ (Input.mk [heads "bag"]).bindingChecks := by decide

theorem illegal_sentinel_rejected :
    ¬ (Input.mk [{target with card := [0, -2]}]).bindingChecks := by decide

theorem wrong_mode_rejected :
    ¬ (repeated "unknown").bindingChecks := by decide

theorem zero_rank_rejected :
    ¬ coreChecks (Input.mk [{target with parentRank := 0}]).normalize
        (Input.mk [{target with parentRank := 0}]).certificate := by decide

def expect (name : String) (actual : Bool) : IO Unit :=
  unless actual do throw (IO.userError name)

-- [utest->req~clafer-resolved-import~1]
def executableTests : IO Unit := do
  expect "repeated names admitted" (decide (repeated "bag").bindingChecks)
  expect "bag keeps repeated targets" (verify (repeated "bag").normalize repeatedCandidate == .satisfies)
  expect "set rejects repeated targets" (verify (repeated "set").normalize repeatedCandidate == .violates)
  expect "UID rows are preserved" (match uidCandidate.translate (repeated "bag") with
    | .ok c => c == repeatedCandidate | .error _ => false)
  expect "duplicate UID" (!decide (Input.mk [target, target]).bindingChecks)
  expect "dangling target" (!decide (Input.mk [heads "bag"]).bindingChecks)
  expect "invalid sentinel" (!decide (Input.mk [{target with card := [0, -2]}]).bindingChecks)

end Clafer.Verification.Import.Examples
