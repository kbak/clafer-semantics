module

public import Clafer.Verification.ImportProofs
public meta import Clafer.Verification.ImportProofs

/-! Internal adapter for canonical JSON emitted by capture.py after strict
external decoding (including duplicate-key rejection). Lean.Json.parse alone
does not enforce that lexical boundary. Parsing and runtime execution are outside
the kernel proof boundary; decoded records pass `Import.admit` before a verdict. -/

@[expose] public section
namespace Clafer.Verification.Import
open Lean

def strictKeys (j : Json) (keys : List String) : Except String Unit := do
  let obj ← j.getObj?
  let actual := obj.toList.map Prod.fst
  if actual.length = keys.length ∧ actual.all (· ∈ keys) then pure ()
  else .error "unexpected_fields"

def response (status : String) (code : String := "") : Json :=
  Json.mkObj [("status", toJson status), ("code", toJson code)]

/-- Diagnostic names evaluate the existing checker conjuncts. They are not a
second satisfaction definition or a per-verdict proof certificate. -/
def failedPredicates {n : Nat} (m : Semantics.EffectiveCore n) (c : Candidate n) : List String :=
  ([ ("typed", decide ((realize c).Typed m)),
     ("rooted", decide ((realize c).Rooted m)),
     ("inherits", decide ((realize c).Inherits m)),
     ("declaration_disjoint", decide ((realize c).DeclarationDisjoint m)),
     ("abstracts", decide ((realize c).Abstracts m)),
     ("parents", decide ((realize c).Parents m)),
     ("references", decide ((realize c).References m)),
     ("keys", decide ((realize c).Keys m)),
     ("multiplicities", decide (multiplicityChecks m c)),
     ("groups", decide (groupChecks m c)) ] : List (String × Bool)).filterMap
       (fun (name, passed) => if passed then none else some name)

-- [impl->req~clafer-bounded-comparison~1]
def execute (json : Json) : Except String Json := do
  strictKeys json ["schema", "declarations", "candidate"]
  let schema ← json.getObjValAs? String "schema"
  if schema != "clafer-import/1" then return response "unsupported" "version"
  let declarations ← json.getObjValAs? (Array Json) "declarations"
  for row in declarations do
    strictKeys row ["uid", "name", "parent", "abstract", "super", "mode", "target",
      "card", "group", "parentRank", "superRank", "unused"]
  let r : Input := ⟨← json.getObjValAs? (List Row) "declarations"⟩
  match admit r with
  | .error .unsupportedOrInvalidCertificate => return response "unsupported" "fragment_or_certificate"
  | .error e => return response "malformed" (reprStr e)
  | .ok _ =>
    let candidate ← json.getObjVal? "candidate"
    if let .null := candidate then return response "admitted"
    strictKeys candidate ["objects", "root", "members", "containment", "references"]
    let c : UidCandidate ← fromJson? candidate
    let c ← c.translate r
    match verify r.normalize c with
    | .malformed error => return response "malformed" (reprStr error)
    | .satisfies => return response "satisfies"
    | .violates =>
      if h : c.root ∈ c.objects then
        return Json.mkObj [("status", toJson "violates"), ("code", toJson ""),
          ("failed_predicates", toJson (failedPredicates r.normalize (c.decode r.normalize h)))]
      else return response "error" "violation_missing_root"

end Clafer.Verification.Import

-- [impl->req~clafer-resolved-import~1]
public def main (args : List String) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let evaluate (input : String) :=
    let output := do
      let json ← Lean.Json.parse input
      Clafer.Verification.Import.execute json
    match output with
    | .ok value => value
    | .error error => Clafer.Verification.Import.response "malformed" error
  if args == ["--stream"] then
    stdout.putStrLn (Lean.Json.mkObj [("schema", Lean.toJson "clafer-checker-stream/1"),
      ("lean", Lean.toJson Lean.versionString), ("limit", Lean.toJson (1000000 : Nat)),
      ("executable", Lean.toJson (← IO.appPath).toString)]).compress
    stdout.flush
    -- A bounded loop keeps the entrypoint total; each line independently calls
    -- the unchanged admission/translation/checker boundary.
    for sequence in [:1000000] do
      let input ← stdin.getLine
      if input.isEmpty then break
      stdout.putStrLn (Lean.Json.mkObj [("sequence", Lean.toJson sequence),
        ("verdict", evaluate input)]).compress
      stdout.flush
  else
    stdout.putStrLn (evaluate (← stdin.readToEnd)).compress
