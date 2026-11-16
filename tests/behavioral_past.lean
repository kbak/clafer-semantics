import Clafer.Behavioral.FiniteEvaluation

/-!
Small exhaustive regressions compare history machines with an independent
arithmetic-index oracle. Past intervals are evaluated directly from time zero.
The fixed future windows below suffice for these particular depth-two formulas;
exactness for arbitrary mixed formulas is supplied by machine_agrees, not this test.
-/
open Clafer.Behavioral

private def index (states loop t : Nat) : Nat :=
  if t < states then t else loop + (t - loop) % (states - loop)
private def signal (mask i : Nat) : Bool := (mask / 2 ^ i) % 2 == 1
private def previous (a : Nat → Bool) (t : Nat) : Bool := t != 0 && a (t - 1)
private def since (a b : Nat → Bool) (t : Nat) : Bool :=
  (List.range (t + 1)).any fun j => b j &&
    ((List.range (t + 1)).filter (j < ·)).all a

private def sample (last : Nat) (loop : Fin (last + 1)) : Lasso Unit 1 last where
  identities := ⟨0, fun _ => (), fun _ => none⟩
  loop := loop
  live _ _ := true
  deref _ _ _ _ := false
private def observations (last p q : Nat) : FiniteObservation (fun _ => Bool) (fun _ => Empty) 1 last where
  atom a _ s := signal (if a then p else q) s.1.val
  domain d := nomatch d
private def atomP : Core (fun _ => Bool) (fun _ => Empty) 0 := .atom (.source true)
private def atomQ : Core (fun _ => Bool) (fun _ => Empty) 0 := .atom (.source false)

-- [utest->req~behavioral-past-verification~1]
#eval show IO Unit from do
  let mut cases := 0
  for last in [0:3] do
    let states := last + 1
    for loop in List.finRange states do
      for p in [0:2 ^ states] do
        for q in [0:2 ^ states] do
          let L := sample last loop
          let F := observations last p q
          let P := fun t => signal p (index states loop.val t)
          let Q := fun t => signal q (index states loop.val t)
          for t in [0:3 * states + 3] do
            let future := (List.range (2 * states + 3)).map (t + ·)
            let YY := previous (previous P)
            let expected : List (Core (fun _ => Bool) (fun _ => Empty) 0 × Bool) := [
              (.previous atomP, previous P t),
              (.previous (.previous atomP), YY t),
              (.not (.previous (.not atomP)), !previous (fun j => !P j) t),
              (.since .truth atomP, (List.range (t + 1)).any P),
              (.not (.since .truth (.not atomP)), (List.range (t + 1)).all P),
              (.since atomP atomQ, since P Q t),
              (.not (.since (.not atomP) (.not atomQ)), !since (fun j => !P j) (fun j => !Q j) t),
              (.eventually (.previous (.previous atomP)), future.any YY),
              (.always (.previous (.previous atomP)), future.all YY),
              (.eventually (.since atomP atomQ), future.any (since P Q))]
            for (a, wanted) in expected do
              unless a.finite L F (.closed 0) t == wanted do
                throw (IO.userError s!"past mismatch: states={states}, loop={loop.val}, p={p}, q={q}, t={t}")
              cases := cases + 1
  IO.println s!"behavioral past: {cases} exhaustive history checks passed"
