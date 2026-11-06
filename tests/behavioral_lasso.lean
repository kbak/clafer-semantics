import Clafer.Behavioral.Verification

/-!
Exhaustively compare the actual evaluator with an independent arithmetic-index
oracle on all one-, two- and three-state lassos and all pairs of Boolean signals.
The oracle uses a whole suffix prefix/cycle, not the implementation's expanded
clock or finite-orbit functions. Dedicated examples additionally prove semantics
on valid structural candidates and exercise admission mutations.
-/

open Clafer.Behavioral

private def index (states loop t : Nat) : Nat :=
  if t < states then t else loop + (t - loop) % (states - loop)

private def signal (mask i : Nat) : Bool := (mask / 2 ^ i) % 2 == 1

private def sample (last : Nat) (loop : Fin (last + 1)) (p : Nat) : Lasso Unit 2 last where
  identities := ⟨0, fun _ => (), fun x => if x = 0 then none else some 0⟩
  loop := loop
  live i x := x == 0 || signal p i.val
  deref _ _ _ _ := false

private def observations (last p q : Nat) : FiniteObservation (fun _ => Bool) (fun _ => Unit) 2 last where
  atom a _ s := signal (if a then p else q) s.1.val
  domain _ _ _ := ∅

private def atomP : Core (fun _ => Bool) (fun _ => Unit) 0 := .atom (.source true)
private def atomQ : Core (fun _ => Bool) (fun _ => Unit) 0 := .atom (.source false)

-- [utest->req~behavioral-lassos~1]
-- [utest->req~behavioral-finite-checker~1]
#eval show IO Unit from do
  let mut cases := 0
  for last in [0:3] do
    let states := last + 1
    for loop in List.finRange states do
      for p in [0:2 ^ states] do
        for q in [0:2 ^ states] do
          let L := sample last loop p
          let F := observations last p q
          for t in [0:2 * states + 1] do
            let P := fun k => signal p (index states loop.val (t + k))
            let Q := fun k => signal q (index states loop.val (t + k))
            let offsets := List.range states
            let eventuallyP := offsets.any P
            let alwaysP := offsets.all P
            let untilPQ := offsets.any (fun k => Q k && (List.range k).all P)
            let eval := fun a => Core.finite L F a (.closed 1) (L.clock t)
            let expected : List (Core (fun _ => Bool) (fun _ => Unit) 0 × Bool) := [
              (.next atomP, P 1),
              (.eventually atomP, eventuallyP),
              (.always atomP, alwaysP),
              (.strongUntil atomP atomQ, untilPQ),
              (.weakUntil atomP atomQ, alwaysP || untilPQ),
              (.not (.eventually atomP), !eventuallyP),
              (.always (.eventually atomP), offsets.all (fun i => offsets.any (fun j => P (i + j)))),
              (.eventually (.always atomP), offsets.any (fun i => offsets.all (fun j => P (i + j)))),
              (.atom .starts, P 0 && (t == 0 || !signal p (index states loop.val (t - 1)))),
              (.atom .ends, P 0 && !P 1)]
            unless (L.clock t).1.val == index states loop.val t do
              throw (IO.userError s!"clock mismatch: {states}, {loop.val}, {t}")
            for (formula, wanted) in expected do
              unless eval formula == wanted do
                throw (IO.userError s!"temporal mismatch: states={states}, loop={loop.val}, p={p}, q={q}, t={t}")
              cases := cases + 1
    unless (Lasso.loopIndex states states).isNone && (Lasso.loopIndex 0 0).isNone do
      throw (IO.userError "invalid loop admitted")
  unless cases == 15160 do
    throw (IO.userError s!"unexpected exhaustive check count: {cases}")
  IO.println s!"behavioral lasso: {cases} exhaustive temporal checks passed"
