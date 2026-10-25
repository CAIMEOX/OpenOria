module

public import Oria.Examples.RockPaperScissors
meta import Oria.Examples.RockPaperScissors
meta import Oria
meta import Oria.Datapack

namespace Oria.Proofs.Fixtures.RockPaperScissors

open Oria.Std Oria.Datapack
open Oria.Examples.RockPaperScissors

@[mcfunction]
private def checkJudge : Prog (Scoreboard.enableGrade .self) Int32 := do
  let p ← Scoreboard.get .self "rps.player"
  let c ← Scoreboard.get .self "rps.server"
  let player ← decode.call p
  let computer ← decode.call c
  let outcome ← judge.call player computer
  let code ← (do
    match outcome with
    | .draw => return 0
    | .win => return 1
    | .lose => return -1 : Prog .pure Int32)
  Scoreboard.set .self "rps.result" (.dynamic code)

@[mcfunction]
private def judgeEntry : Prog (Grade.handled (Scoreboard.enableGrade .self)) Unit := checkJudge.call.ignore

public inductive Number where
  | wrap (value : Int32)
  deriving Oria.Object

@[mcfunction]
private def literalCase (x : Val Number) (y : Val Int32) : Prog .pure Int32 := do
  match x, y with
  | .wrap (-2147483648), _ => return 11
  | .wrap (-1), 0 => return 12
  | .wrap 0, y => return y
  | .wrap 2147483647, _ => return 13
  | _, y => return y

@[mcfunction]
private def checkLiterals : Prog (Scoreboard.enableGrade .self) Int32 := do
  let x ← Scoreboard.get .self "rps.player"
  let y ← Scoreboard.get .self "rps.server"
  let value ← Number.wrap x
  let result ← literalCase.call value y
  Scoreboard.set .self "rps.result" (.dynamic result)

@[mcfunction]
private def literalEntry : Prog (Grade.handled (Scoreboard.enableGrade .self)) Unit := checkLiterals.call.ignore

@[mcfunction]
private def fixedPoll : Prog playerGrade Int32 :=
  receive ((do
    let computer ← Choice.scissors
    return computer : Prog .pure Choice).weaken (by decide))

@[mcfunction]
private def fixedTick : Prog (Grade.handled ⟨Req.none, playerGrade.eff⟩) Unit := do
  Execute.forEach [.as .allPlayers] do
    fixedPoll.call

@[mcfunction]
private def failedPoll : Prog playerGrade Int32 :=
  receive (Prog.fail.weaken (by decide))

@[mcfunction]
private def failedTick : Prog (Grade.handled ⟨Req.none, playerGrade.eff⟩) Unit := do
  Execute.forEach [.as .allPlayers] do
    failedPoll.call

@[datapack]
public def specimen : Spec := build { ns := "rpstest", registerBudget := 6 } do
  entry "judge" judgeEntry.ref
  entry "literals" literalEntry.ref
  entry "fixed-tick" fixedTick.ref
  entry "failed-tick" failedTick.ref

end Oria.Proofs.Fixtures.RockPaperScissors
