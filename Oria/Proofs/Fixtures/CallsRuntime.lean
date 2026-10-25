module

public import Oria.Examples.Calls
public import Oria.Datapack
meta import Oria.Examples.Calls
meta import Oria.Datapack

namespace Oria.Proofs.Fixtures.CallsRuntime

open Oria Oria.Std Oria.Datapack

private def points : Command.Objective := "calls_test.oria"

@[mcfunction]
private def run : Prog (Grade.handled ⟨Req.none, Eff.scoreboardWrite⟩) Unit := do
  let value ← Examples.Calls.chain3.call 4
  (Scoreboard.set (.named "#chain") points value).ignore
  let value ← Examples.Calls.chain7.call 4
  (Scoreboard.set (.named "#long") points value).ignore
  let value ← Examples.Calls.tree.call 4
  (Scoreboard.set (.named "#tree") points value).ignore
  let value ← Examples.Calls.sum24.call 1 2 3 4 5 6 7 8 9 10 11 12
    13 14 15 16 17 18 19 20 21 22 23 24
  (Scoreboard.set (.named "#params") points value).ignore
  let value ← Examples.Calls.locals.call 4
  (Scoreboard.set (.named "#locals") points value).ignore
  let value ← Examples.Calls.choose.call (-4)
  (Scoreboard.set (.named "#negative") points value).ignore
  let value ← Examples.Calls.choose.call 4
  (Scoreboard.set (.named "#positive") points value).ignore

@[datapack]
public def specimen : Spec := build {ns := "calls_test", registerBudget := 128} do
  entry "run" run.ref

@[datapack]
public def limited : Spec := build {ns := "calls_low", registerBudget := 8} do
  entry "run" run.ref

@[datapack]
public def allStack : Spec := build {ns := "calls_zero", registerBudget := 6} do
  entry "run" run.ref

end Oria.Proofs.Fixtures.CallsRuntime
