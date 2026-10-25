module

import Oria
import Oria.Datapack
meta import Oria
meta import Oria.Datapack

open Oria Oria.Std Oria.Datapack

private def choice : Command.Objective := "input.choice"
private def playerGrade := (Scoreboard.enableGrade .self).seq (Tellraw.grade .self)

@[mcfunction]
private def setup : Prog Scoreboard.objectiveGrade.handled Unit :=
  (Scoreboard.Objectives.add choice .trigger).ignore

@[mcfunction]
private def receive : Prog playerGrade Int32 := do
  (Scoreboard.enable .self choice).ignore
  let n ← Scoreboard.get .self choice
  if n == 0 then return 0
  else
    Scoreboard.set .self choice (.static 0)
    Tellraw.number .self (.dynamic n)

@[mcfunction]
private def tick : Prog ⟨Req.none, playerGrade.handled.eff⟩ Unit := do
  Execute.forEach [.as .allPlayers] do
    receive.call

@[datapack]
private def inputs : Spec := build { ns := "input", description := "Oria player trigger input" } do
  onLoad setup.ref
  onTick tick.ref

public def main (args : List String) : IO Unit := do
  let [destination] := args
    | throw (.userError "usage: lake exe oria-trigger <empty-directory>")
  inputs.artifact.writeTo destination
