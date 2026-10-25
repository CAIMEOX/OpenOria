module

import Oria
import Oria.Datapack
meta import Oria
meta import Oria.Datapack

open Oria Oria.Std

@[mcfunction]
private def roll : Prog ((Random.grade none).seq ((Tellraw.grade .self).seq Grade.pure)) Int32 := do
  let n ← Random.value (.between (.static 1) (.static 6))
  Tellraw.number .self (.dynamic n)
  return n

@[mcfunction]
private def play : Prog ((Random.grade none).seq ((Tellraw.grade .self).seq Grade.pure)).handled Unit := roll.call.ignore

@[datapack]
private def dice : Datapack.Spec := Datapack.build {ns := "dice"} do
  Datapack.entry "roll" play.ref

public def main (args : List String) : IO Unit := do
  let [destination] := args
    | throw (.userError "usage: lake exe oria-dice <empty-directory>")
  dice.artifact.writeTo destination
