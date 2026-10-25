module

import Oria.Datapack
import Oria.Proofs.Fixtures.Tasks

open Oria.Proofs.Fixtures.Tasks

public def main (args : List String) : IO Unit := do
  match args with
  | [output] => specimen.artifact.writeTo output
  | [output, "stack"] => spilled.artifact.writeTo output
  | [] =>
      for file in synchronous.artifact.files do
        if file.contents.contains "#task." || file.contents.contains "schedule function" ||
            file.path.toString.contains "/task/" then
          throw (.userError "synchronous program contains task runtime")
      for artifact in [specimen.artifact, spilled.artifact] do
        unless artifact.files.any (·.contents.contains "schedule function") do
          throw (.userError "task wakeup was not emitted")
        unless artifact.files.any (·.contents.contains "scoreboard players remove #task.fuel") do
          throw (.userError "task fuel was not charged")
  | _ => throw (.userError "usage: lake exe task-artifact-test [empty-directory [stack]]")
