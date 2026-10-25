module

import Oria.Datapack
import Oria.Proofs.Fixtures.ValueTypes

open Oria.Proofs.Fixtures.ValueTypes

public def main (args : List String) : IO Unit := do
  match args with
  | [destination] => specimen.artifact.writeTo destination
  | [destination, "zero"] => allStack.artifact.writeTo destination
  | [] =>
      for file in arithmeticOnly.artifact.files do
        if file.contents.contains "arena append" then
          throw (.userError s!"inline product allocated in {file.path}")
      for artifact in [specimen.artifact, allStack.artifact] do
        IO.FS.withTempDir fun root => do
          artifact.writeTo (root / "pack")
          for file in artifact.files do
            unless (← IO.FS.readFile (root / "pack" / file.path)) == file.contents do
              throw (.userError s!"value-type artifact differs: {file.path}")
  | _ => throw (.userError "usage: lake exe value-types-artifact-test [empty-directory [zero]]")
