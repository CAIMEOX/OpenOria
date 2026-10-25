module

import Oria.Datapack
import Oria.Proofs.Fixtures.FailureRuntime

open Oria.Proofs.Fixtures.FailureRuntime

public def main (args : List String) : IO Unit := do
  match args with
  | [destination] => specimen.artifact.writeTo destination
  | [destination, "unready"] => unready.artifact.writeTo destination
  | [destination, "zero"] => allStack.artifact.writeTo destination
  | [] =>
      for artifact in [specimen.artifact, allStack.artifact, unready.artifact] do
        IO.FS.withTempDir fun root => do
          artifact.writeTo (root / "pack")
          for file in artifact.files do
            unless (← IO.FS.readFile (root / "pack" / file.path)) == file.contents do
              throw (.userError s!"failure artifact differs: {file.path}")
  | _ => throw (.userError "usage: lake exe failure-artifact-test [empty-directory [zero|unready]]")
