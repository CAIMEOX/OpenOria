module

import Oria.Datapack
import Oria.Proofs.Fixtures.RegisterRuntime

open Oria.Proofs.Fixtures.RegisterRuntime

public def main (args : List String) : IO Unit := do
  match args with
  | [destination] => specimen.artifact.writeTo destination
  | [destination, "zero"] => allStack.artifact.writeTo destination
  | [] =>
      for (label, artifact) in [("two", specimen.artifact), ("zero", allStack.artifact)] do
        IO.FS.withTempDir fun root => do
          artifact.writeTo (root / "pack")
          for file in artifact.files do
            let golden := ("tests/golden/registers" : System.FilePath) / label / file.path
            unless (← IO.FS.readFile golden) == file.contents do
              throw (.userError s!"register allocation golden differs: {label}/{file.path}")
  | _ => throw (.userError "usage: lake exe register-artifact-test [empty-directory [zero]]")
