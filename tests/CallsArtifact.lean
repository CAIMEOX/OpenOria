module

import Oria.Proofs.Fixtures.CallsRuntime

open Oria.Proofs.Fixtures.CallsRuntime

public def main (args : List String) : IO Unit := do
  match args with
  | [destination] => specimen.artifact.writeTo destination
  | [destination, "two"] => limited.artifact.writeTo destination
  | [destination, "zero"] => allStack.artifact.writeTo destination
  | [] =>
      for artifact in [specimen.artifact, limited.artifact, allStack.artifact] do
        IO.FS.withTempDir fun dir => artifact.writeTo (dir / "pack")
  | _ => throw (.userError "usage: lake exe calls-artifact-test [empty-directory [two|zero]]")
