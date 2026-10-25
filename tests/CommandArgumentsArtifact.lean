module

import Oria.Proofs.Fixtures.CommandArguments

public def main (args : List String) : IO Unit := do
  let [destination] := args
    | throw (.userError "usage: lake exe command-arguments-artifact-test <empty-directory>")
  Oria.Proofs.Fixtures.CommandArguments.specimen.artifact.writeTo destination
