module

import Oria.Proofs.Fixtures.RockPaperScissors

public def main (args : List String) : IO Unit := do
  let [destination] := args
    | throw (.userError "usage: lake exe rps-artifact-test <empty-directory>")
  Oria.Proofs.Fixtures.RockPaperScissors.specimen.artifact.writeTo destination
