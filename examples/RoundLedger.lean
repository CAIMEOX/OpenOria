module

import Oria.Examples.RoundLedger

public def main (args : List String) : IO Unit := do
  match args with
  | [destination] => Oria.Examples.RoundLedger.specimen.artifact.writeTo destination
  | [destination, "--stack"] => Oria.Examples.RoundLedger.stacked.artifact.writeTo destination
  | _ => throw (.userError "usage: lake exe oria-ledger <empty-directory> [--stack]")
