module

import Oria.Examples.MergeSort

public def main (args : List String) : IO Unit := do
  match args with
  | [destination] => Oria.Examples.MergeSort.specimen.artifact.writeTo destination
  | [destination, "--stack"] => Oria.Examples.MergeSort.stacked.artifact.writeTo destination
  | _ => throw (.userError "usage: lake exe oria-merge-sort <empty-directory> [--stack]")
