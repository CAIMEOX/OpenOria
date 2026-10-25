module

import Oria.Examples.RockPaperScissors

public def main (args : List String) : IO Unit := do
  let [destination] := args
    | throw (.userError "usage: lake exe oria-rps <empty-directory>")
  Oria.Examples.RockPaperScissors.game.artifact.writeTo destination
