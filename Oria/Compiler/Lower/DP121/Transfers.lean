module

public import Oria.Compiler.Lower.DP121.Stack

namespace Oria.Lower.DP121.Transfers

open Oria.Target.DP121

/-- Forward an immediately stored I32 directly from its still-live score.
Only unconditional compiler transfers participate; calls and native commands end the window. -/
public def run : List (Command .plain) → List (Command .plain)
  | .store .result (.storageI32 p) (.scoreboard (.get x)) ::
      .store .result (.score y) (.data (.get (.static q))) :: rest =>
      let write := Command.store .result (.storageI32 p) (.scoreboard (.get x))
      if p == q then
        write :: (if x == y then run rest else .scoreboard (.operation y .assign x) :: run rest)
      else write :: run (.store .result (.score y) (.data (.get (.static q))) :: rest)
  | command :: rest => command :: run rest
  | [] => []

end Oria.Lower.DP121.Transfers
