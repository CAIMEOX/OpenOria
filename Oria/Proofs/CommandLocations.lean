module

import Oria.Compiler.Lower.DP121.Command
import Oria.IR.DP121.Pretty
meta import Oria.Compiler.Lower.DP121.Command
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.CommandLocations

open Oria Oria.Lower.DP121 Oria.Target.DP121

private def check : Except Diagnostic Bool := do
  let bank ← Layout.allocate (.ofString "command.oria") 0
  let target : Place := .storage (Stack.slot (.ofString "command:runtime") .current .locals 0)
  let captured ← Command.capture bank #v[some target, none]
    ⟨[.scoreboard (.get bank.scratch[0])], []⟩
  pure (captured.commands.length == 3)

#guard check.toOption == some true

end Oria.Proofs.CommandLocations
