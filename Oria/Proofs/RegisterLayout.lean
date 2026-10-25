module

import Oria.Compiler.Lower.DP121.Layout
meta import Oria.Compiler.Lower.DP121.Layout

namespace Oria.Proofs.RegisterLayout

open Oria Oria.Lower.DP121

private def bank := Layout.allocate (Command.Objective.ofString "registers.oria") 2

#guard bank.isOk
#guard bank.toOption.any fun layout =>
  layout.registers.size == 2 && layout.scratch.size == 4 && layout.results.size == 2

end Oria.Proofs.RegisterLayout
