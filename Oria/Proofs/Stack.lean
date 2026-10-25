module

import Oria.Compiler.Lower.DP121.Stack
import Oria.IR.DP121.Pretty
meta import Oria.Compiler.Lower.DP121.Stack
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.Stack

open Oria Oria.Target.DP121 Oria.Lower.DP121

private def storage : ResourceId := .ofString "stack:runtime"
private def score : Score := ⟨.ofToken (.ofString "#r0"), .ofString "stack.oria"⟩
private def cell := Stack.slot storage .current .locals 3

#guard (Stack.move ⟨.storage cell, .loc (.score score)⟩).pretty 120 ==
  "execute store result storage stack:runtime \"stack\"[-1].\"locals\"[3] int 1 run scoreboard players get #r0 stack.oria"
#guard (Stack.move ⟨.score score, .loc (.storage cell)⟩).pretty 120 ==
  "execute store result score #r0 stack.oria run data get storage stack:runtime \"stack\"[-1].\"locals\"[3]"

end Oria.Proofs.Stack
