module

import Oria.Compiler.Lower.DP121.Heap
import Oria.Compiler.Lower.DP121.Stack
import Oria.IR.DP121.Pretty
meta import Oria.Compiler.Lower.DP121.Heap
meta import Oria.Compiler.Lower.DP121.Stack
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.MemoryLocations

open Oria Oria.Target.DP121 Oria.Lower.DP121

private def cfg : Heap.Config := ⟨.ofString "heap:runtime", .ofString "heap.oria"⟩
private def cell := Stack.slot cfg.storage .current .locals 0
private def shape : Representation.HeapLayout 1 :=
  ⟨.option .i32, `some, 1, #v[.scalar]⟩
private def code := Heap.allocate cfg shape #v[.loc (.storage cell)] (.storage cell)

#guard code.any fun command => (command.pretty 120).contains
  "set from storage heap:runtime \"stack\"[-1].\"locals\"[0]"

end Oria.Proofs.MemoryLocations
