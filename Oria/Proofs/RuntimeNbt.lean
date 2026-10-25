module

import Oria.Proofs.Fixtures.RuntimeNbt
import Oria.IR.DP121.Semantics
import Oria.IR.Representation.Persistent
import Oria.Proofs.DynamicPaths

namespace Oria.Proofs.RuntimeNbt

open Oria Oria.Target.DP121.Semantics Oria.Representation

example (table : Table) (t : Option Nbt.Tag) : table.width (.nbt t) = 1 := rfl

example (s : String) : CodecOption .i32 (some ⟨.string, .string s⟩) = none := rfl

example (s : String) :
    CodecOption (.nativeNbt (t := some .string)) (some ⟨.string, .string s⟩) =
      some (.string s) := by simp [CodecOption]

example (t : Nbt.Tag) : Persistent.PlanTable.canonical (.nbt (some t)) = .nbt none := rfl

private def plans := do
  let table ← Table.build #[]
  Persistent.build table #[.nbt none, .nbt (some .string), .nbt (some .compound)]

#guard match plans with
  | .ok p =>
      p.nodeCount == 1 && (p.scanners.toList.map Persistent.Scanner.code) == [1] &&
      p.lookup? (.nbt (some .string)) == p.lookup? (.nbt none)
  | .error _ => false

end Oria.Proofs.RuntimeNbt
