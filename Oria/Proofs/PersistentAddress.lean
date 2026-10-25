module

import Oria.Compiler.Lower.DP121.Heap
meta import Oria.Compiler.Lower.DP121.Heap
import Oria.IR.DP121.Pretty
import Oria.IR.DP121.Semantics
meta import Oria.IR.DP121.Semantics
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.PersistentAddress

open Oria Oria.Target.DP121

private def base : StoragePath := ⟨.ofString "memory:runtime", .key "memo"⟩
private def schema := Lower.DP121.Heap.addressSchema

private def key : DataPath (.macro schema) :=
  .key base ⟨0, by simp [schema]⟩ [] (by simp [schema])

private def arguments (value : Int32) : Semantics.MacroEnv schema := by
  simp only [Semantics.MacroEnv, schema, Lower.DP121.Heap.addressSchema, MacroSchema.fields_ofFields]
  exact .cons value .nil

example : key.parameterCount = 1 := rfl

#guard ([(-3 : Int32), 0, 42].all fun value =>
  Semantics.dataPath (mode := .macro schema) (arguments value) key ==
    ⟨base.storage, base.path.child (.key ⟨toString value.toInt⟩)⟩)

#guard (Command.data (.get key)).pretty 160 ==
  "data get storage memory:runtime \"memo\".\"$(p0)\""

end Oria.Proofs.PersistentAddress
