module

import Oria.Proofs.Fixtures.GlobalNbt
import Oria.Compiler.Analysis.Memory
import Oria.Compiler.Lower.DP121.Emit
meta import Oria
meta import Oria.Datapack
meta import Oria.Proofs.Fixtures.GlobalNbt

namespace Oria.Proofs.GlobalNbt

open Oria Oria.Proofs.Fixtures.GlobalNbt

/-- error: datapack -/
#guard_msgs(error, substring := true) in
@[datapack]
private def missing : Datapack.Spec :=
  { scalar with globals := #[] }

#guard (Datapack.build {ns := "global_test"} do
  Datapack.global state
  Datapack.global state).check matches .error (.overlappingNbtGlobals _)

private def nested : Nbt.Global Int32 := Nbt.Global.init "state" ((Nbt.Path.key "buffer").field "count") 0
#guard (Datapack.build {ns := "global_test"} do
  Datapack.global state
  Datapack.global nested).check matches .error (.overlappingNbtGlobals _)

#guard (Datapack.build {ns := "global_test"} do
  Datapack.global (Nbt.Global.init "runtime" (.key "owned") (0 : Int32))).check
  matches .error (.reservedNbtGlobal _)

#guard (Datapack.build {ns := "global_test"} do
  Datapack.global (Nbt.Global.init "state" (.key "bad\nkey") (0 : Int32))).check matches .error _

example : ¬IR.Nbt.FieldPath ((Nbt.Path.key "values").at 0) := by decide

#guard !(Datapack.ResourcePath.parse "other:state").isOk

example (config : Lower.DP121.Config) (ns : Datapack.ResourceNamespace) :
    ({ config with resourceNamespace := ns } : Lower.DP121.Config).dataNamespace =
      config.dataNamespace := rfl

example (g : Nbt.Global Int32) (n : Val Int32) :
    (do g := n : Prog IR.Nbt.writeGrade Unit) = Nbt.set g Nbt.Access.root (.i32 n) := rfl

example (g : Nbt.Global Int32) :
    (do let x ← g; return x : Prog IR.Nbt.readGrade Int32) =
    (do let x ← Nbt.readI32 g Nbt.Access.root; return x : Prog IR.Nbt.readGrade Int32) := rfl

example (g : Nbt.Global (Array Int32)) (i n : Val Int32) :
    (do g[i] := n : Prog IR.Nbt.writeGrade Unit) =
    Nbt.set g (Nbt.Access.root.at i) (.i32 n) := rfl

example (g : Nbt.Global (Array Int32)) (i : Val Int32) :
    (do let x ← g[i]; return x : Prog IR.Nbt.readGrade Int32) =
    (do let x ← Nbt.readI32 g (Nbt.Access.root.at i); return x : Prog IR.Nbt.readGrade Int32) := rfl

example {a : Type} [r : Nbt.Repr a] (n : a) :
    @Nbt.FromNbt.fromNbt a r.toFromNbt
      (Nbt.Global.init "state" (.key "count") n).definition.initial = Except.ok n :=
  Nbt.Global.init_decodes _ _ _ _

private def root (path : Nbt.Path) (h : IR.Nbt.FieldPath path) : IR.Nbt.Base [] :=
  .global ⟨"state", path, .atom .int, h⟩

example :
    Analysis.Memory.Location.ofPath (Γ := []) .nil (root (.key "player") (by decide))
      (.ofSegments (.atom .int) [.key ⟨"stats"⟩, .key ⟨"points"⟩]) =
    Analysis.Memory.Location.ofPath (Γ := []) .nil
      (root ((Nbt.Path.key "player").field "stats") (by decide))
      (.ofSegments (.atom .int) [.key ⟨"points"⟩]) := by rfl

end Oria.Proofs.GlobalNbt
