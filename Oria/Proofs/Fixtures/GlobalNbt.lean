module

public import Oria.Examples.GlobalNbt
meta import Oria
meta import Oria.Datapack
meta import Oria.Examples.GlobalNbt

namespace Oria.Proofs.Fixtures.GlobalNbt

open Oria Oria.Std
open Oria.Examples.GlobalNbt (State)

public def state : Nbt.Global State :=
  Nbt.Global.init "state" (.key "buffer") ⟨0, #[10, 20], "initial"⟩
public def neighbor : Nbt.Global State :=
  Nbt.Global.init "state" (.key "neighbor") ⟨100, #[30], "neighbor"⟩

private def increment (g : Nbt.Global State) := show Prog _ Unit from do
  let n ← g.count
  g.count := n + 1

private def exercise (g other : Nbt.Global State) := show Prog _ Unit from do
  let n ← g.count
  if n != 2 then Prog.fail
  let old ← Nbt.snapshot g State.Nbt.values
  let tmp ← Nbt.alloc (State.mk 0 #[] "scratch")
  Nbt.copy tmp Nbt.Access.root g Nbt.Access.root
  tmp.values[0] := 41
  let original ← g.values[0]
  if original != 10 then Prog.fail
  Nbt.copy g State.Nbt.values tmp State.Nbt.values
  let copied ← g.values[0]
  if copied != 41 then Prog.fail
  let snapshot ← Nbt.numberAt old ⟨.index (.static 0), []⟩
  if snapshot != 10 then Prog.fail
  Nbt.appendFrom g State.Nbt.values tmp (State.Nbt.values.at (0 : Val Int32))
  let len ← Nbt.length g State.Nbt.values
  if len != 3 then Prog.fail
  let alias := g
  alias.values[-1] := 42
  let aliased ← g.values[-1]
  if aliased != 42 then Prog.fail
  g.label := "updated"
  let unchanged ← (Nbt.set g State.Nbt.label (.literal "updated")).isSuccess
  if unchanged then Prog.fail
  let bad ← (Nbt.set g (State.Nbt.values.at (99 : Val Int32)) (.i32 0)).isSuccess
  if bad then Prog.fail
  let before ← other.count
  g := State.mk 9 #[7, 8] "replaced"
  let after ← other.count
  if after != before then Prog.fail
  let current ← g.values[0]
  if current != 7 then Prog.fail
  Nbt.copy g (State.Nbt.values.at (0 : Val Int32)) g (State.Nbt.values.at (1 : Val Int32))
  let copied ← g.values[0]
  if copied != 8 then Prog.fail

private def foreignWrite (storage : ResourceId) (g : Nbt.Global State) := show Prog _ Unit from do
  let _before ← g.count
  Data.modify (.storage storage) ((Nbt.Path.key "buffer").field "count") .set (.ofNbt (77 : Int32))
  let after ← g.count
  if after != 77 then Prog.fail

private def repair (storage : ResourceId) (g other : Nbt.Global State) := show Prog _ Unit from do
  Data.remove (.storage storage) ((Nbt.Path.key "buffer").field "count")
  let missing ← (Nbt.readI32 g State.Nbt.count).isSuccess
  if missing then Prog.fail
  g.count := 77
  Data.modify (.storage storage) ((Nbt.Path.key "buffer").field "count") .set (.ofNbt "text")
  let numeric ← (show Prog _ Unit from do
    (Nbt.snapshot g State.Nbt.count).discard
    (Nbt.readI32 g State.Nbt.count).discard).isSuccess
  if numeric then Prog.fail
  g.count := 77
  Data.remove (.storage storage) ((Nbt.Path.key "buffer").field "label")
  g.label := "recreated"
  Data.remove (.storage storage) ((Nbt.Path.key "buffer").field "values")
  Nbt.clear g State.Nbt.values
  let n ← Nbt.length g State.Nbt.values
  if n != 0 then Prog.fail
  Data.remove (.storage storage) ((Nbt.Path.key "buffer").field "values")
  Nbt.copy g State.Nbt.values other State.Nbt.values
  let value ← g.values[0]
  if value != 30 then Prog.fail

private def task (g : Nbt.Global State) := show Prog _ Unit from do
  let before ← g.count
  Task.yield
  let after ← g.count
  if after != before + 10 then Prog.fail
  g.count := after + 1

private def interfere (g : Nbt.Global State) := show Prog _ Unit from do
  let n ← g.count
  g.count := n + 10

@[mcfunction] private def inc := increment state
@[mcfunction] private def run := exercise state neighbor
@[mcfunction] private def foreign := foreignWrite "global_test:state" state
@[mcfunction] private def work := task state
@[mcfunction] private def update := interfere state
@[mcfunction] private def foreignStack := foreignWrite "global_stack:state" state
@[mcfunction] private def repairNative := repair "global_test:state" state neighbor
@[mcfunction] private def repairStack := repair "global_stack:state" state neighbor

private def pack {g h : Grade} (settings : Datapack.Settings)
    (foreign : IR.DeclRef ⟨[], .unit, g⟩)
    (repair : IR.DeclRef ⟨[], .unit, h⟩) : Datapack.Spec := Datapack.build settings do
  Datapack.global state
  Datapack.global neighbor
  Datapack.entry "increment" inc.ref
  Datapack.entry "exercise" run.ref
  Datapack.entry "foreign" foreign
  Datapack.entry "repair" repair
  Datapack.entry "interfere" update.ref
  Datapack.task "work" work.ref

@[datapack]
public def specimen : Datapack.Spec := pack {ns := "global_test", sliceBudget := 2000} foreign.ref repairNative.ref

@[datapack]
public def allStack : Datapack.Spec :=
  pack {ns := "global_stack", registerBudget := 6, sliceBudget := 2000} foreignStack.ref repairStack.ref

@[datapack]
public def scalar : Datapack.Spec := Datapack.build {ns := "global_test"} do
  Datapack.global state
  Datapack.entry "increment" inc.ref

@[datapack]
public def relocated : Datapack.Spec :=
  { scalar with settings := { scalar.settings with ns := "global_renamed" } }

@[root]
private def saved : Persistent.Root Nbt.Data := Persistent.Root.init do
  let initial ← Nbt.literal (.int 0)
  let value ← Nbt.forget initial
  Persistent.persist value

@[mcfunction]
private def save := show Prog _ Unit from do
  state.count := 23
  let snapshot ← Nbt.snapshot state State.Nbt.count
  let value ← Persistent.persist snapshot
  saved := value
  state.count := 24

@[mcfunction]
private def inspectSaved := show Prog _ Unit from do
  let snapshot ← saved
  let n ← Nbt.toI32 snapshot
  let current ← state.count
  if n != 23 || current != 24 then Prog.fail

@[datapack]
public def managed : Datapack.Spec := Datapack.build {ns := "global_managed", registerBudget := 6} do
  Datapack.global state
  Datapack.root "global_managed:saved" saved
  Datapack.entry "save" save.ref
  Datapack.entry "inspect" inspectSaved.ref
  Datapack.collector "gc"

end Oria.Proofs.Fixtures.GlobalNbt
