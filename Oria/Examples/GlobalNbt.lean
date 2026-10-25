module

public import Oria
public import Oria.Datapack
meta import Oria
meta import Oria.Datapack

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Global native documents

The global's storage name and field path are chosen during construction. The datapack supplies
their namespace. Contents survive ordinary entries and matching-schema reloads.
Typed operations work directly on native storage.
-/

namespace Oria.Examples.GlobalNbt

/-- A native document containing numeric data and a host-written string. -/
public structure State where
  /-- Number of successful edits. -/
  count : Int32
  /-- Values addressed by runtime indices. -/
  values : Array Int32
  /-- Last edit label. -/
  label : String
  deriving Nbt.Repr

/-- First-load contents for the owned {lit}`buffer` subtree. -/
public def state : Nbt.Global State :=
  Nbt.Global.init "state" (.key "buffer") ⟨0, #[10, 20], "initial"⟩

/-- Update one element and count the edit. Missing indices leave through Failure. -/
@[mcfunction]
public def edit (i : Val Int32) := show Prog _ Int32 from do
  let n ← state.values[i]
  state.values[i] := n + 1
  let count ← state.count
  state.count := count + 1
  (Nbt.set state State.Nbt.label (.literal "edited")).ignore
  let result ← state.values[i]
  return result

/-- An exported Unit entry edits the first element. -/
@[mcfunction]
public def step := (edit.call 0).discard

/-- Register the native document before exposing its entry. -/
@[datapack]
public def game : Datapack.Spec := Datapack.build {ns := "global_demo"} do
  Datapack.global state
  Datapack.entry "step" step.ref

end Oria.Examples.GlobalNbt
