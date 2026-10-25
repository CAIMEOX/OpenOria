module

public import Oria
public import Oria.Datapack
public import Oria.Proofs.Fixtures.Memory
import Oria.Nbt.Deriving
meta import Oria
meta import Oria.Datapack
meta import Oria.Proofs.Fixtures.Memory
meta import Oria.Nbt.Deriving

namespace Oria.Proofs.TypedNbt

open Oria

@[root]
private def saved : Persistent.Root (Nbt.Data none) := Persistent.Root.init do
  let empty ← Nbt.literal (nbt% [])
  let empty ← Nbt.forget empty
  Persistent.persist empty

structure Item where
  name : String
  score : Int32
  deriving Nbt.Repr

public structure State where
  input : Array Int32
  output : Array Int32
  deriving Nbt.Repr

inductive Color where
  | red | green | blue
  deriving Nbt.Repr

structure Box (a : Type) where
  value : a
  deriving Nbt.Repr

structure Nested where
  item : Item
  colors : List Color
  optional : Option Int32
  deriving Nbt.Repr

structure Extended extends Item where
  enabled : Bool
  deriving Nbt.Repr

structure NativeFields where
  counter : Int64
  samples : Nbt.Value .intArray
  deriving Nbt.Repr

inductive Event where
  | idle
  | done (value : Int32)
  deriving Nbt.Repr

example (x : Item) : Nbt.FromNbt.fromNbt (Nbt.ToNbt.toNbt x) = Except.ok x :=
  Nbt.Repr.roundTrip x

/-!
Mutable native documents belong to the invocation even when nested in ordinary data.
-/
/-- error: Oria.Diagnostic.mutableNbtPersistence -/
#guard_msgs in
@[mcfunction]
private def rejected (v : Val (Option (Nbt.Ref State))) :
    Prog Persistent.allocGrade (Option (Nbt.Ref State)) .persistent := Persistent.persist v

@[mcfunction]
private def increment (s : Val (Nbt.Ref State)) := show Prog _ Unit from do
  let x ← Nbt.readI32 s (State.Nbt.input.at (0 : Val Int32))
  Nbt.set s (State.Nbt.input.at (0 : Val Int32)) (.i32 (x + 1))

@[mcfunction]
private def tryWrite (s : Val (Nbt.Ref State)) (i n : Val Int32) := show Prog _ Bool from do
  (Nbt.set s (State.Nbt.input.at i) (.i32 n)).isSuccess

@[mcfunction]
private def run := show Prog _ Unit from do
  let s ← Nbt.alloc (State.mk #[] #[])
  Nbt.append s State.Nbt.input (.i32 7)
  let x ← Nbt.readI32 s (State.Nbt.input.at (0 : Val Int32))
  let unchanged ← tryWrite.call s 0 x
  if unchanged then Prog.fail
  increment.call s
  Nbt.copy s State.Nbt.output s State.Nbt.input
  let copied ← (Nbt.copy s State.Nbt.output s State.Nbt.input).isSuccess
  if copied then Prog.fail
  Nbt.clear s State.Nbt.input
  let cleared ← (Nbt.clear s State.Nbt.input).isSuccess
  if cleared then Prog.fail
  let n ← Nbt.length s State.Nbt.input
  if n != 0 then Prog.fail
  Nbt.store s State.Nbt.output (.storage "typed_nbt:result") (.key "values")
  let exported ← (Nbt.store s State.Nbt.output (.storage "typed_nbt:result") (.key "values")).isSuccess
  if exported then Prog.fail
  let snapshot ← Nbt.snapshot s State.Nbt.output
  let frozen ← Persistent.persist snapshot
  saved := frozen
  Nbt.set s (State.Nbt.output.at (0 : Val Int32)) (.i32 99)
  let old ← Nbt.numberAt snapshot ⟨.index (0 : Oria.Std.Command.Arg.Scalar), []⟩
  if old != 8 then Prog.fail
  let nested ← Nbt.alloc (Nested.mk (Item.mk "Ada" 5) [Color.red, Color.blue] (some 3))
  Nbt.set nested (Nested.Nbt.item.then Item.Nbt.score) (.i32 41)
  Nbt.store nested Nbt.Access.root (.storage "typed_nbt:result") (.key "nested")
  let native ← Nbt.literal (nbt% [17, 23])
  let saved ← Persistent.persist native
  let number ← Nbt.numberAt saved ⟨.index (1 : Oria.Std.Command.Arg.Scalar), []⟩
  Nbt.set s (State.Nbt.output.at (0 : Val Int32)) (.i32 number)
  Nbt.store s (State.Nbt.output.at (0 : Val Int32)) (.storage "typed_nbt:result") (.key "persistentRead")
  let written ← (Nbt.set s (State.Nbt.input.at (99 : Val Int32)) (.i32 42)).isSuccess
  if written then Prog.fail
  else Nbt.store s State.Nbt.input (.storage "typed_nbt:result") (.key "empty")

@[mcfunction]
private def restore := show Prog _ Unit from do
  let snapshot ← saved
  (Oria.Std.Data.write (.storage "typed_nbt:result") (.key "snapshot") snapshot).discard

@[datapack]
public def specimen : Datapack.Spec := Datapack.build {ns := "typed_nbt"} do
  Datapack.root "typed_nbt:saved" saved
  Datapack.collector "gc"
  Datapack.entry "run" run.ref
  Datapack.entry "restore" restore.ref
  Fixtures.Memory.entries

@[datapack]
public def allStack : Datapack.Spec := Datapack.build {ns := "typed_nbt_stack", registerBudget := 6} do
  Fixtures.Memory.entries

end Oria.Proofs.TypedNbt
