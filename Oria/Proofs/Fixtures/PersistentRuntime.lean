module

public import Oria
public import Oria.Datapack
import Oria.Std.Manifest
meta import Oria
meta import Oria.Datapack

namespace Oria.Proofs.Fixtures.PersistentRuntime

open Oria Oria.Persistent Oria.Std

private def objective : Command.Objective := "memory.oria"

private def callback : Command.Ref {schema := [], req := Req.none, eff := Eff.world} :=
  ⟨`memory.callback, {parts := [.token "function", .space, .token "oria_test:reentry"]}, none⟩

public structure Pair where
  left : Option Int32
  right : Option Int32
  deriving Oria.Object

public inductive Ring where
  | empty
  | node (value : Int32) (next : Ref Ring)
  deriving Oria.Object

@[root]
private def points : Root Int32 := Root.init (persist 0)

@[root]
private def pair : Root Pair := Root.init do
  let value ← Oria.Option.none (A := Int32)
  let pair ← Pair.Obj.Ctor.mk value value
  persist pair

@[root]
private def saved : Root (Option Pair) := Root.init do
  let value ← Oria.Option.none (A := Pair)
  persist value

@[root]
private def ring : Root (Ref Ring) := Root.init do
  let empty ← Ring.Obj.Ctor.empty
  let value ← persist empty
  Ref.new value

@[mcfunction]
private def sum {r : Region} (value : Val Pair r) : Prog .pure Int32 := do
  match value with
  | .mk (.some a) (.some b) => return a + b
  | _ => return -1

@[mcfunction]
private def wrapped (value : Val (Option Pair)) : Prog .pure Int32 := do
  match value with
  | .some value => sum.call value
  | .none => return -1

@[mcfunction]
private def ringValue {r : Region} (value : Val Ring r) : Prog .pure Int32 := do
  match value with
  | .empty => return -1
  | .node value _ => return value

@[mcfunction]
private def publish (n : Val Int32) : Prog (Grade.handled (allocGrade.seq writeGrade)) Unit := do
  let leaf ← Oria.Option.some n
  let value ← Pair.Obj.Ctor.mk leaf leaf
  let value ← persist value
  pair := value

@[mcfunction]
private def publish41 : Prog (Grade.handled (allocGrade.seq writeGrade)) Unit := publish.call 41

@[mcfunction]
private def publish42 : Prog (Grade.handled (allocGrade.seq writeGrade)) Unit := publish.call 42

@[mcfunction]
private def retainPair : Prog (Grade.handled stateGrade) Unit := do
  let value ← pair
  let wrapper ← Oria.Option.some value
  let wrapper ← persist wrapper
  saved := wrapper

@[mcfunction]
private def releasePair : Prog (Grade.handled (allocGrade.seq writeGrade)) Unit := do
  let empty ← Oria.Option.none (A := Pair)
  let empty ← persist empty
  saved := empty

@[mcfunction]
private def increment : Prog (Grade.handled stateGrade) Unit := do
  let old ← points
  let value ← persist (old + 1)
  points := value

@[mcfunction]
private def makeCycle : Prog (Grade.handled stateGrade) Unit := do
  let cell ← ring
  let node ← Ring.Obj.Ctor.node 73 cell
  let value ← persist node
  Ref.set cell value

@[mcfunction]
private def replaceCycle : Prog (Grade.handled (stateGrade.seq ⟨Req.none, Eff.scoreboardWrite⟩)) Unit := do
  let cell ← ring
  let old ← Ref.get cell
  let node ← Ring.Obj.Ctor.node 88 cell
  let value ← persist node
  Ref.set cell value
  let number ← ringValue.call old
  (Scoreboard.set (.named "#old") objective (.dynamic number)).ignore

@[mcfunction]
private def snapshot : Prog (Grade.handled (readGrade.seq ⟨Req.none, Eff.scoreboardWrite⟩)) Unit := do
  let p ← pair
  let ephemeral ← Oria.Option.some p
  let total ← wrapped.call ephemeral
  (Scoreboard.set (.named "#sum") objective (.dynamic total)).ignore
  let wrapper ← saved
  let total ← wrapped.call wrapper
  (Scoreboard.set (.named "#saved") objective (.dynamic total)).ignore
  let cell ← ring
  let value ← Ref.get cell
  let value ← ringValue.call value
  (Scoreboard.set (.named "#ring") objective (.dynamic value)).ignore
  let count ← points
  (Scoreboard.set (.named "#points") objective (.dynamic count)).ignore

@[mcfunction]
private def reentry := show Prog _ Unit from do
  let leaf ← Oria.Option.some 17
  let value ← Pair.mk leaf leaf
  (Command.emit (callback.call .nil)).ignore
  let n ← sum.call value
  (Scoreboard.set (.named "#survived") objective n).ignore

@[datapack]
public def specimen : Datapack.Spec := Datapack.build {
    ns := "memory", registerBudget := 6,
    commands := some (callback.declaration :: Std.Manifest.commandDeclarations) } do
  Datapack.root "memory:points" points
  Datapack.root "memory:pair" pair
  Datapack.root "memory:saved" saved
  Datapack.root "memory:ring" ring
  Datapack.entry "publish41" publish41.ref
  Datapack.entry "publish42" publish42.ref
  Datapack.entry "retain" retainPair.ref
  Datapack.entry "release" releasePair.ref
  Datapack.entry "increment" increment.ref
  Datapack.entry "cycle" makeCycle.ref
  Datapack.entry "replace-cycle" replaceCycle.ref
  Datapack.entry "snapshot" snapshot.ref
  Datapack.entry "reentry" reentry.ref
  Datapack.collector "gc"

end Oria.Proofs.Fixtures.PersistentRuntime
