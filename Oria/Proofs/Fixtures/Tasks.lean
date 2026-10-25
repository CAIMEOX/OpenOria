module

public import Oria
public import Oria.Datapack
meta import Oria
meta import Oria.Datapack

namespace Oria.Proofs.Fixtures.Tasks

open Oria Oria.Std Oria.Datapack Oria.Persistent

private def points : Command.Objective := "task.points"
private def grade : Grade :=
  ⟨Req.none, Eff.world ||| Eff.random ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.suspend ||| Eff.failure⟩

public structure Box where
  value : Int32
  deriving Oria.Object

@[value_type]
public structure Pair where
  left : Int32
  right : Int32
  deriving Oria.Object

@[mcfunction]
private def pair (seed : Val Int32) : Prog (Grade.suspension.seq .failure) Pair := do
  if seed < 0 then Prog.fail
  else
    Task.yield
    return {left := seed, right := seed + 1}

@[mcfunction]
private def sum : Val Int32 → Val Int32 → Prog .suspension Int32 :=
  Prog.fix fun again n acc => do
    if n <= 0 then return acc
    else
      Task.checkpoint
      again (n - 1) (acc + n)

@[mcfunction]
private def peek (b : Val Box) : Prog .pure Int32 := return b.value

@[root]
private def result : Root Int32 := Root.init (persist 0)

@[mcfunction]
private def setup := (Scoreboard.Objectives.add points .dummy).ignore

@[mcfunction]
private def accumulate : Val Int32 → Val Int32 → Prog grade Int32 :=
  Prog.fix fun again n acc => do
    if n <= 0 then return acc
    else
      Task.checkpoint
      Scoreboard.add (.one (.named "#effects")) points 1
      let y ← again (n - 1) (acc + 1)
      return y + n

@[mcfunction]
private def middle (n seed : Val Int32) : Prog grade Int32 := do
  let x ← accumulate.call n seed
  return x + seed

@[mcfunction]
private def work := show Prog _ Unit from do
  let seed ← Scoreboard.get (.named "#input") points
  let box ← Box.mk seed
  Task.yield
  let x ← middle.call 40 seed
  let p ← pair.call 10
  Scoreboard.set (.named "#pair") points (p.left + p.right)
  let total ← sum.call 20 0
  Scoreboard.set (.named "#tail") points total
  let other ← Box.mk (seed + 1)
  let old ← peek.call box
  let next ← peek.call other
  Scoreboard.set (.named "#answer") points (x + old + next)
  let saved ← persist (x + old + next)
  result := saved

@[mcfunction]
private def failing : Val Int32 → Prog grade Int32 :=
  Prog.fix fun again n => do
    if n <= 0 then Prog.fail
    else
      Task.checkpoint
      let x ← again (n - 1)
      return x + n

@[mcfunction]
private def recovery := show Prog _ Unit from do
  let x ← (failing.call 15).getD (-7)
  Scoreboard.set (.named "#caught") points x

@[mcfunction]
private def failTask : Prog (Grade.suspension.seq .failure) Unit := do
  Task.yield
  Prog.fail

@[mcfunction]
private def plain := (Scoreboard.set (.named "#plain") points 1).discard

@[mcfunction]
private def pause : Prog .suspension Unit := Task.yield

@[mcfunction]
private def dormant : Prog .suspension Unit := do
  if (0 : Val Int32) == 1 then pause.call
  else return Val.unit

@[mcfunction]
private def clobber := show Prog _ Unit from do
  let x ← Scoreboard.get (.named "#noise") points
  let b ← Box.mk (x + 1000)
  let n ← peek.call b
  Scoreboard.set (.named "#noise") points n

@[mcfunction]
private def snapshot := show Prog _ Unit from do
  let n ← result
  Scoreboard.set (.named "#root") points n

private def entries (id : ResourceId) : Builder Unit := do
  onLoad setup.ref
  root id result
  collector "gc"
  task "start" work.ref
  task "alias" work.ref
  task "recovery" recovery.ref
  task "fail" failTask.ref
  task "plain" plain.ref
  entry "clobber" clobber.ref
  entry "snapshot" snapshot.ref

@[datapack]
public def specimen : Spec := build {ns := "task_test", sliceBudget := 512} (entries "task_test:result")

@[datapack]
public def spilled : Spec := build {ns := "task_stack", registerBudget := 6, sliceBudget := 512} (entries "task_stack:result")

@[datapack]
public def synchronous : Spec := build {ns := "task_sync"} do
  onLoad setup.ref
  entry "plain" plain.ref
  entry "dormant" dormant.ref

end Oria.Proofs.Fixtures.Tasks
