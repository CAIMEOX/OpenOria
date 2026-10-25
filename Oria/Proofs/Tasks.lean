module

import Oria
public import Oria.Datapack
meta import Oria
meta import Oria.Datapack

namespace Oria.Proofs.Tasks

open Oria Oria.Std Oria.Datapack

@[mcfunction]
private def pause : Prog .suspension Unit := Task.yield

/--
error: datapack `Oria.Proofs.Tasks.synchronousEntry`: Oria.Diagnostic.invalidTask
-/
#guard_msgs(error, substring := true) in
@[datapack]
public def synchronousEntry : Spec := build {ns := "task_bad"} do
  entry "work" pause.ref

/--
error: datapack `Oria.Proofs.Tasks.smallBudget`: Oria.Diagnostic.taskBudgetTooSmall
-/
#guard_msgs(error, substring := true) in
@[datapack]
public def smallBudget : Spec := build {ns := "task_small", sliceBudget := 1} do
  task "work" pause.ref

@[mcfunction]
private def broadcast := show Prog _ Unit from do
  Task.checkpoint
  (Tellraw.text .all "Finished").ignore

/--
error: datapack `Oria.Proofs.Tasks.unknownNative`: Oria.Diagnostic.unboundedTaskRegion
-/
#guard_msgs(error, substring := true) in
@[datapack]
public def unknownNative : Spec := build {ns := "task_unknown"} do
  task "work" broadcast.ref

@[mcfunction]
private def loop : Val Int32 → Prog .pure Int32 :=
  Prog.fix fun again n => do
    if n <= 0 then return 0
    else again (n - 1)

@[mcfunction]
private def uncheckedLoop := show Prog _ Unit from do
  Task.checkpoint
  let n ← loop.call 10
  let _ ← Scoreboard.set (.named "#answer") "task.points" n
  return Val.unit

/--
error: datapack `Oria.Proofs.Tasks.unboundedLoop`: Oria.Diagnostic.unboundedTaskRegion
-/
#guard_msgs(error, substring := true) in
@[datapack]
public def unboundedLoop : Spec := build {ns := "task_loop"} do
  task "work" uncheckedLoop.ref

end Oria.Proofs.Tasks
