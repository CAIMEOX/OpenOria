module

public import Oria
public import Oria.Datapack
meta import Oria
meta import Oria.Datapack

namespace Oria.Proofs.Fixtures.ScoreboardRuntime

open Oria.Std Oria.Std.Command.Arg Oria.Datapack

private def points : Command.Objective := "sbtest.oria"
private def choice : Command.Objective := "sbtest.choice"
private def other : Command.Objective := "sbtest.other"
private def temporary : Command.Objective := "sbtest.temporary"
private def input : ScoreHolder := .named "#input"
private def writeGrade := Scoreboard.writeGrade (.named "#status")

private def report (result : Val (Option Int32)) : Prog (Grade.handled writeGrade) Unit := do
  match result with
  | .none =>
    (Scoreboard.set (.named "#status") points (.static 0)).ignore
    (Scoreboard.set (.named "#result") points (.static (-999))).ignore
  | .some n =>
    (Scoreboard.set (.named "#status") points (.static 1)).ignore
    (Scoreboard.set (.named "#result") points (.dynamic n)).ignore

@[mcfunction]
private def setup : Prog (Grade.handled Scoreboard.objectiveGrade) Unit := do
  (Scoreboard.Objectives.add choice .trigger).ignore
  (Scoreboard.Objectives.add other .dummy).ignore

@[mcfunction]
private def addObjective : Prog (Grade.handled Scoreboard.objectiveGrade) Unit := do
  let result : Val (Option Int32) ← Prog.attempt <| Scoreboard.Objectives.add temporary .dummy
  report result

@[mcfunction]
private def duplicate : Prog (Grade.handled Scoreboard.objectiveGrade) Unit := do
  let result : Val (Option Int32) ← Prog.attempt <| Scoreboard.Objectives.add temporary .trigger
  report result

@[mcfunction]
private def removeObjective : Prog (Grade.handled Scoreboard.objectiveGrade) Unit := do
  let result : Val (Option Int32) ← Prog.attempt <| Scoreboard.Objectives.remove temporary
  report result

@[mcfunction]
private def enableInput : Prog (Grade.handled (Scoreboard.enableGrade input)) Unit := do
  let result : Val (Option Int32) ← Prog.attempt <| Scoreboard.enable input choice
  report result

@[mcfunction]
private def enableWrong : Prog (Grade.handled (Scoreboard.enableGrade input)) Unit := do
  let result : Val (Option Int32) ← Prog.attempt <| Scoreboard.enable input other
  report result

@[mcfunction]
private def enableTemporary : Prog (Grade.handled (Scoreboard.enableGrade input)) Unit := do
  let result : Val (Option Int32) ← Prog.attempt <| Scoreboard.enable input temporary
  report result

@[mcfunction]
private def resetInput : Prog (Grade.handled writeGrade) Unit := do
  let result : Val (Option Int32) ← Prog.attempt <| Scoreboard.reset input choice
  report result

@[mcfunction]
private def resetMissing : Prog (Grade.handled writeGrade) Unit := do
  let result : Val (Option Int32) ← Prog.attempt <| Scoreboard.reset input "sbtest.absent"
  report result

@[mcfunction]
private def resetEvery : Prog (Grade.handled writeGrade) Unit := do
  let result : Val (Option Int32) ← Prog.attempt <| Scoreboard.resetAll input
  report result

@[mcfunction]
private def fire : Prog (Grade.handled Trigger.grade) Unit := do
  let result : Val (Option Int32) ← Prog.attempt <| Trigger.run choice
  report result

@[mcfunction]
private def fireSet (n : Val Int32) : Prog (Grade.handled Trigger.grade) Unit := do
  let result : Val (Option Int32) ← Prog.attempt <| Trigger.set choice (.dynamic n)
  report result

@[mcfunction]
private def fireAdd (n : Val Int32) : Prog (Grade.handled Trigger.grade) Unit := do
  let result : Val (Option Int32) ← Prog.attempt <| Trigger.add choice (.dynamic n)
  report result

@[mcfunction]
private def setEntry : Prog (Grade.handled Trigger.grade) Unit := do
  let n : Val (Option Int32) ← Prog.attempt <| Scoreboard.get (.named "#n") points
  match n with
  | .none => report n
  | .some n => fireSet.call n

@[mcfunction]
private def addEntry : Prog (Grade.handled Trigger.grade) Unit := do
  let n : Val (Option Int32) ← Prog.attempt <| Scoreboard.get (.named "#n") points
  match n with
  | .none => report n
  | .some n => fireAdd.call n

@[mcfunction]
private def stopping : Prog Trigger.grade Int32 := do
  Trigger.run choice
  Scoreboard.set (.named "#continued") points (.static 1)

@[mcfunction]
private def stoppingEntry : Prog (Grade.handled Trigger.grade) Unit := stopping.call.ignore

@[mcfunction]
private def discarded : Prog (Grade.handled Trigger.grade) Unit := do
  (Trigger.run choice).ignore
  (Scoreboard.set (.named "#continued") points (.static 2)).ignore

@[datapack]
public def specimen : Spec := build {
    ns := "sbtest", description := "Scoreboard and trigger acceptance", registerBudget := 6
  } do
    onLoad setup.ref
    entry "setup" setup.ref
    entry "add" addObjective.ref
    entry "duplicate" duplicate.ref
    entry "remove" removeObjective.ref
    entry "enable" enableInput.ref
    entry "enable-wrong" enableWrong.ref
    entry "enable-temporary" enableTemporary.ref
    entry "reset" resetInput.ref
    entry "reset-missing" resetMissing.ref
    entry "reset-all" resetEvery.ref
    entry "trigger" fire.ref
    entry "trigger-set" setEntry.ref
    entry "trigger-add" addEntry.ref
    entry "stop" stoppingEntry.ref
    entry "discard" discarded.ref

end Oria.Proofs.Fixtures.ScoreboardRuntime
