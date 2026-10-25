module

public import Oria.Language
public import Oria.Meta
public import Oria.Std.Scoreboard
public import Oria.Std.Teleport
public import Oria.Datapack
public import Oria.Std.Execute
meta import Oria.Meta
meta import Oria.Std.Scoreboard
meta import Oria.Std.Teleport
meta import Oria.Datapack
meta import Oria.Std.Execute

namespace Oria.Proofs.Fixtures.ExecuteRuntime

open Oria.Std Oria.Std.Command.Arg Oria.Datapack

private def points : Command.Objective := "execute.oria"
private def results : Command.Objective := "execute.result"
private def successes : Command.Objective := "execute.success"
private def subjects : Command.Selector := .ofString "@e[type=minecraft:marker,tag=oria_execute]"
private def shared (name : String) (h : Command.SyntaxToken.Valid name := by native_decide)
    (safe : scoreHolderNameSafe name := by native_decide) : ScoreSlot :=
  ⟨.named (.ofString name h safe), points⟩
private def effects := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.failure
private def grade : Grade := ⟨Req.all, effects⟩

@[mcfunction]
private def eachPlayer : Prog (Grade.handled ⟨Req.none, effects⟩) Unit :=
  Execute.forEach [.as .allPlayers] do
    Scoreboard.set .self points (.static 1)

example : eachPlayer.signature.grade.req = Req.none := rfl

@[mcfunction]
private def fork : Prog grade Int32 := do
  let captured ← Scoreboard.get (.named "#seed") points
  Execute.forEach [.storeResult (.score ⟨.self, results⟩), .as subjects,
      .storeSuccess (.score ⟨.self, successes⟩), .storeResult (.score ⟨.self, results⟩)] do
    let value ← Scoreboard.get .self points
    let n := captured + value
    Scoreboard.set .self points (.dynamic n)
    Scoreboard.operation (shared "#count") .add (shared "#one")
    Scoreboard.set (.named "#seed") points (.static 999)
    return n
  Scoreboard.set (.named "#after") points (.dynamic captured)
  return captured

@[mcfunction]
private def forkEntry : Prog (Grade.handled grade) Unit := fork.call.ignore

@[mcfunction]
private def nested : Prog (Grade.handled grade) Unit := do
  Execute.forEach [.as subjects] do
    Scoreboard.operation (shared "#before") .add (shared "#one")
    Execute.forEach [.as subjects] do
      Scoreboard.operation (shared "#cross") .add (shared "#one")
    Scoreboard.operation (shared "#outer") .add (shared "#one")
  (Scoreboard.set (.named "#continued") points (.static 1)).ignore

@[mcfunction]
private def conditional (threshold : Val Int32) : Prog (Grade.handled grade) Unit := do
  Execute.forEach [.as subjects, .when (.matches ⟨.self, points⟩ (.atLeast (.dynamic threshold))),
      .at .self, .positioned (.world (.relative (.static 1)) (.relative (.static 0)) (.relative (.static 0)))] do
    Teleport.to .self (.world (.relative (.static 0)) (.relative (.static 0)) (.relative (.static 0)))
  (Scoreboard.set .self points (.static 77)).ignore

@[mcfunction]
private def conditionalEntry : Prog (Grade.handled grade) Unit := conditional.call 11

@[mcfunction]
private def empty : Prog (Grade.handled grade) Unit := do
  Execute.forEach [.as (.ofString "@e[tag=oria_execute_absent]")] do
    Scoreboard.set (.named "#skipped") points (.static 1)
  (Scoreboard.set (.named "#continued") points (.static 2)).ignore

@[datapack]
public def specimen : Spec := build {
    ns := "execute"
    description := "Scoped execution acceptance"
    registerBudget := 8
  } do
    entry "fork" forkEntry.ref
    entry "nested" nested.ref
    entry "conditional" conditionalEntry.ref
    entry "empty" empty.ref
    onTick eachPlayer.ref

@[datapack]
public def allStack : Spec := build { specimen.settings with
    ns := "execute_stack", registerBudget := 6 } do
  entry "fork" forkEntry.ref
  entry "nested" nested.ref
  entry "conditional" conditionalEntry.ref
  entry "empty" empty.ref

end Oria.Proofs.Fixtures.ExecuteRuntime
