module

import Oria
import Oria.Datapack
meta import Oria
meta import Lean.Elab.GuardMsgs

namespace Oria.Tests.ExecuteImports

open Oria Oria.Std Oria.Datapack

private def points : Command.Objective := .ofString "scope.points"
private def effects := Eff.world ||| Eff.scoreboardRead ||| Eff.random

@[mcfunction]
private def inspectPlayers : Prog ⟨Req.none, effects⟩ Unit := do
  let read := Scoreboard.get .self points
  Execute.forEach [.as .allPlayers] do
    let n ← read
    return n

private def spec : Spec := build { ns := .ofString "scope" } do
  onTick inspectPlayers.ref

example : inspectPlayers.signature.grade.req = Req.none := rfl
#guard spec.registrations.size == 1

/-- error: Oria `do` grade mismatch -/
#guard_msgs(error, substring := true) in
example : Prog ⟨Req.none, Eff.scoreboardRead⟩ Int32 := do
  Scoreboard.get .self points

/-- error: Oria `do` grade mismatch -/
#guard_msgs(error, substring := true) in
example : Prog ⟨Req.executor, Eff.scoreboardRead⟩ Int32 := do
  let n ← Scoreboard.get .self points
  return n

end Oria.Tests.ExecuteImports
