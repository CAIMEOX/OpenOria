module

import Game.Shared
import Oria.Datapack
meta import Oria
meta import Oria.Datapack

namespace Game

open Oria Oria.Std Oria.Datapack

@[mcfunction]
def setup : Prog Scoreboard.objectiveGrade.handled Unit :=
  (Scoreboard.Objectives.add "consumer.points" .dummy).ignore

@[mcfunction]
def run : Prog (Scoreboard.writeGrade (.named "#result")).handled Unit := do
  let n ← increment.call 7
  (Scoreboard.set (.named "#result") "consumer.points" n).ignore

@[datapack]
def game : Spec := build {ns := "consumer"} do
  onLoad setup.ref
  entry "home" run.ref
