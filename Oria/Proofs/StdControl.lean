module

import Oria
import Oria.Std.DP121
import Oria.IR.DP121.Pretty
meta import Oria
meta import Oria.Std.DP121
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.StdControl
open Oria.Std Oria.Std.Command.Arg

example (team : String) :
    (Command.Selector.allPlayers {team := some (.include team)}).requirements = Req.none := by
  simp [Command.Selector.requirements, Command.Selector.Filters.requirements, Req.none]
example (value : Scalar) :
    (GameRule.randomTickSpeed.assign value).requirements = Req.none := by simp
example (value : Bool) :
    (GameRule.keepInventory.assign value).requirements = Req.none := by simp
example : (Spawnpoint.grade .all .here).req = Req.dimension ||| Req.position := rfl
example : (Rotate.grade .self (.angles ⟨.absolute (.static 0), .absolute (.static 0)⟩)).req =
    Req.executor := rfl
example : (Rotate.grade .self (.angles ⟨.relative (.static 0), .absolute (.static 0)⟩)).req =
    Req.executor ||| Req.rotation := rfl
example : (ScoreFormat.fixed (.literal "Round")).requirements = Req.none := rfl
example : (ScoreFormat.styled (.value (nbt% {bold: true}))).requirements = Req.none := rfl
example : (ObjectiveProperty.numberFormat .blank).requirements = Req.none := rfl
example : (DisplaySlot.sidebarTeam .red |> Command.encode).requirements = Req.none := rfl

private def render {sig : Command.Signature} (call : Command.Call EncodedVal sig) :
    Except Diagnostic String := do
  let p ← Std.DP121.plan call
  p.withInvocation
    (fun i => pure ((Target.DP121.Command.invoke i).format.pretty 120))
    (fun _ _ _ i _ => pure ((Target.DP121.Command.invoke i).format.pretty 120))

private def message (team : Command.Selector.Match String) :=
  Command.Declarations.tellraw.call <|
    .cons (Command.encode (Players.selector (.allPlayers {team := some team}))) <|
      .cons (Command.encode (TextComponent.literal "Ready")) .nil

#guard (render (message (.include "red"))).toOption =
  some "tellraw @a[team=red] {\"text\":\"Ready\"}"
#guard (render (message (.exclude ""))).toOption =
  some "tellraw @a[team=!] {\"text\":\"Ready\"}"
#guard render (message (.include "red,limit=1")) matches .error _

private def belowName := Command.Declarations.objectiveSetDisplay.call <|
  .cons (Command.encode DisplaySlot.belowName) <|
    .cons (Command.encode (Oria.Command.Objective.ofString "points")) .nil

#guard (render belowName).toOption = some "scoreboard objectives setdisplay below_name points"

end Oria.Proofs.StdControl
