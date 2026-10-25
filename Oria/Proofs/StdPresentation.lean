module

import Oria
import Oria.Std.Command.Declarations
import Oria.Std.DP121
import Oria.IR.DP121.Pretty
meta import Oria
meta import Oria.Std.DP121
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.StdPresentation

open Oria.Std Oria.Std.Command.Arg

example (word : Oria.Command.Word) : Oria.Command.Word.Valid word.text := word.valid
#guard (Oria.Command.Word.parse "round.active-1").isOk
#guard Oria.Command.Word.parse "" matches .error _
#guard Oria.Command.Word.parse "two words" matches .error _
#guard Oria.Command.Word.parse "x,limit=1" matches .error _
example (time : Time) : (Command.encode time).requirements = Req.none := rfl
example (channel : SoundChannel) : (Command.encode channel).requirements = Req.none := rfl
example : (Title.grade .all).req = Req.none := rfl
example : (Sound.grade .all).req = Req.dimension ||| Req.position := rfl
example : (Sound.stopGrade .all).req = Req.none := rfl
example : (Tag.grade .self).req = Req.executor := rfl
example : Eff.hud &&& Eff.sound = Eff.none := rfl
example : (Title.grade .all).req ||| Req.server = Req.server := by decide
example : ¬((Title.grade .all Req.all).req ||| Req.server = Req.server) := by decide

@[mcfunction]
private def cue : Prog ⟨Req.none, Eff.sound ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random⟩ Unit := do
  Execute.forEach [.as .allPlayers, .at .self] do
    Sound.play .self "minecraft:ui.button.click" .ui

private def rendered {sig : Command.Signature} (call : Command.Call EncodedVal sig) :
    Except Diagnostic (String × Nat) := do
  let plan ← Std.DP121.plan call
  plan.withInvocation
    (fun i => pure ((Target.DP121.Command.invoke i).format.pretty 120, 0))
    (fun schema _ _ i _ => pure ((Target.DP121.Command.invoke i).format.pretty 120, schema.fields.length))

private def tag := Std.Command.Declarations.tagAdd.call <|
  .cons (Command.encode Target.self) <| .cons (Command.encode (Oria.Command.Word.ofString "round.active")) .nil
#guard (rendered tag).toOption = some ("tag @s add round.active", 0)

private def title := Std.Command.Declarations.titleShow.call <|
  .cons (Command.encode Players.all) <| .cons (Command.encode TitlePart.actionbar) <|
    .cons (Command.encode (TextComponent.number (.dynamic 4))) .nil
#guard (rendered title).toOption =
  some ("title @a actionbar {\"translate\":\"%s\",\"with\":[$(p0)]}", 1)

private def times := Std.Command.Declarations.titleTimes.call <|
  .cons (Command.encode Players.all) <| .cons (Command.encode (Time.seconds (.decimal 0.25))) <|
    .cons (Command.encode (Time.ticks (.dynamic 2))) <| .cons (Command.encode (Time.days (.static 1))) .nil
#guard (rendered times).toOption = some ("title @a times 0.25s $(p0)t 1d", 1)

private def play := Std.Command.Declarations.soundPlay.call <|
  .cons (Command.encode (ResourceId.ofString "game:cue")) <|
  .cons (Command.encode SoundChannel.ui) <| .cons (Command.encode Players.all) <|
  .cons (Command.encode ({pitch := .dynamic 2, minVolume := .decimal 0.25} : SoundSettings)) .nil
#guard (rendered play).toOption = some ("playsound game:cue ui @a ~0 ~0 ~0 1 $(p0) 0.25", 1)

private def stop := Std.Command.Declarations.soundStopAny.call <|
  .cons (Command.encode Players.all) <| .cons (Command.encode (ResourceId.ofString "game:cue")) .nil
#guard (rendered stop).toOption = some ("stopsound @a * game:cue", 0)

end Oria.Proofs.StdPresentation
