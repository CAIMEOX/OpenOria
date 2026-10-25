module

public import Oria.Std.Command.Arg.Presentation
import Oria.Std.Command.Declarations

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Sound playback and stopping

`play` sends a sound in a category at a position. Its default position is the command's
execution position. Use Execute as/at together to make the sound originate at each player.
Native playback skips other dimensions and recipients beyond the sound's range. Positive
minVolume allows distant recipients in the same dimension by relocating their sound origin.

`stop` independently filters category and sound ID. It sends a stop request even if a client
is not playing a matching sound. Results count packet recipients; actual audibility depends
on client assets and volume settings. The host sound ID may come from a resource pack.
-/

namespace Oria.Std.Sound

open Oria.Std.Command.Arg

/-- Playback reads the dimension for native filtering and its random seed, plus target and
coordinate requirements. Effects include sound, world access, score reads, and randomness. -/
@[expose] public def grade (targets : Players) (settings : SoundSettings := {}) : Grade :=
  ⟨Req.dimension ||| targets.requirements ||| settings.requirements,
    Eff.sound ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩

/-- Stop requests require only target selection; they do not filter by source dimension. -/
@[expose] public def stopGrade (targets : Players) : Grade :=
  ⟨targets.requirements, Eff.sound ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩

/-- Play a sound, defaulting to the master category at the execution position, volume 1,
pitch 1, and minVolume 0. Return the number of players sent a packet, failing if none qualify.
Native Float32 bounds are volume ≥ 0, pitch in 0..2, and minVolume in 0..1. Numeric settings
and coordinates may contain runtime integers; fractions are host values. Invalid dynamic
arguments fail after macro substitution. A missing client asset may remain inaudible despite success.

```lean
open Oria Oria.Std
example := Sound.play .self "minecraft:ui.button.click" .ui
example := Sound.play .all "game:round_start" .master
  {volume := .decimal 0.5, pitch := .decimal 1.25, minVolume := .decimal 0.1}
```
-/
public def play (targets : Players) (sound : ResourceId) (channel : SoundChannel := .master)
    (settings : SoundSettings := {}) : Prog (grade targets settings) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, Players.requirements, SoundSettings.requirements, Oria.Command.Call.grade,
    Oria.Command.Call.requirements, Oria.Command.Ref.call, Command.Declarations.soundPlay,
    Req.none, BitVec.or_assoc] using
    (Oria.Command.emit <| Command.Declarations.soundPlay.call <|
      .cons (Oria.Command.encode sound) <| .cons (Oria.Command.encode channel) <|
        .cons (Oria.Command.encode targets) <| .cons (Oria.Command.encode settings) .nil)

/-- Stop sounds for selected players. Optional category and ID filters are independent;
omitting both stops all sounds. Return the recipient count, even for repeated requests.
An empty player selection fails. Filters are chosen during construction. -/
public def stop (targets : Players) (channel : Option SoundChannel := none)
    (sound : Option ResourceId := none) : Prog (stopGrade targets) Int32 :=
  match channel, sound with
  | none, none => by
      simpa [Eff.failure, Grade.seq, Grade.failure, stopGrade, Players.requirements, Oria.Command.Call.grade, Oria.Command.Call.requirements,
        Oria.Command.Ref.call, Command.Declarations.soundStop, Req.none] using
        (Oria.Command.emit <| Command.Declarations.soundStop.call <|
          .cons (Oria.Command.encode targets) .nil)
  | some channel, none => by
      simpa [Eff.failure, Grade.seq, Grade.failure, stopGrade, Players.requirements, Oria.Command.Call.grade, Oria.Command.Call.requirements,
        Oria.Command.Ref.call, Command.Declarations.soundStopChannel, Req.none] using
        (Oria.Command.emit <| Command.Declarations.soundStopChannel.call <|
          .cons (Oria.Command.encode targets) <| .cons (Oria.Command.encode channel) .nil)
  | none, some sound => by
      simpa [Eff.failure, Grade.seq, Grade.failure, stopGrade, Players.requirements, Oria.Command.Call.grade, Oria.Command.Call.requirements,
        Oria.Command.Ref.call, Command.Declarations.soundStopAny, Req.none] using
        (Oria.Command.emit <| Command.Declarations.soundStopAny.call <|
          .cons (Oria.Command.encode targets) <| .cons (Oria.Command.encode sound) .nil)
  | some channel, some sound => by
      simpa [Eff.failure, Grade.seq, Grade.failure, stopGrade, Players.requirements, Oria.Command.Call.grade, Oria.Command.Call.requirements,
        Oria.Command.Ref.call, Command.Declarations.soundStopOne, Req.none] using
        (Oria.Command.emit <| Command.Declarations.soundStopOne.call <|
          .cons (Oria.Command.encode targets) <| .cons (Oria.Command.encode channel) <|
            .cons (Oria.Command.encode sound) .nil)

end Oria.Std.Sound
