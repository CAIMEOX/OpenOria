module

public import Oria.Std.Command.Arg.Position
import Oria.Std.Command.Declarations.Control
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Spawnpoint

Set selected players' respawn configuration in the execution dimension. The position
defaults to the command position and rotation to zero. Explicit yaw and pitch may be
relative to the execution rotation. Player spawn pitch is clamped to the native range.
-/

namespace Oria.Std.Spawnpoint
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Dimension, player selection, and spawn-location requirements. -/
@[expose] public def grade (players : Players) (location : SpawnLocation := .here) : Grade :=
  ⟨Req.dimension ||| (players.requirements ||| location.requirements),
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.failure⟩

/-- Set player respawn positions. Return the number of selected players, including repeated
assignments. Empty/non-player selections and out-of-bounds positions fail. -/
public def set (players : Players := .self) (location : SpawnLocation := .here) :
    Prog (grade players location) Int32 := do
  emit <| Command.Declarations.spawnpoint.call <|
    .cons (encode players) <| .cons (encode location) <| .nil

end Oria.Std.Spawnpoint
