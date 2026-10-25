module

public import Oria.Std.Command.Arg.Position
import Oria.Std.Command.Declarations.Control
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# SetWorldSpawn

Set native world respawn data using the execution dimension, a block position, and optional
yaw/pitch. Omitting the location uses the execution position and zero rotation.
-/

namespace Oria.Std.SetWorldSpawn
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Dimension and location requirements. -/
@[expose] public def grade (location : SpawnLocation := .here) : Grade :=
  ⟨Req.dimension ||| location.requirements,
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.failure⟩

/-- Set world respawn data and return 1. Native position bounds are checked.
The setting persists independently of Oria's invocation arena. -/
public def set (location : SpawnLocation := .here) : Prog (grade location) Int32 := do
  emit <| Command.Declarations.worldSpawn.call <|
    .cons (encode location) <| .nil

end Oria.Std.SetWorldSpawn
