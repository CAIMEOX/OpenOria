module

public import Oria.Std.Command.Arg.Control
import Oria.Std.Command.Declarations.Control
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Spectate

Spectating selects one native entity as one player's camera. The viewer must be a spectator
and may not target themself. Stop resets the executing player's camera. These operations
return 1 on success and preserve native failure conditions.
-/

namespace Oria.Std.Spectate
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Camera target and viewer requirements. -/
@[expose] public def grade (target : Target) (player : Players := .self) : Grade :=
  ⟨target.requirements ||| player.requirements,
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.failure⟩

/-- Set one spectator's camera target. Minecraft enforces singular target and player selection. -/
public def start (target : Target) (player : Players := .self) :
    Prog (grade target player) Int32 := do
  emit <| Command.Declarations.spectate.call <|
    .cons (encode target) <| .cons (encode player) <| .nil

/-- Reset the executing spectator's camera to themself. -/
public def stop : Prog ⟨Req.executor, Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.failure⟩ Int32 := do
  emit <| Command.Declarations.spectateStop.call <|
    .nil

end Oria.Std.Spectate
