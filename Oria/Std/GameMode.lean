module

public import Oria.Std.Command.Arg.Gameplay
import Oria.Std.Command.Declarations.Player
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# GameMode

Set individual players' mode or the server default. Targets and modes are host descriptions;
selection happens when Minecraft executes the command. Results retain native changed/forced-player
counts, including successful zero.
-/

namespace Oria.Std.GameMode

open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Player-selection requirements with conservative gameplay and client-feedback effects. -/
@[expose] public def grade (targets : Players := .self) : Grade :=
  ⟨targets.requirements,
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.chat ||| Eff.failure⟩

/-- Change selected players' game mode, defaulting to self. An empty selection fails. -/
public def set (mode : Oria.Command.GameMode) (targets : Players := .self) :
    Prog (grade targets) Int32 := do
  emit <| Command.Declarations.gameMode.call <| .cons (encode mode) <| .cons (encode targets) <| .nil

/-- Set the server default mode. Native force-gamemode configuration determines immediate updates. -/
public def setDefault (mode : Oria.Command.GameMode) :
    Prog ⟨Req.none,
      Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.chat ||| Eff.failure⟩
      Int32 := do
  emit <| Command.Declarations.defaultGameMode.call <| .cons (encode mode) <| .nil

end Oria.Std.GameMode
