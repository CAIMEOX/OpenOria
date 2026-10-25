module

public import Oria.Std.Command.Arg
import Oria.Std.Command.Declarations.Utility
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Native server information

Players returns the online count, seed returns the low signed I32 bits of the world seed,
and version returns 1. Minecraft functions suppress the native report text; generated
programs receive the integer payloads. Native report text is not available as an Oria value.
-/

namespace Oria.Std.ServerInfo
open Oria.Command (emit)

/-- Server information reads world state, with an optional dimension requirement. -/
@[expose] public def grade (req : ReqRow := Req.none) : Grade :=
  ⟨req, Eff.world ||| Eff.failure⟩

/-- Return the online-player count. Uuids changes the native report format, which ordinary
function execution suppresses. An empty server succeeds with result zero. -/
public def players (uuids : Bool := false) : Prog (grade) Int32 := by
  cases uuids with
  | false => exact emit (Command.Declarations.onlinePlayers.call .nil)
  | true => exact emit (Command.Declarations.onlinePlayersUuids.call .nil)

/-- Return the current world's low 32 seed bits interpreted as signed I32, following Java's
long-to-int conversion. Function execution suppresses the native full-seed report. -/
public def seed : Prog (grade Req.dimension) Int32 := do
  emit <| Command.Declarations.worldSeed.call .nil

/-- Run the native version command and return 1. Functions suppress its report text.
The payload is a success result, not a version identifier or datapack format. -/
public def version : Prog (grade) Int32 := do
  emit <| Command.Declarations.serverVersion.call .nil

end Oria.Std.ServerInfo
