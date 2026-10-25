module

public import Oria.Std.Command.Arg.Server
import Oria.Std.Command.Declarations.Server
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Datapack inspection

Listing returns counts. Names are native source feedback, which Minecraft suppresses inside
functions. The native permission is gamemaster (level 2).
-/

namespace Oria.Std.PackControl
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Which native datapack list to inspect. -/
public inductive Filter where
  /-- Enabled packs and compatible disabled packs. -/
  | all
  /-- Enabled packs. -/
  | enabled
  /-- Compatible packs that are currently disabled. -/
  | available

/-- Pack repository inspection has a world-effect bound and no context requirement. -/
@[expose] public def grade : Grade :=
  ⟨Req.none, Eff.world ||| Eff.failure⟩

/-- Refresh pack discovery and return the selected list's count. Empty lists succeed with zero.
Available packs exclude enabled packs and packs requiring unavailable features. -/
public def list (filter : Filter := .all) : Prog grade Int32 :=
  match filter with
  | .all => do emit <| Command.Declarations.packList.call <| .nil
  | .enabled => do emit <| Command.Declarations.packListEnabled.call <| .nil
  | .available => do emit <| Command.Declarations.packListAvailable.call <| .nil

end Oria.Std.PackControl
