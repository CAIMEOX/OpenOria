module

public import Oria.Std.Command.Arg.Control
import Oria.Std.Command.Declarations.Control
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# PostEffect

Manage resource-pack post-processing effects on players. The server records IDs and sends
packets on a subsequent player update; it cannot verify that a client has or renders the
referenced shader. Add/remove/clear return changed-player counts and fail when none change.
List requires one player.
-/

namespace Oria.Std.PostEffect
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Player selection and client presentation effects. -/
@[expose] public def grade (players : Players) : Grade :=
  ⟨players.requirements,
    Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.hud ||| Eff.failure⟩

/-- Add a post effect. Duplicate-only selections fail. -/
public def add (players : Players) (effect : ResourceId) : Prog (grade players) Int32 := do
  emit <| Command.Declarations.postAdd.call <|
    .cons (encode players) <| .cons (encode effect) <| .nil

/-- Remove a post effect, failing when absent from every selected player. -/
public def remove (players : Players) (effect : ResourceId) : Prog (grade players) Int32 := do
  emit <| Command.Declarations.postRemove.call <|
    .cons (encode players) <| .cons (encode effect) <| .nil

/-- Clear all post effects from selected players. -/
public def clear (players : Players) : Prog (grade players) Int32 := do
  emit <| Command.Declarations.postClear.call <|
    .cons (encode players) <| .nil

/-- Return the active effect count for one player, including successful zero. -/
public def list (player : Players := .self) : Prog (grade player) Int32 := do
  emit <| Command.Declarations.postList.call <|
    .cons (encode player) <| .nil

end Oria.Std.PostEffect
