module

public import Oria.Std.Command.Arg.Server
import Oria.Std.Command.Declarations.Server
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Player disconnection

Kick requires native administrator permission (level 3) and a published server.
Reasons use the greedy Message argument, including its structured selector requirements.
-/

namespace Oria.Std.Admin.Kick
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Selection and reason requirements, with disconnection and message effects. -/
@[expose] public def grade (players : Players) (reason : Option Message := none) : Grade :=
  ⟨players.requirements ||| (reason.map Message.requirements).getD Req.none,
    Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.chat ||| Eff.failure⟩

/-- Disconnect selected players and return the number disconnected. The singleplayer owner
is skipped. Fails if no eligible player remains or the server is not published. Omitting a
reason uses Minecraft's localized default. -/
public def run (players : Players) (reason : Option Message := none) :
    Prog (grade players reason) Int32 :=
  match reason with
  | none => do emit <| Command.Declarations.kick.call <| .cons (encode players) <| .nil
  | some message => do emit <| Command.Declarations.kickReason.call <| .cons (encode players) <| .cons (encode message) <| .nil

end Oria.Std.Admin.Kick
