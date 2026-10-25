module

public import Oria.Std.Command.Arg.Server
import Oria.Std.Command.Declarations.Server
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Server transfer requests

Transfer is registered on dedicated servers and requires administrator permission (level 3).
The receiving server must accept transfers. Client connection completion happens after the
command and is not acknowledged by its result.
-/

namespace Oria.Std.Admin.Transfer
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Recipient selection determines context; transfer changes connection state. -/
@[expose] public def grade (players : Players) : Grade :=
  ⟨players.requirements, Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩

/-- Send a transfer request and return the selected player count. Defaults to the executor.
The host is quoted statically; the port may be a runtime I32 and must be in 1 through 65535.
A missing player target fails. -/
public def to (destination : Destination) (players : Players := .self) :
    Prog (grade players) Int32 := do
  emit <| Command.Declarations.transfer.call <| .cons (encode destination) <| .cons (encode players) <| .nil

end Oria.Std.Admin.Transfer
