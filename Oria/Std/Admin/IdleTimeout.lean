module

public import Oria.Std.Command.Arg.Server
import Oria.Std.Command.Declarations.Server
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Player idle timeout

The native administrator command changes the server-wide timeout in minutes.
It does not wait for an idle player to be disconnected.
-/

namespace Oria.Std.Admin.IdleTimeout
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Server configuration mutation, independent of execution context. -/
@[expose] public def grade : Grade :=
  ⟨Req.none, Eff.world ||| Eff.failure⟩

/-- Set a nonnegative timeout and return the minute count. Zero disables the timeout.
Dynamic values use an I32 macro hole and native range checking. -/
public def set (minutes : Scalar) : Prog grade Int32 := do
  emit <| Command.Declarations.idleTimeout.call <| .cons (encode minutes) <| .nil

end Oria.Std.Admin.IdleTimeout
