module

public import Oria.Std.Command.Arg.Server
import Oria.Std.Command.Declarations.Server
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Server tick control

The native permission is administrator (level 3). Generated functions require a function
compilation permission set admitting this command. Each operation takes effect through the
server tick manager; it does not suspend the current Oria invocation.
-/

namespace Oria.Std.Admin.Tick
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Tick-manager reads and writes require no implicit execution context. -/
@[expose] public def grade : Grade :=
  ⟨Req.none, Eff.world ||| Eff.failure⟩

/-- Query/rate return the target rate truncated to I32. Freeze returns 1; unfreeze returns 0.
Step, sprint, and their stop operations return 1. Step requires frozen simulation; stopping
an inactive step or sprint fails. Durations must round to at least one tick. Rate accepts
1 through 10000 ticks per second. Numeric fields may contain runtime I32 holes. -/
public def run (action : TickAction) : Prog grade Int32 := do
  emit <| Command.Declarations.tick.call <| .cons (encode action) <| .nil

end Oria.Std.Admin.Tick
