module

public import Oria.Std.Command.Arg
import Oria.Std.Command.Declarations.Generation
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Stopwatch

Stopwatches track server-running real time with millisecond resolution. They advance
independently of game ticks and continue while the server is paused. Their elapsed value is
saved with the world; offline time is excluded. Names are server-wide resource IDs.

Query returns elapsed seconds multiplied by scale and converted to I32 with Java's
truncation and saturation. Scale 1000 returns milliseconds; larger scales do not increase
the underlying clock's resolution. Ordinary I32 expressions can consume the result.
-/

namespace Oria.Std.Stopwatch
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Server-wide clock state needs no execution context and carries the world effect. -/
@[expose] public def grade : Grade :=
  ⟨Req.none, Eff.world ||| Eff.failure⟩

/-- Start a new stopwatch and return 1. An existing name fails without restarting it. -/
public def create (id : ResourceId) : Prog grade Int32 := do
  emit <| Command.Declarations.stopwatchCreate.call <| .cons (encode id) .nil

/-- Read elapsed seconds, scale, then truncate toward zero to I32. Zero and negative scales
are accepted. Scale may be a host decimal or a runtime I32; the ID is a host resource.
Missing names fail. A valid query returning zero still succeeds. -/
public def query (id : ResourceId) (scale : Decimal := .static 1) : Prog grade Int32 := do
  emit <| Command.Declarations.stopwatchQuery.call <|
    .cons (encode id) <| .cons (encode scale) .nil

/-- Reset an existing stopwatch's elapsed time to zero and return 1. Missing names fail. -/
public def restart (id : ResourceId) : Prog grade Int32 := do
  emit <| Command.Declarations.stopwatchRestart.call <| .cons (encode id) .nil

/-- Remove an existing stopwatch and return 1. Missing names fail. -/
public def remove (id : ResourceId) : Prog grade Int32 := do
  emit <| Command.Declarations.stopwatchRemove.call <| .cons (encode id) .nil

end Oria.Std.Stopwatch
