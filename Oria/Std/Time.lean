module

public import Oria.Std.Command.Arg.World
import Oria.Std.Command.Declarations.World
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Time

DP121 world clocks support total ticks, named markers, rates, pause/resume, and timeline queries. A
missing clock selects the source dimension's default; named clocks are server resources. These
operations do not suspend Oria execution.
-/

namespace Oria.Std.Time

open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Default-clock selection reads the dimension; named-clock selection is context-independent. -/
@[expose] public def grade (clock : Option ResourceId := none) : Grade :=
  ⟨if clock.isNone then Req.dimension else Req.none,
    Eff.world ||| Eff.failure⟩

/-- Execute a clock operation. Unchanged set/pause/rate operations can fail.
Tick queries use the native remainder modulo 2147483647; pause, resume, and rate return 1. -/
public def run (action : ClockAction) (clock : Option ResourceId := none) :
    Prog (grade clock) Int32 :=
  match clock with
  | none => do
      emit <| Command.Declarations.clock.call <| .cons (encode action) <| .nil
  | some id => do
      emit <| Command.Declarations.clockOf.call <| .cons (encode id) <| .cons (encode action) <| .nil

/-- Read native game time, independently of world-clock rate and pause state. -/
public def gameTime : Prog ⟨Req.dimension, Eff.world ||| Eff.failure⟩ Int32 := do
  emit <| Command.Declarations.gameTime.call <| .nil

end Oria.Std.Time
