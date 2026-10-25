module

public import Oria.Std.Command.Arg.Scoreboard
import Oria.Std.Command.Declarations

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Player trigger input

Trigger commands modify the executing player's enabled trigger objective. The executor must
be a player, the objective must have the trigger criterion, and the score must be unlocked.
Minecraft checks these runtime conditions and reports failure through failure.

A successful trigger locks the score, including when the resulting value is zero. The next
input requires `Scoreboard.enable`. Numeric reset and authorization are distinct operations.
Server callbacks can process player input inside `Execute.forEach [.as .allPlayers]`.
-/

namespace Oria.Std.Trigger

open Oria.Std.Command.Arg
open Oria.Command (Objective)

/-- Trigger operations require an executor and read/write scoreboard state.
Player identity and authorization remain runtime checks. -/
@[expose] public def grade : Grade :=
  ⟨Req.executor, Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.failure⟩

/-- Increment the executing player's trigger score by one and consume its authorization.
Returns the updated score. Missing player context, a missing/non-trigger objective, or a
missing/locked score causes failure. -/
public def run (objective : Objective) : Prog grade Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, Oria.Command.Call.grade, Oria.Command.Call.requirements,
    Oria.Command.Ref.call, Command.Declarations.triggerRun, Req.none] using
    (Oria.Command.emit <| Command.Declarations.triggerRun.call <|
      .cons (Oria.Command.encode objective) .nil)

/-- Add a signed static or dynamic I32 and consume trigger authorization.
Returns the updated score. Preconditions and failure behavior follow run. -/
public def add (objective : Objective) (value : Scalar) : Prog grade Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, Oria.Command.Call.grade, Oria.Command.Call.requirements,
    Oria.Command.Ref.call, Command.Declarations.triggerAdd, Req.none] using
    (Oria.Command.emit <| Command.Declarations.triggerAdd.call <|
      .cons (Oria.Command.encode objective) <| .cons (Oria.Command.encode value) .nil)

/--
Set a signed static or dynamic I32 and consume trigger authorization, returning the written
value. A successful write of zero is a success and still locks the score. Preconditions
and failure behavior follow run.

```lean
open Oria Oria.Std
example (n : Val Int32) := Trigger.set "game.choice" (.dynamic n)
```
-/
public def set (objective : Objective) (value : Scalar) : Prog grade Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, Oria.Command.Call.grade, Oria.Command.Call.requirements,
    Oria.Command.Ref.call, Command.Declarations.triggerSet, Req.none] using
    (Oria.Command.emit <| Command.Declarations.triggerSet.call <|
      .cons (Oria.Command.encode objective) <| .cons (Oria.Command.encode value) .nil)

end Oria.Std.Trigger
