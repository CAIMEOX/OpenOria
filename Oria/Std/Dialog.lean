module

public import Oria.Std.Command.Arg.Dialog
import Oria.Std.Command.Declarations

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Dialogs

`show` sends a native dialog, `clear` requests its dismissal, and `notice` constructs a
notification with a title and body. Dialogs may come from loaded registry resources,
host NBT, or command fragments with dynamic fields.

The result describes the send operation, with the recipient count as its success payload.
No matching players causes failure. Execution continues immediately after sending. Later
clicks and inputs belong to subsequent interactions and do not extend the current Oria
invocation arena's lifetime. Literal notices require only their targets' context.
Named and inline descriptions add the full context requirement because their components
may read the environment. All variants retain a conservative effect bound.
-/

namespace Oria.Std.Dialog

open Oria.Std.Command.Arg

/-- Combine target and content requirements, retaining the conservative dialog, world,
scoreboard-reading, and random effect bound. -/
@[expose] public def grade (targets : Players) (extraReq : ReqRow := Req.none) : Grade :=
  {
  req := Players.requirements targets ||| extraReq
  eff := Eff.dialog ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure }

/-- Dismissal-request effect bound, with context requirements determined by the player targets. -/
@[expose] public def clearGrade (targets : Players) : Grade :=
  { req := Players.requirements targets
    eff := Eff.dialog ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure }

private def showImpl (targets : Players) (content : DialogContent) :=
  Oria.Command.emit <| Command.Declarations.dialogShow.call <|
    .cons (Oria.Command.encode targets) <| .cons (Oria.Command.encode content) .nil

/--
Send a dialog and return immediately, yielding the recipient count on success. Named
resources must be loaded, and Minecraft checks inline schemas. No matching players causes
execution failure. Dynamic inline fields are parsed at function macro invocation.

```lean
open Oria Oria.Std
example := Dialog.show .self (.named "minecraft:server_links")
```
-/
public def «show» (targets : Players) (content : DialogContent) :
    Prog (grade targets (Oria.Command.encode content).requirements) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, Players.requirements, Oria.Command.Call.grade,
    Oria.Command.Call.requirements, Oria.Command.EncodedArgs.requirements,
    Oria.Command.EncodedArg.requirements, Oria.Command.Ref.call, Args.foldl,
    Command.Declarations.dialogShow, Oria.Command.Fragment.token,
    Oria.Command.Fragment.inline, Oria.Command.Fragment.require,
    Oria.Command.Fragment.nbt, Req.none, BitVec.or_assoc] using
    showImpl targets content

private def clearImpl (targets : Players) :=
  Oria.Command.emit <| Command.Declarations.dialogClear.call <|
    .cons (Oria.Command.encode targets) .nil

/-- Request dialog dismissal, returning the recipient count on success.
Fails if no players match. -/
public def clear (targets : Players) :
    Prog (clearGrade targets) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, clearGrade, Players.requirements, Oria.Command.encode,
    Oria.Command.ArgCodec.encode, Oria.Command.Call.grade,
    Oria.Command.Call.requirements, Oria.Command.EncodedArgs.requirements,
    Oria.Command.EncodedArg.requirements, Oria.Command.Ref.call, Args.foldl,
    Command.Declarations.dialogClear, Oria.Command.Fragment.token,
    Oria.Command.Fragment.require, Req.none] using
    clearImpl targets

/--
Construct and send a notice dialog from a host-side title and body.
The payload and failure conditions follow show. Context requirements come only from the
targets, so a notice to all players is valid in load or tick callbacks.

```lean
open Oria Oria.Std
example := Dialog.notice .all "Ready" "Choose your next action."
```
-/
public def notice (targets : Players) (title message : String) :
    Prog (grade targets) Int32 := by
  simpa using Dialog.show targets (.notice title message)

end Oria.Std.Dialog
