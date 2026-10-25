module

public import Oria.Std.Command.Arg.Scoreboard
public import Oria.Std.Command.Arg.Display
import Oria.Std.Command.Declarations
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Scoreboards

`ScoreHolder` and `Objective` identify an I32 score. `ScoreSlot` combines them for binary
operations, Execute conditions, and result stores. The datapack's initialization or the
server must create the objective before use.

Named holders may be fake players, such as `#counter`. `.self` refers to the current executor
and requires its context. `readGrade`, `writeGrade`, and `operationGrade` describe the effects
of `get`, `set`, and `operation`. `Objectives.add` and `Objectives.remove` manage objectives;
`reset` removes one score, while `resetAll` explicitly removes all scores of a holder.
`enable` permits the next trigger input. See the [standard library guide](##Oria.Std) for
command results and failure composition.

Add and remove accept the shared Holders selection, including entity groups and the tracked
holder wildcard. Their native payload is the I32 sum of the resulting scores. Each update
and the aggregate sum use signed I32 overflow behavior. The amount is nonnegative, while a
resulting score may be negative.
-/

namespace Oria.Std.Scoreboard

open Oria.Std.Command.Arg
open Oria.Command (Objective ScoreOp)

/-- Score-reading effects and the holder's context requirements. Named holders need no executor. -/
@[expose] public def readGrade (holder : ScoreHolder) : Grade :=
  ⟨holder.requirements, Eff.scoreboardRead ||| Eff.failure⟩

/-- Score-writing effects and the holder's context requirements. -/
@[expose] public def writeGrade (holder : ScoreHolder) : Grade :=
  ⟨holder.requirements, Eff.scoreboardWrite ||| Eff.failure⟩

/-- Read/write effects of a binary operation, including both holders' context requirements. -/
@[expose] public def operationGrade (target source : ScoreSlot) : Grade :=
  ⟨target.requirements ||| source.requirements, Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.failure⟩

/-- Objective creation/removal reads the catalog and modifies scoreboard state. -/
@[expose] public def objectiveGrade : Grade :=
  ⟨Req.none, Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.failure⟩

/-- Trigger enabling inspects the holder's lock and modifies scoreboard state. -/
@[expose] public def enableGrade (holder : ScoreHolder) : Grade :=
  ⟨holder.requirements, Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.failure⟩

/-- Group score updates combine native holder selection with score reads and writes. -/
@[expose] public def updateGrade (holders : Holders) : Grade :=
  ⟨holders.requirements, Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.failure⟩

/-- Add a nonnegative amount to every selected score. Creates missing scores at zero;
the objective must already exist. Returns the native sum of resulting scores, using I32
overflow semantics. The amount may be a runtime integer, with native nonnegative checking. -/
public def add (holders : Holders) (objective : Objective) (amount : Scalar) :
    Prog (updateGrade holders) Int32 := do
  Oria.Command.emit <| Command.Declarations.scoreAdd.call <|
    .cons (Oria.Command.encode holders) <| .cons (Oria.Command.encode objective) <|
    .cons (Oria.Command.encode amount) .nil

/-- Subtract a nonnegative amount from selected scores and return their resulting sum.
Scores may become negative. Zero can succeed; missing objectives and invalid dynamic amounts
fail. Holder wildcards use the native scoreboard's tracked-holder set. -/
public def remove (holders : Holders) (objective : Objective) (amount : Scalar) :
    Prog (updateGrade holders) Int32 := do
  Oria.Command.emit <| Command.Declarations.scoreRemove.call <|
    .cons (Oria.Command.encode holders) <| .cons (Oria.Command.encode objective) <|
    .cons (Oria.Command.encode amount) .nil

namespace Objectives

/--
Create an objective, returning the total objective count after creation. An existing name
fails without changing its criterion or scores. The criterion is parsed by Minecraft.
Discard the duplicate-name failure explicitly when initialization should preserve an
existing objective across reloads.

```lean
open Oria Oria.Std
example := Scoreboard.Objectives.add "game.choice" .trigger
```
-/
public def add (objective : Objective) (criterion : Criterion) :
    Prog objectiveGrade Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, objectiveGrade, Oria.Command.Call.grade, Oria.Command.Call.requirements,
    Oria.Command.Ref.call, Command.Declarations.objectiveAdd, Req.none] using
    (Oria.Command.emit <| Command.Declarations.objectiveAdd.call <|
      .cons (Oria.Command.encode objective) <| .cons (Oria.Command.encode criterion) .nil)

/-- Remove an existing objective and all its scores, returning the remaining objective count.
A missing objective fails. Use this for explicit teardown; routine reload initialization
should preserve existing player state. Keep the compiler's runtime objective alive while
generated code is executing. -/
public def remove (objective : Objective) : Prog objectiveGrade Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, objectiveGrade, Oria.Command.Call.grade, Oria.Command.Call.requirements,
    Oria.Command.Ref.call, Command.Declarations.objectiveRemove, Req.none] using
    (Oria.Command.emit <| Command.Declarations.objectiveRemove.call <|
      .cons (Oria.Command.encode objective) .nil)

end Objectives

/-- Count a holder's score entries, or all tracked holders when omitted. Empty lists succeed.
Native names and values are source feedback; only their count enters the object program. -/
public def list (holder : Option ScoreHolder := none) :
    Prog ⟨(holder.map ScoreHolder.requirements).getD Req.none, Eff.scoreboardRead ||| Eff.failure⟩ Int32 :=
  match holder with
  | none => do Oria.Command.emit <| Command.Declarations.scoreList.call .nil
  | some h => do
      Oria.Command.emit <| Command.Declarations.scoreListOf.call <|
        .cons (Oria.Command.encode h) .nil

namespace Objectives

/-- Count all objectives, including successful zero. Native names are source feedback. -/
public def list : Prog ⟨Req.none, Eff.scoreboardRead ||| Eff.failure⟩ Int32 := do
  Oria.Command.emit <| Command.Declarations.objectiveList.call .nil

end Objectives

namespace Group

/-- Bulk-operation effects and the requirements of every operand. -/
@[expose] public def grade (req : ReqRow) : Grade :=
  ⟨req, Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.failure⟩

/-- Set every selected score and return their I32 sum. Missing entries start at zero;
the objective must exist and be writable. An empty entity selection fails. -/
public def set (target : Scores) (value : Scalar) :
    Prog (grade target.requirements) Int32 := do
  Oria.Command.emit <| Command.Declarations.scoreSetGroup.call <|
    .cons (Oria.Command.encode target) <| .cons (Oria.Command.encode value) .nil

/-- Remove selected entries in one objective and return the selected-holder count,
including holders whose entry was absent. An unresolved selection fails. -/
public def reset (target : Scores) : Prog (grade target.requirements) Int32 := do
  Oria.Command.emit <| Command.Declarations.scoreResetGroup.call <|
    .cons (Oria.Command.encode target) .nil

/-- Remove every score of selected holders across objectives. Returns their count.
This also removes trigger authorization. Keep compiler-owned scores outside this selection. -/
public def resetAll (holders : Holders) : Prog (grade holders.requirements) Int32 := do
  Oria.Command.emit <| Command.Declarations.scoreResetGroupAll.call <|
    .cons (Oria.Command.encode holders) .nil

/-- Unlock selected trigger scores and return the newly unlocked count. Missing entries are
created at zero. A non-trigger objective or no newly unlocked entries fails. -/
public def enable (target : Scores) : Prog (grade target.requirements) Int32 := do
  Oria.Command.emit <| Command.Declarations.scoreEnableGroup.call <|
    .cons (Oria.Command.encode target) .nil

/-- Apply each source to each target in native iteration order, returning the sum of final
target scores. Missing scores start at zero. Swap also mutates sources. Division by zero
can fail after earlier writes; failure does not roll them back. I32 aggregation can overflow. -/
public def operation (target : Scores) (op : ScoreOp) (source : Scores) :
    Prog (grade (target.requirements ||| source.requirements)) Int32 := do
  Oria.Command.emit <| Command.Declarations.scoreOperationGroup.call <|
    .cons (Oria.Command.encode target) <| .cons (Oria.Command.encode op) <|
    .cons (Oria.Command.encode source) .nil

end Group

/--
Read a score, returning its I32 value on success. Fails if the objective is absent or the
holder has no score in it. A successful read of 0 is distinct from failure.

```lean
open Oria Oria.Std Oria.Std.Command.Arg
example := Scoreboard.get (.named "#counter") "demo"
```
-/
public def get (holder : ScoreHolder) (objective : Objective) :
    Prog (readGrade holder) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, readGrade, ScoreHolder.requirements, Oria.Command.Call.grade,
    Oria.Command.Call.requirements, Oria.Command.Ref.call,
    Command.Declarations.scoreGet, Req.none] using
    (Oria.Command.emit <| Command.Declarations.scoreGet.call <|
      .cons (Oria.Command.encode holder) <| .cons (Oria.Command.encode objective) .nil)

/--
Set a holder's score and return the written value on success. Creates a missing score in
an existing objective; the objective itself must already exist. Writing the same value can
still succeed. Dynamic inputs use integer macro arguments.

```lean
open Oria Oria.Std Oria.Std.Command.Arg
example (n : Val Int32) := Scoreboard.set (.named "#counter") "demo" (.dynamic n)
```
-/
public def set (holder : ScoreHolder) (objective : Objective) (value : Scalar) :
    Prog (writeGrade holder) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, writeGrade, ScoreHolder.requirements, Oria.Command.Call.grade,
    Oria.Command.Call.requirements, Oria.Command.Ref.call,
    Command.Declarations.scoreSet, Req.none] using
    (Oria.Command.emit <| Command.Declarations.scoreSet.call <|
      .cons (Oria.Command.encode holder) <| .cons (Oria.Command.encode objective) <|
        .cons (Oria.Command.encode value) .nil)

/--
Perform a native scoreboard operation, usually updating the target. The success payload is
the target score after the operation; {name}`Oria.Command.ScoreOp.swap` updates both scores.
Division rounds toward negative infinity, modulo follows native command semantics, and a
zero divisor causes failure. Both objectives must exist. The native command initializes
missing scores participating in the operation to zero.
-/
public def operation (target : ScoreSlot) (op : ScoreOp) (source : ScoreSlot) :
    Prog (operationGrade target source) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, operationGrade, ScoreSlot.requirements, Oria.Command.Call.grade,
    Oria.Command.Call.requirements, Oria.Command.Ref.call,
    Command.Declarations.scoreOperation, Req.none] using
    (Oria.Command.emit <| Command.Declarations.scoreOperation.call <|
      .cons (Oria.Command.encode target) <| .cons (Oria.Command.encode op) <|
        .cons (Oria.Command.encode source) .nil)

/-- Remove a holder's score in an existing objective, returning 1 on success even if that
score was absent. A missing objective or unresolved holder fails. Removing a trigger score
also removes its authorization state; enable it again before accepting input. -/
public def reset (holder : ScoreHolder) (objective : Objective) :
    Prog (writeGrade holder) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, writeGrade, ScoreHolder.requirements, Oria.Command.Call.grade,
    Oria.Command.Call.requirements, Oria.Command.Ref.call,
    Command.Declarations.scoreReset, Req.none] using
    (Oria.Command.emit <| Command.Declarations.scoreReset.call <|
      .cons (Oria.Command.encode holder) <| .cons (Oria.Command.encode objective) .nil)

/-- Remove all scores of a holder across objectives, returning 1 on success even if no scores
were present. An unresolved holder fails. This also removes trigger authorization state. -/
public def resetAll (holder : ScoreHolder) : Prog (writeGrade holder) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, writeGrade, ScoreHolder.requirements, Oria.Command.Call.grade,
    Oria.Command.Call.requirements, Oria.Command.Ref.call,
    Command.Declarations.scoreResetAll, Req.none] using
    (Oria.Command.emit <| Command.Declarations.scoreResetAll.call <|
      .cons (Oria.Command.encode holder) .nil)

/-- Unlock a holder's trigger score, creating it at zero if absent. Returns 1 when a lock
is cleared. Fails for a missing/non-trigger objective, unresolved holder, or an already
unlocked score. Setting the numeric score does not unlock it. Use an Execute scope to
enable each selected player's self score. -/
public def enable (holder : ScoreHolder) (objective : Objective) :
    Prog (enableGrade holder) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, enableGrade, ScoreHolder.requirements, Oria.Command.Call.grade,
    Oria.Command.Call.requirements, Oria.Command.Ref.call,
    Command.Declarations.scoreEnable, Req.none] using
    (Oria.Command.emit <| Command.Declarations.scoreEnable.call <|
      .cons (Oria.Command.encode holder) <| .cons (Oria.Command.encode objective) .nil)

/-- Context and effects of objective and score presentation. -/
@[expose] public def displayGrade (req : ReqRow := Req.none) : Grade :=
  ⟨req, Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.failure⟩

namespace Objectives

/-- Assign or clear a display slot. Repeating the current assignment fails; success returns 0.
Team-colored sidebar slots reuse the native TeamColor argument. -/
public def setDisplay (slot : DisplaySlot) (objective : Option Objective := none) :
    Prog displayGrade Int32 :=
  match objective with
  | none => do
      Oria.Command.emit <| Command.Declarations.objectiveClearDisplay.call <|
        .cons (Oria.Command.encode slot) .nil
  | some objective => do
      Oria.Command.emit <| Command.Declarations.objectiveSetDisplay.call <|
        .cons (Oria.Command.encode slot) <| .cons (Oria.Command.encode objective) .nil

/-- Update an objective's name, rendering, automatic display names, or number format.
Successful results are 0; equality and failure behavior follow the selected native property. -/
public def modify (objective : Objective) (property : ObjectiveProperty) :
    Prog (displayGrade property.requirements) Int32 := do
  Oria.Command.emit <| Command.Declarations.objectiveModify.call <|
    .cons (Oria.Command.encode objective) <| .cons (Oria.Command.encode property) .nil

end Objectives

/-- Set or reset score display names. Missing score entries are created by Minecraft.
Return the native affected-holder count. Text may contain dynamic integer interpolation. -/
public def setName (holders : Holders) (objective : Objective) (name : Option TextComponent := none) :
    Prog (displayGrade (holders.requirements |||
      (name.map TextComponent.requirements).getD Req.none)) Int32 :=
  match name with
  | none => do
      Oria.Command.emit <| Command.Declarations.scoreResetName.call <|
        .cons (Oria.Command.encode holders) <| .cons (Oria.Command.encode objective) .nil
  | some name => do
      Oria.Command.emit <| Command.Declarations.scoreDisplayName.call <|
        .cons (Oria.Command.encode holders) <| .cons (Oria.Command.encode objective) <|
          .cons (Oria.Command.encode name) .nil

/-- Set or reset per-score number formats, returning the affected-holder count.
Reset restores the objective's format. Style decoding adds no requirements beyond its NBT fragment. -/
public def numberFormat (holders : Holders) (objective : Objective) (format : ScoreFormat) :
    Prog (displayGrade (holders.requirements ||| format.requirements)) Int32 := do
  Oria.Command.emit <| Command.Declarations.scoreNumberFormat.call <|
    .cons (Oria.Command.encode holders) <| .cons (Oria.Command.encode objective) <|
      .cons (Oria.Command.encode format) .nil

end Oria.Std.Scoreboard
