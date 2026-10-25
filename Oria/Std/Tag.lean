module

public import Oria.Std.Command.Arg
import Oria.Std.Command.Declarations

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Entity tags

Tags group entities for structured selectors. Tag names are checked host words; selectors
and these commands share Brigadier's unquoted alphabet. Add and remove return the number
of entities changed. List returns the size of the union of tag names on the selected entities.
The union can be empty, yielding a successful zero result.
-/

namespace Oria.Std.Tag

open Oria.Std.Command.Arg

/-- Entity selection requirements with a world, score-reading, and randomness effect bound. -/
@[expose] public def grade (targets : Target) : Grade :=
  ⟨targets.requirements, Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩

/-- Add a host tag to selected entities. Return the changed-entity count; fail if no tag is
added, including duplicate tags or Minecraft's per-entity tag limit. Empty selections fail.

```lean
open Oria Oria.Std
example := Tag.add .self "game.playing"
```
-/
public def add (targets : Target) (tag : Oria.Command.Word) : Prog (grade targets) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, Target.requirements, Oria.Command.Call.grade, Oria.Command.Call.requirements,
    Oria.Command.Ref.call, Command.Declarations.tagAdd, Req.none] using
    (Oria.Command.emit <| Command.Declarations.tagAdd.call <|
      .cons (Oria.Command.encode targets) <| .cons (Oria.Command.encode tag) .nil)

/-- Remove a host tag. Return the number of changed entities; fail if none carry the tag
or the selection is empty. Discard permits idempotent cleanup. -/
public def remove (targets : Target) (tag : Oria.Command.Word) : Prog (grade targets) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, Target.requirements, Oria.Command.Call.grade, Oria.Command.Call.requirements,
    Oria.Command.Ref.call, Command.Declarations.tagRemove, Req.none] using
    (Oria.Command.emit <| Command.Declarations.tagRemove.call <|
      .cons (Oria.Command.encode targets) <| .cons (Oria.Command.encode tag) .nil)

/-- Query the distinct tag count across a nonempty entity selection. The command also sends
native feedback. A selection whose entities have no tags succeeds with result zero; an empty
entity selection fails. Read entity NBT separately when the actual names are needed. -/
public def list (targets : Target) : Prog (grade targets) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, Target.requirements, Oria.Command.Call.grade, Oria.Command.Call.requirements,
    Oria.Command.Ref.call, Command.Declarations.tagList, Req.none] using
    (Oria.Command.emit <| Command.Declarations.tagList.call <|
      .cons (Oria.Command.encode targets) .nil)

end Oria.Std.Tag
