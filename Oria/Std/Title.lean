module

public import Oria.Std.Command.Arg.Presentation
import Oria.Std.Command.Declarations

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Titles and action bars

`show` sends text to the main title, subtitle, or action bar. TextComponent is shared with
Tellraw: literal text and numeric interpolation add no context requirements, while complete
NBT components retain the full context contract. Commands return the recipient count and
fail for an empty player selection. Success reports packet delivery, not client rendering.

`times` sets title animation durations using native time units. `clear` clears titles;
its reset flag also restores native timings. Action-bar display is independent of title timing.
-/

namespace Oria.Std.Title

open Oria.Std.Command.Arg

/-- Combine target and text requirements with HUD, world, score-reading, and random effects. -/
@[expose] public def grade (targets : Players) (extraReq : ReqRow := Req.none) : Grade :=
  ⟨targets.requirements ||| extraReq, Eff.hud ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩

/-- Send a text component to a title location, defaulting to the main title. The result is
the recipient count; no players means failure. Full NBT components are resolved per recipient.
Numeric text may contain a runtime I32; other component data and the location are host values.

```lean
open Oria Oria.Std
example := Title.show .all (.literal "Round one")
example (n : Val Int32) := Title.show .self (.number (.dynamic n)) .actionbar
example := Title.show .self (.ofNbt (nbt% {text: "Ready", color: "gold"})) .subtitle
```
-/
public def «show» (targets : Players) (message : TextComponent) (part : TitlePart := .title) :
    Prog (grade targets message.requirements) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, Players.requirements, Oria.Command.Call.grade, Oria.Command.Call.requirements,
    Oria.Command.Ref.call, Command.Declarations.titleShow, Req.none, BitVec.or_assoc] using
    (Oria.Command.emit <| Command.Declarations.titleShow.call <|
      .cons (Oria.Command.encode targets) <| .cons (Oria.Command.encode part) <|
        .cons (Oria.Command.encode message) .nil)

/-- Set fade-in, stay, and fade-out durations. Native Float32 scaling and rounding produce
nonnegative tick counts; negative results fail parsing. Values can combine host fractions and
runtime integers. Return the recipient count, failing on an empty selection. -/
public def times (targets : Players) (fadeIn stay fadeOut : Time) :
    Prog (grade targets) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, Players.requirements, Oria.Command.Call.grade, Oria.Command.Call.requirements,
    Oria.Command.Ref.call, Command.Declarations.titleTimes, Req.none, BitVec.or_assoc] using
    (Oria.Command.emit <| Command.Declarations.titleTimes.call <|
      .cons (Oria.Command.encode targets) <| .cons (Oria.Command.encode fadeIn) <|
        .cons (Oria.Command.encode stay) <| .cons (Oria.Command.encode fadeOut) .nil)

/-- Clear the title and subtitle. A true host reset flag also restores native animation
timings. Return the recipient count even when titles were already clear; no players fails. -/
public def clear (targets : Players) (reset : Bool := false) : Prog (grade targets) Int32 :=
  if reset then by
    simpa [Eff.failure, Grade.seq, Grade.failure, grade, Players.requirements, Oria.Command.Call.grade, Oria.Command.Call.requirements,
      Oria.Command.Ref.call, Command.Declarations.titleReset, Req.none] using
      (Oria.Command.emit <| Command.Declarations.titleReset.call <|
        .cons (Oria.Command.encode targets) .nil)
  else by
    simpa [Eff.failure, Grade.seq, Grade.failure, grade, Players.requirements, Oria.Command.Call.grade, Oria.Command.Call.requirements,
      Oria.Command.Ref.call, Command.Declarations.titleClear, Req.none] using
      (Oria.Command.emit <| Command.Declarations.titleClear.call <|
        .cons (Oria.Command.encode targets) .nil)

end Oria.Std.Title
