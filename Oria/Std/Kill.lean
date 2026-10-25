module

public import Oria.Std.Command.Arg
import Oria.Std.Command.Declarations

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Killing entities

`Kill.run` accepts a single entity or a structured selection. The native command processes
every selected entity and returns the count. Empty selections fail. The command's side
effects include the game's death processing and any resulting score/statistic changes.
-/

namespace Oria.Std.Kill

open Oria.Std.Command.Arg

/-- Native killing reads the current dimension and the target's selection context.
World, score access, and randomness form the conservative effect bound. -/
@[expose] public def grade (targets : Target := .self) : Grade :=
  ⟨Req.dimension ||| targets.requirements,
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.failure⟩

/-- Kill the selected entities, defaulting to the executor. Return the selected entity count;
an empty selection fails. Self requires an executor, supplied by an enclosing Execute scope
when needed. Arguments are constructed in Lean and the command runs in Minecraft.

```lean
open Oria Oria.Std
example := Kill.run (.selector (.allEntities { tags := [.include "temporary"] }))
```
-/
public def run (targets : Target := .self) : Prog (grade targets) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, Target.requirements, Oria.Command.Call.grade,
    Oria.Command.Call.requirements, Oria.Command.Ref.call, Command.Declarations.kill,
    Req.none, BitVec.or_assoc] using
    (Oria.Command.emit <| Command.Declarations.kill.call <|
      .cons (Oria.Command.encode targets) .nil)

end Oria.Std.Kill
