module

public import Oria.Std.Command.Arg.World
import Oria.Std.Command.Declarations.World
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Difficulty

Difficulty query returns its native ID (peaceful 0 through hard 3). Setting changes server
difficulty, returns a successful zero, and fails when unchanged.
-/

namespace Oria.Std.Difficulty

open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Requirements and effects of querying difficulty. -/
@[expose] public def readGrade : Grade :=
  ⟨Req.dimension,
    Eff.world ||| Eff.failure⟩
/-- Requirements and effects of setting difficulty. -/
@[expose] public def writeGrade : Grade :=
  ⟨Req.none,
    Eff.world ||| Eff.failure⟩

/-- Query the source world's native difficulty ID. -/
public def get : Prog readGrade Int32 := do
  emit <| Command.Declarations.difficultyGet.call <| .nil

/-- Set server difficulty; unchanged difficulty fails, success returns 0. -/
public def set (level : DifficultyLevel) : Prog writeGrade Int32 := do
  emit <| Command.Declarations.difficultySet.call <| .cons (encode level) <| .nil

end Oria.Std.Difficulty
