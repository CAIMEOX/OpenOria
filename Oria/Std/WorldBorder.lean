module

public import Oria.Std.Command.Arg.World
import Oria.Std.Command.Declarations.World
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# WorldBorder

Operations address the source dimension's world border. Coordinates and numeric values reuse shared
codecs. Native size bounds, transition timing, and unchanged-state failures are preserved.
-/

namespace Oria.Std.WorldBorder

open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- The border requires a dimension, plus any coordinate requirements. -/
@[expose] public def grade (action : BorderAction) : Grade :=
  ⟨Req.dimension ||| action.requirements,
    Eff.world ||| Eff.failure⟩

/-- Execute a border operation. Get returns rounded diameter; setters retain their native
numeric results. Transition and warning durations use the native time parser. -/
public def run (action : BorderAction) : Prog (grade action) Int32 := do
  emit <| Command.Declarations.border.call <| .cons (encode action) <| .nil

end Oria.Std.WorldBorder
