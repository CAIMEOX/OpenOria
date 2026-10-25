module

public import Oria.Std.Command.Arg.Control
import Oria.Std.Command.Declarations.Control
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Forceload

Forced chunks belong to the execution dimension. Coordinates name blocks and are converted
to chunk coordinates by Minecraft. Native world bounds and the per-operation chunk limit
apply. A successful request records a loading ticket; loading may finish later.
-/

namespace Oria.Std.Forceload
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Source dimension and coordinate requirements. -/
@[expose] public def grade (action : ForceloadAction) : Grade :=
  ⟨Req.dimension ||| action.requirements,
    Eff.world ||| Eff.failure⟩

/-- Add/remove returns changed chunks and fails when none change. Query succeeds with 1 for
a forced chunk; list returns the count, including successful zero. Clear returns 0. -/
public def run (action : ForceloadAction) : Prog (grade action) Int32 := do
  emit <| Command.Declarations.forceload.call <|
    .cons (encode action) <| .nil

end Oria.Std.Forceload
