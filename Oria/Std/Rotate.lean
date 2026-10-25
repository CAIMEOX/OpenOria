module

public import Oria.Std.Command.Arg.Control
import Oria.Std.Command.Declarations.Control
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Rotate

Rotate one entity using explicit yaw/pitch or a facing target. Relative angles read the
execution rotation. Facing uses the execution anchor on the rotated entity, independently
of the anchor chosen on a destination entity.
-/

namespace Oria.Std.Rotate
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Target and rotation/facing requirements. -/
@[expose] public def grade (target : Target) (action : RotationAction) : Grade :=
  ⟨target.requirements ||| action.requirements,
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.failure⟩

/-- Apply native rotation, returning 1. Missing targets fail; repeated angles can succeed. -/
public def run (target : Target) (action : RotationAction) :
    Prog (grade target action) Int32 := do
  emit <| Command.Declarations.rotate.call <|
    .cons (encode target) <| .cons (encode action) <| .nil

end Oria.Std.Rotate
