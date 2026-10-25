module

public import Oria.Std.Command.Arg.Control
import Oria.Std.Command.Declarations.Control
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# SpreadPlayers

Random placement searches for safe ground in the source dimension. Settings select
separation, range, an optional height bound, and native team grouping. The result counts
positions/groups; failure to find a placement follows native command failure semantics.
-/

namespace Oria.Std.SpreadPlayers
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Dimension, center coordinates, target selection, and random placement effects. -/
@[expose] public def grade (targets : Target) (center : Vec2) : Grade :=
  ⟨Req.dimension ||| ((encode center).requirements ||| targets.requirements),
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.failure⟩

/-- Spread selected entities. A recorded forceload ticket does not guarantee chunks are
ready; callers must arrange loaded terrain. Numeric settings can carry dynamic I32 holes. -/
public def run (targets : Target) (center : Vec2) (settings : SpreadSettings) :
    Prog (grade targets center) Int32 := do
  emit <| Command.Declarations.spread.call <|
    .cons (encode center) <| .cons (encode settings) <| .cons (encode targets) <| .nil

end Oria.Std.SpreadPlayers
