module

public import Oria.Std.Command.Arg.Control
import Oria.Std.Command.Declarations.Control
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Swing

Animate living entities' main or off hand. DP121 supports none, whack, and stab animations
with a positive native time duration. Non-living targets are skipped; a wholly ineligible
selection fails. Results count living targets, independently of client rendering.
-/

namespace Oria.Std.Swing
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Entity-selection requirements and gameplay/animation effects. -/
@[expose] public def grade (targets : Target) : Grade :=
  ⟨targets.requirements,
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.failure⟩

/-- Swing selected living entities' hands. Settings default to mainhand, whack, and six ticks.
Dynamic durations are checked by the native parser when the macro is invoked. -/
public def run (targets : Target := .self) (settings : SwingSettings := {}) :
    Prog (grade targets) Int32 := do
  emit <| Command.Declarations.swing.call <|
    .cons (encode targets) <| .cons (encode settings) <| .nil

end Oria.Std.Swing
