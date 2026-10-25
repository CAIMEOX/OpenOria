module

public import Oria.Std.Command.Arg.Gameplay
import Oria.Std.Command.Declarations.Player
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Advancement

Scopes select all advancements, one advancement/criterion, or graph traversal from, until,
or through an advancement. Grant executes native rewards, including external functions.
A reward calling an active pack's public entry receives native failure before the entry
touches its registers or invocation arena. Defer the next Oria entry until this invocation
has returned. The command's effect bound includes all current observable effect labels.
-/

namespace Oria.Std.Advancement

open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Target requirements and all current effects, accounting for external reward functions. -/
@[expose] public def grade (targets : Players) : Grade :=
  ⟨targets.requirements,
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud |||
      Eff.chat ||| Eff.sound ||| Eff.dialog ||| Eff.persistentRead ||| Eff.persistentWrite |||
      Eff.persistentAlloc ||| Eff.failure⟩

/-- Grant selected progress and execute native rewards. Unknown criteria and unchanged
progress fail. Results retain native advancement/criterion modification counts. -/
public def grant (targets : Players) (scope : AdvancementScope) :
    Prog (grade targets) Int32 := do
  emit <| Command.Declarations.advancementGrant.call <|
    .cons (encode targets) <| .cons (encode scope) <| .nil

/-- Revoke selected progress. Rewards already issued are not rolled back. -/
public def revoke (targets : Players) (scope : AdvancementScope) :
    Prog ⟨targets.requirements,
      Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.chat ||| Eff.failure⟩
      Int32 := do
  emit <| Command.Declarations.advancementRevoke.call <|
    .cons (encode targets) <| .cons (encode scope) <| .nil

end Oria.Std.Advancement
