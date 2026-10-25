module

import Oria
import Oria.Std.Command.Declarations
import Oria.Std.DP121
import Oria.IR.DP121.Pretty
meta import Oria
meta import Oria.Std.DP121
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.StdScoreboardTrigger

open Oria.Std Oria.Std.Command.Arg

example (criterion : Criterion) : (Command.encode criterion).requirements = Req.none :=
  criterion.encode_requirements
example : Scoreboard.objectiveGrade.req = Req.none := rfl
example : (Scoreboard.enableGrade .self).req = Req.executor := rfl
example : (Scoreboard.enableGrade (.named "#input")).req = Req.none := rfl
example : Trigger.grade.req = Req.executor := rfl
example : Scoreboard.objectiveGrade.req ||| Req.server = Req.server := by decide
example : ¬(Trigger.grade.req ||| Req.server = Req.server) := by decide

@[mcfunction]
private def scopedTrigger : Prog
    ⟨Req.none, Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random⟩ Unit := do
  Execute.forEach [.as .allPlayers] do
    Trigger.run "game.choice"

example : scopedTrigger.signature.grade.req = Req.none := rfl

private def rendered {sig : Command.Signature} (request : Command.Call EncodedVal sig) :
    Except Diagnostic (String × Nat) := do
  let plan ← Std.DP121.plan request
  plan.withInvocation
    (fun invocation => pure ((Target.DP121.Command.invoke invocation).format.pretty 120, 0))
    (fun schema _ _ invocation _ =>
      pure ((Target.DP121.Command.invoke invocation).format.pretty 120, schema.fields.length))

private def objective : Command.Objective := "game.choice"
private def add (criterion : Criterion) := Std.Command.Declarations.objectiveAdd.call <|
  .cons (Command.encode objective) <| .cons (Command.encode criterion) .nil

#guard (rendered (add .dummy)).toOption = some ("scoreboard objectives add game.choice dummy", 0)
#guard (rendered (add .trigger)).toOption = some ("scoreboard objectives add game.choice trigger", 0)
#guard (rendered (add (.named "minecraft.used:minecraft.carrot_on_a_stick"))).toOption =
  some ("scoreboard objectives add game.choice minecraft.used:minecraft.carrot_on_a_stick", 0)

private def reset := Std.Command.Declarations.scoreReset.call <|
  .cons (Command.encode ScoreHolder.self) <| .cons (Command.encode objective) .nil
private def enable := Std.Command.Declarations.scoreEnable.call <|
  .cons (Command.encode (ScoreHolder.named "#input")) <| .cons (Command.encode objective) .nil
private def set (value : Scalar) := Std.Command.Declarations.triggerSet.call <|
  .cons (Command.encode objective) <| .cons (Command.encode value) .nil
private def increment (value : Scalar) := Std.Command.Declarations.triggerAdd.call <|
  .cons (Command.encode objective) <| .cons (Command.encode value) .nil

#guard (rendered reset).toOption = some ("scoreboard players reset @s game.choice", 0)
#guard (rendered enable).toOption = some ("scoreboard players enable #input game.choice", 0)
#guard (rendered (set (.static 0))).toOption = some ("trigger game.choice set 0", 0)
#guard (rendered (set (.dynamic 12))).toOption = some ("trigger game.choice set $(p0)", 1)
#guard (rendered (increment (.static (-1)))).toOption = some ("trigger game.choice add -1", 0)
#guard (rendered (increment (.dynamic 12))).toOption = some ("trigger game.choice add $(p0)", 1)

end Oria.Proofs.StdScoreboardTrigger
