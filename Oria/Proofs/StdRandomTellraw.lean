module

import Oria
import Oria.Std.Random
import Oria.Std.Tellraw
import Oria.Std.Command.Declarations
import Oria.Std.DP121
import Oria.IR.DP121.Pretty
meta import Oria
meta import Oria.Std.Random
meta import Oria.Std.Tellraw
meta import Oria.Std.DP121
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.StdRandomTellraw

open Oria.Std Oria.Std.Command.Arg

@[mcfunction]
private def draw (lo hi : Val Int32) : Prog (Random.grade none) Int32 :=
  Random.value (.between (.dynamic lo) (.dynamic hi))

@[mcfunction]
private def reset (seed : Val Int32) : Prog (Random.resetGrade (.one (.ofString "demo:roll"))) Int32 :=
  Random.reset (.one (.ofString "demo:roll")) (some {value := .dynamic seed, includeWorldSeed := false})

@[mcfunction]
private def message : Prog (Tellraw.grade Players.all Req.all) Int32 :=
  Tellraw.send .all (nbt% {text: "Hello", color: "gold", bold: true,
    hover_event: {action: "show_text", value: "Details"}})

@[mcfunction]
private def number (n : Val Int32) : Prog (Tellraw.grade Players.self) Int32 :=
  Tellraw.number .self (.dynamic n)

example : draw.signature.grade = Random.grade none := rfl
example : reset.signature.grade = Random.resetGrade (.one (.ofString "demo:roll")) := rfl
example : message.signature.grade = Tellraw.grade Players.all Req.all := rfl
example : number.signature.grade = Tellraw.grade Players.self := rfl

example : (Tellraw.grade Players.all).req = Req.none := rfl
example : (Tellraw.grade Players.self).req = Req.executor := rfl
example : (Tellraw.grade Players.all Req.all).req = Req.all := rfl
example : (Tellraw.grade Players.all).req ||| Req.server = Req.server := by decide
example : ¬((Tellraw.grade Players.self).req ||| Req.server = Req.server) := by decide
example : ¬((Tellraw.grade Players.all Req.all).req ||| Req.server = Req.server) := by decide

example (text : String) :
    (Command.encode (TextComponent.literal text)).requirements = Req.none :=
  TextComponent.encode_requirements _
example (n : Val Int32) :
    (Command.encode (TextComponent.number (.dynamic n))).requirements = Req.none :=
  TextComponent.encode_requirements _
example (value : Nbt.Any) :
    (Command.encode (TextComponent.raw value)).requirements = Req.all :=
  TextComponent.encode_requirements _

@[mcfunction]
private def scopedMessage : Prog (Grade.handled (Tellraw.grade Players.all)) Unit := do
  Execute.forEach [.as .allPlayers] do
    Tellraw.number .self (.static 1)

example : scopedMessage.signature.grade.req = Req.none := rfl

example : Prog (Random.rollGrade (some (.ofString "demo:dice"))) Int32 :=
  Random.roll (.between (.static 1) (.static 6)) (some (.ofString "demo:dice"))

example : Prog (Random.resetGrade .all) Int32 := Random.reset .all
example : Prog (Random.resetGrade .all) Int32 :=
  Random.reset .all (some {value := .static 42, includeWorldSeed := false, includeSequenceId := false})

example : Prog (Tellraw.grade (Players.ofString "@a[name=\"round one\"]")) Int32 :=
  Tellraw.text (Players.ofString "@a[name=\"round one\"]") "Quoted \"message\" $(literal)"

private def rendered {sig : Command.Signature}
    (request : Command.Call EncodedVal sig) : Except Diagnostic (String × Nat) := do
  let p ← Std.DP121.plan request
  p.withInvocation
    (fun i => pure ((Target.DP121.Command.invoke i).format.pretty 120, 0))
    (fun schema _ _ i _ => pure ((Target.DP121.Command.invoke i).format.pretty 120, schema.fields.length))

private def drawRequest (range : Range) :=
  Std.Command.Declarations.randomValue.call (.cons (Command.encode range) .nil)

#guard (rendered (drawRequest (.between (.static (-3)) (.static 9)))).toOption =
  some ("random value -3..9", 0)
#guard (rendered (drawRequest (.atLeast (.static 0)))).toOption = some ("random value 0..", 0)
#guard (rendered (drawRequest (.atMost (.static 9)))).toOption = some ("random value ..9", 0)
#guard (rendered (drawRequest .any)).toOption = some ("random value ..", 0)
#guard (rendered (drawRequest (.between (.dynamic 1) (.static 9)))).toOption =
  some ("random value $(p0)..9", 1)

private def namedRoll := Std.Command.Declarations.randomRollSequence.call <|
  .cons (Command.encode (.between (.static 1) (.static 6) : Range)) <|
  .cons (Command.encode (ResourceId.ofString "demo:dice")) .nil

#guard (rendered namedRoll).toOption = some ("random roll 1..6 demo:dice", 0)

private def configuredReset := Std.Command.Declarations.randomResetSeed.call <|
  .cons (Command.encode Sequences.all) <|
  .cons (Command.encode (Seed.mk (.static 42) true false)) .nil

#guard (rendered configuredReset).toOption = some ("random reset * 42 true false", 0)

private def tell (component : TextComponent) :=
  Std.Command.Declarations.tellraw.call <|
    .cons (Command.encode Players.all) <| .cons (Command.encode component) .nil

#guard (rendered (tell (.literal "Loaded"))).toOption =
  some ("tellraw @a {\"text\":\"Loaded\"}", 0)
#guard (rendered (tell (.number (.dynamic 12)))).toOption =
  some ("tellraw @a {\"translate\":\"%s\",\"with\":[$(p0)]}", 1)

end Oria.Proofs.StdRandomTellraw
