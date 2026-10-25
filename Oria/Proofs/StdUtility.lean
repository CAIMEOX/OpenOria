module

import Oria
import Oria.Std.DP121
import Oria.IR.DP121.Pretty
meta import Oria
meta import Oria.Std.DP121
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.StdUtility
open Oria.Std Oria.Std.Command.Arg

example : Locate.grade.req = Req.position ||| Req.dimension := rfl
example : (ServerInfo.grade).req = Req.none := rfl
example : (ServerInfo.grade Req.dimension).req = Req.dimension := rfl
example : (Chat.grade "Hello").req = Req.none := by simp [Chat.grade, Req.none]
example : (Chat.grade "Hello" Req.executor).req = Req.executor := by simp [Chat.grade, Req.none]
example (s : Command.Selector) : (Message.selector s).requirements = s.requirements := by simp
example (n : Scalar) : (Message.number n).requirements = Req.none := by simp
example (a : Message) (bs : List Message) :
    (Message.join a bs).requirements =
      a.requirements ||| (bs.map (·.requirements)).foldr (· ||| ·) Req.none := by simp
example : (Message.join (.selector .allPlayers) ["[distance=..1]"]).requirements = Req.none := by
  simp [Command.Selector.requirements, Command.Selector.Filters.requirements, Req.none]
example : (Message.native "Hi @s").requirements = Req.all := by simp
example : (Scoreboard.updateGrade (.one .self)).req = Req.executor := rfl
example : (Scoreboard.updateGrade .all).req = Req.none := rfl

#guard (Message.parse "Hi").isOk
#guard !(Message.parse "").isOk
#guard !(Message.parse "   ").isOk
#guard !(Message.parse "Hi @s").isOk
#guard !(Message.parse "x\ny").isOk
#guard !(Message.parse "$(x)").isOk

private def render {sig : Command.Signature} (call : Command.Call EncodedVal sig) : Except Diagnostic String := do
  let p ← Std.DP121.plan call
  p.withInvocation
    (fun i => pure ((Target.DP121.Command.invoke i).format.pretty 120))
    (fun _ _ _ i _ => pure ((Target.DP121.Command.invoke i).format.pretty 120))

private def joined := Std.Command.Declarations.chatSay.call <|
  .cons (Command.encode (Message.join "Hi" [.selector .self, .number (.static 7)])) .nil
#guard (render joined).toOption = some "say Hi @s 7"

private def separated := Std.Command.Declarations.chatSay.call <|
  .cons (Command.encode (Message.join (.selector .allPlayers) ["[distance=..1]"])) .nil
#guard (render separated).toOption = some "say @a [distance=..1]"

private def locateTag := Std.Command.Declarations.locatePoi.call <|
  .cons (Command.encode (Command.ResourceOrTag.tag "demo:poi")) .nil
#guard (render locateTag).toOption = some "locate poi #demo:poi"

private def dynamicNumber := Std.Command.Declarations.chatSay.call <|
  .cons (Command.encode (Message.join "Count" [.number (.dynamic 4)])) .nil
#guard (render dynamicNumber).toOption = some "say Count $(p0)"

end Oria.Proofs.StdUtility
