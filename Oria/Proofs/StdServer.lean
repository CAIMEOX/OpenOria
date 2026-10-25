module

import Oria
import Oria.Std.DP121
import Oria.IR.DP121.Pretty
meta import Oria
meta import Oria.Std.DP121
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.StdServer
open Oria.Std Oria.Std.Command.Arg

example (d : Destination) : (Command.encode d).requirements = Req.none := by simp
example (s : Scores) : (Command.encode s).requirements = s.holders.requirements := by
  simp [Scores.requirements]
example : (Profiles.named "Alex").requirements = Req.none := rfl
example : (Profiles.players .self).requirements = Req.executor := rfl
example (p : Players) : (Profiles.players p).requirements = p.requirements := rfl
example : (Admin.Transfer.grade .self).req = Req.executor := rfl
example : (Admin.Transfer.grade .all).req = Req.none := rfl
example : (Admin.Kick.grade .all (some "Maintenance")).req = Req.none := by
  simp [Admin.Kick.grade, Players.requirements, Req.none]
  rfl
example : Admin.Tick.grade.req = Req.none := rfl
example (t : TickAction) : (Command.encode t).requirements = Req.none := by simp

private def render {sig : Command.Signature} (call : Command.Call EncodedVal sig) : Except Diagnostic String := do
  let p ← Std.DP121.plan call
  p.withInvocation
    (fun i => pure ((Target.DP121.Command.invoke i).format.pretty 120))
    (fun _ _ _ i _ => pure ((Target.DP121.Command.invoke i).format.pretty 120))


private def destination := Std.Command.Declarations.transfer.call <|
  .cons (Command.encode ({host := "play.example.invalid", port := .dynamic 25565} : Destination)) <|
  .cons (Command.encode Players.all) .nil
#guard (render destination).toOption = some "transfer \"play.example.invalid\" $(p0) @a"

private def ipv4 := Std.Command.Declarations.pardonIp.call <|
  .cons (Command.encode (_root_.Std.Net.IPv4Addr.ofParts 192 0 2 1)) .nil
#guard (render ipv4).toOption = some "pardon-ip 192.0.2.1"

end Oria.Proofs.StdServer
