module

import Oria
import Oria.Std.DP121
import Oria.IR.DP121.Pretty
import Oria.Std.Command.Declarations.Generation
meta import Oria
meta import Oria.Std.DP121
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.StdGeneration
open Oria.Std Oria.Std.Command.Arg

example : Stopwatch.grade.req = Req.none := rfl
example : (Waypoint.grade .self).req = Req.dimension ||| Req.executor := rfl
example : (Place.grade .here).req = Req.dimension ||| Req.position := rfl
example : (Place.grade (.world (.absolute (.static 1)) (.absolute (.static 2))
    (.absolute (.static 3)))).req = Req.dimension := rfl
example (id : ResourceId) : (Feature.named id).requirements = Req.none := by simp
example (f : Command.Fragment EncodedVal) : (Feature.inline f).requirements = f.requirements := by simp
example (settings : TemplateSettings) : (Command.encode settings).requirements = Req.none := by simp
example (property : WaypointProperty) : (Command.encode property).requirements = Req.none := by simp

private def known : Feature := .named "demo:feature"
example : known.requirements = Req.none := by simp [known]

#guard (HexColor.parse "F0a").isOk
#guard (HexColor.parse "6495ED").isOk
#guard !(HexColor.parse "#6495ED").isOk
#guard !(HexColor.parse "1234").isOk
#guard !(HexColor.parse "red").isOk
#guard !(HexColor.parse "0\n0").isOk

private def render {sig : Command.Signature} (call : Command.Call EncodedVal sig) : Except Diagnostic String := do
  let p ← Std.DP121.plan call
  p.withInvocation
    (fun i => pure ((Target.DP121.Command.invoke i).format.pretty 120))
    (fun _ _ _ i _ => pure ((Target.DP121.Command.invoke i).format.pretty 120))

private def templateRequest := Std.Command.Declarations.placeTemplate.call <|
  .cons (Command.encode (ResourceId.ofString "demo:room")) <| .cons (Command.encode BlockPos.here) <|
  .cons (Command.encode ({
    rotation := .clockwise90, mirror := .frontBack
    integrity := .decimal 0.5, seed := .static 7, strict := true} : TemplateSettings)) .nil

#guard (render templateRequest).toOption =
  some "place template demo:room ~0 ~0 ~0 clockwise_90 front_back 0.5 7 strict"

private def waypointRequest := Std.Command.Declarations.waypointModify.call <|
  .cons (Command.encode Target.self) <|
  .cons (Command.encode (WaypointProperty.hex "f0A")) .nil

#guard (render waypointRequest).toOption =
  some "waypoint modify @s color hex f0A"

private def stopwatchRequest := Std.Command.Declarations.stopwatchQuery.call <|
  .cons (Command.encode (ResourceId.ofString "demo:lap")) <|
  .cons (Command.encode (Decimal.static (-1000))) .nil

#guard (render stopwatchRequest).toOption =
  some "stopwatch query demo:lap -1000"

end Oria.Proofs.StdGeneration
