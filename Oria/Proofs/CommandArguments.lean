module

import Oria
import Oria.Std.DP121
import Oria.IR.DP121.Pretty
import Oria.Std.Command.Declarations
import Oria.Std.Compute.Number
import Oria.Command.Pretty
meta import Oria.Command.Literal
meta import Oria
meta import Oria.Std.DP121
meta import Oria.IR.DP121.Pretty
meta import Oria.Std.Compute.Number

namespace Oria.Proofs.CommandArguments

open Oria.Std Oria.Std.Command.Arg

#guard (Command.Literal.decimal 0).format.pretty 120 == "0"
#guard (Command.Literal.decimal (-0.0)).format.pretty 120 == "-0.0"
#guard !((Command.Literal.decimal 1.0e-16).format.pretty 120).contains "e"

private def players : Command.Selector := .allPlayers {
  tags := [.include "rps.playing", .exclude "spectator"]
  scores := [("points", .between 1 4)] }

example : players.requirements = Req.none := rfl
example (tag : String) :
    (Command.Selector.allPlayers {tags := [.include tag]}).requirements = Req.none := by
  simp [Command.Selector.requirements, Command.Selector.Filters.requirements, Req.none]
example : (Command.Selector.allPlayers {sort := some .nearest}).requirements =
    Req.position ||| Req.dimension := rfl
example : (Command.Selector.ofString "@a[tag=rps.playing]").requirements = Req.all := rfl
example : (Command.Selector.allPlayers {
    x := some 1, y := some 2, z := some 3
    distance := some (.atMost 8)}).requirements = Req.dimension := rfl
example : (Command.Selector.allPlayers {x := some 1, distance := some (.atMost 8)}).requirements =
    Req.position ||| Req.dimension := rfl
example : (Command.Selector.allPlayers {
    xRotation := some (.between (-90) 90)
    predicates := [.include "demo:player"]}).requirements = Req.none := rfl
example : (Command.Selector.nearestPlayer {x := some 1, y := some 2, z := some 3}).requirements =
    Req.dimension := rfl
example : (Command.Selector.allPlayers {
    gameMode := some (.exclude .spectator)
    level := some (.atLeast 3)}).requirements = Req.none := rfl
example : (Command.Selector.allPlayers {
    entityType := some (.exclude (.tag "minecraft:undead"))}).requirements = Req.none := rfl

@[mcfunction]
private def selected : Prog (Grade.handled ⟨Req.none,
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random⟩) Unit := do
  Execute.forEach [.as players] do
    Scoreboard.set .self "points" 1

private def render {sig : Command.Signature} (call : Command.Call EncodedVal sig) : Except Diagnostic String := do
  let p ← Std.DP121.plan call
  p.withInvocation
    (fun i => pure ((Target.DP121.Command.invoke i).format.pretty 120))
    (fun _ _ _ i _ => pure ((Target.DP121.Command.invoke i).format.pretty 120))

private def textRequest := Std.Command.Declarations.tellraw.call <|
  .cons (Command.encode (Players.selector players)) <|
  .cons (Command.encode (TextComponent.literal "Ready")) .nil

#guard (render textRequest).toOption = some
  "tellraw @a[tag=rps.playing,tag=!spectator,scores={points=1..4}] {\"text\":\"Ready\"}"

private def typeTagRequest := Std.Command.Declarations.tellraw.call <|
  .cons (Command.encode (Players.selector (.allPlayers {
    entityType := some (.exclude (.tag "minecraft:undead")) }))) <|
  .cons (Command.encode (TextComponent.literal "Ready")) .nil

#guard (render typeTagRequest).toOption = some
  "tellraw @a[type=!#minecraft:undead] {\"text\":\"Ready\"}"

private def position : Vec3 := .world (.absolute 0.0)
  (.absolute 64.25) (.relative (-0.5))
private def teleportRequest := Std.Command.Declarations.teleport.call <|
  .cons (Command.encode Target.self) <| .cons (Command.encode position) .nil

#guard (render teleportRequest).toOption = some "teleport @s 0.0 64.25 ~-0.5"

private def mixedRequest := Std.Command.Declarations.teleport.call <|
  .cons (Command.encode Target.self) <| .cons (Command.encode (Vec3.world
    (.relative (I32.lit 2)) (.absolute 64.25) (.relative (-0.5)))) .nil

#guard (render mixedRequest).toOption = some "teleport @s ~$(p0) 64.25 ~-0.5"

private def centeredRequest := Std.Command.Declarations.teleport.call <|
  .cons (Command.encode Target.self) <| .cons (Command.encode (Vec3.absolute 1 65.25 1)) .nil
private def exactRequest := Std.Command.Declarations.teleport.call <|
  .cons (Command.encode Target.self) <| .cons (Command.encode (Vec3.absolute 1.0 65.25 1.0)) .nil
private def signedZeroRequest := Std.Command.Declarations.teleport.call <|
  .cons (Command.encode Target.self) <| .cons (Command.encode (Vec3.relative (-0.0) 1.25e2 0)) .nil

#guard (render centeredRequest).toOption = some "teleport @s 1 65.25 1"
#guard (render exactRequest).toOption = some "teleport @s 1.0 65.25 1.0"
#guard (render signedZeroRequest).toOption = some "teleport @s ~-0.0 ~125.0 ~0"

private def invalidTagRequest := Std.Command.Declarations.tellraw.call <|
  .cons (Command.encode (Players.selector (.allPlayers {
    tags := [.include "tag,with\"quote"] }))) <|
  .cons (Command.encode (TextComponent.literal "Ready")) .nil

#guard render invalidTagRequest matches .error _
#guard (Command.Literal.unquoted "").check.isOk
#guard (Command.Literal.unquoted "name,limit=1").check matches .error _
#guard (Command.Literal.unquoted "$(name)").check matches .error _
#guard (Command.Literal.quoted "").check.isOk
#guard (Command.Literal.quoted "Name with spaces").check.isOk
#guard (Command.Literal.quoted "line\nline").check matches .error _
#guard (Command.Literal.quoted "$(name)").check matches .error _
#guard (Command.Literal.quoted "A \"quoted\" \\ name$").format.pretty 120 ==
  "\"A \\\"quoted\\\" \\\\ name$\""

example : position.requirements = Req.position := by native_decide

example (n : Scalar) : (Provider.scalar n).requirements = Req.none := by simp
example (id : ResourceId) : (Provider.named id).requirements = Req.all := by simp

@[mcfunction]
private def dynamicConstant (n : Val Int32) : Prog (Compute.grade .default) Int32 := do
  Compute.run .default (.integer (.scalar (.dynamic n)))

@[mcfunction]
private def staticConstant : Prog (Compute.grade .default) Int32 := do
  Compute.run .default (.integer (.ofNbt (7 : Int32)))

private def arithmetic : Calculation :=
  match Calculation.ofNumber ((2 + 3 : NumberProvider.I32) * 4) with
  | .ok value => value
  | .error _ => .integer (.scalar (.static 0))

#guard arithmetic.requirements == Req.none
#guard (NumberProvider.Number.reference (NumberProvider.Ref.named "demo:external") +
  (2 : NumberProvider.I32)).requirements == Req.all

@[mcfunction]
private def typedCalculation : Prog (Compute.grade .default arithmetic.requirements) Int32 := do
  Compute.run .default arithmetic

#guard typedCalculation.signature.grade.req == Req.position ||| Req.dimension
#guard dynamicConstant.signature.grade.req == Req.position ||| Req.dimension

end Oria.Proofs.CommandArguments
