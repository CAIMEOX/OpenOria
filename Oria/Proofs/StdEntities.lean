module

import Oria
import Oria.Std.Command.Declarations
import Oria.Std.DP121
import Oria.IR.DP121.Pretty
meta import Oria
meta import Oria.Std.DP121
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.StdEntities

open Oria.Std Oria.Std.Command.Arg

example (duration : Duration) : (Command.encode duration).requirements = Req.none := by simp
example (flag : Bool) : (Command.encode flag).requirements = Req.none := by simp
example {r : Region} (value : Val (Nbt.Data (some .compound)) r) :
    (Compound.dynamic value).requirements = Req.none := rfl
example : (Kill.grade .self).req = Req.dimension ||| Req.executor := rfl
example : (Effect.grade .self).req = Req.executor := rfl
example : (Effect.grade (.selector .allPlayers)).req = Req.none := rfl
example : Summon.grade.req = Req.dimension ||| Req.position := rfl
example : Summon.grade.req ||| Req.server = Req.server := by decide

@[mcfunction]
private def empower : Prog (Grade.handled (Effect.grade (.selector .allPlayers))) Unit :=
  (Effect.give (.selector .allPlayers) "minecraft:speed").ignore

@[mcfunction]
private def scopedEffects : Prog (Grade.handled (Effect.grade (.selector .allPlayers))) Unit := do
  Execute.forEach [.as .allPlayers] do
    Effect.giveFor .self "minecraft:speed" (.finite (.static 10))

private def rendered {sig : Command.Signature} (call : Command.Call EncodedVal sig) :
    Except Diagnostic (String × Nat) := do
  let plan ← Std.DP121.plan call
  plan.withInvocation
    (fun i => pure ((Target.DP121.Command.invoke i).format.pretty 120, 0))
    (fun schema _ _ i _ => pure ((Target.DP121.Command.invoke i).format.pretty 120, schema.fields.length))

private def selection : Target := .selector (.allEntities { tags := [.include "temporary"] })
private def kill := Std.Command.Declarations.kill.call <|
  .cons (Command.encode selection) .nil
#guard (rendered kill).toOption = some ("kill @e[tag=temporary]", 0)

private def position : Vec3 := .world (.relative (.dynamic 1))
  (.absolute (.decimal 64.25)) (.relative (.decimal (-0.5)))
private def data : Compound := .fields [
  (⟨"Age"⟩, .hole .i32 (2 : Val Int32)),
  (⟨"Tags"⟩, .nbt (nbt% ["temporary"]))]
private def summon := Std.Command.Declarations.summonData.call <|
  .cons (Command.encode (ResourceId.ofString "minecraft:pig")) <|
  .cons (Command.encode position) <| .cons (Command.encode data) .nil
#guard (rendered summon).toOption = some
  ("summon minecraft:pig ~$(p0) 64.25 ~-0.5 {\"Age\":$(p1),\"Tags\":[\"temporary\"]}", 2)

private def give (duration : Duration) := Std.Command.Declarations.effectGiveFor.call <|
  .cons (Command.encode Target.self) <|
  .cons (Command.encode (ResourceId.ofString "minecraft:speed")) <|
  .cons (Command.encode duration) <| .cons (Command.encode (Scalar.dynamic 2)) <|
  .cons (Command.encode true) .nil
#guard (rendered (give .infinite)).toOption =
  some ("effect give @s minecraft:speed infinite $(p0) true", 1)
#guard (rendered (give (.finite (.dynamic 1)))).toOption =
  some ("effect give @s minecraft:speed $(p0) $(p1) true", 2)

end Oria.Proofs.StdEntities
