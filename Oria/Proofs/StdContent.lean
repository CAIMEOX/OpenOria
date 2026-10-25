module

import Oria
import Oria.Std.DP121
import Oria.IR.DP121.Pretty
meta import Oria
meta import Oria.Std.DP121
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.StdContent
open Oria.Std Oria.Std.Command.Arg

example (n : Scalar) (add : Bool) : (ItemModifier.setCount n add).requirements = Req.none := by simp
example (b : BlockState) : (Command.encode b).requirements = b.requirements := rfl
example (b : BlockPredicate) : (Command.encode b).requirements = b.requirements := rfl
example (s : Slot) : (Command.encode s).requirements = Req.none := rfl

example : (Item.grade ⟨.entity .self, .range "weapon.mainhand"⟩).req =
    Req.dimension ||| Req.position ||| Req.executor := rfl

private def render {sig : Command.Signature} (call : Command.Call EncodedVal sig) :
    Except Diagnostic String := do
  let p ← Std.DP121.plan call
  p.withInvocation
    (fun i => pure ((Target.DP121.Command.invoke i).format.pretty 120))
    (fun _ _ _ i _ => pure ((Target.DP121.Command.invoke i).format.pretty 120))

private def give := Command.Declarations.giveItems.call <|
  .cons (Command.encode Players.self) <|
  .cons (Command.encode ({id := "minecraft:apple", components := [
    .ofNbt "minecraft:custom_data" (nbt% {round: 2}),
    .remove "minecraft:food"]} : ItemSpec)) <|
  .cons (Command.encode (Scalar.static 3)) .nil

#guard (render give).toOption =
  some "give @s minecraft:apple[minecraft:custom_data={\"round\":2},!minecraft:food] 3"

private def condition := Command.Declarations.clearItemsLimit.call <|
  .cons (Command.encode Players.self) <|
  .cons (Command.encode ({tests := [.either (.present "minecraft:food" true)
    (.matches "minecraft:custom_data" (.nbt (nbt% {round: 2})))]} : ItemPredicate)) <|
  .cons (Command.encode (Scalar.static 0)) .nil

#guard (render condition).toOption =
  some "clear @s *[!minecraft:food|minecraft:custom_data~{\"round\":2}] 0"

private def pos : BlockPos :=
  .world (.absolute (.static 0)) (.absolute (.static 64)) (.absolute (.static 0))

private def place := Command.Declarations.setBlock.call <|
  .cons (Command.encode pos) <|
  .cons (Command.encode ({
    id := "minecraft:chest"
    properties := [("facing", .word "north")]
    data := some (.value (nbt% {}))} : BlockState)) <|
  .cons (Command.encode SetBlockMode.strict) .nil

#guard (render place).toOption = some "setblock 0 64 0 minecraft:chest[facing=north]{} strict"

end Oria.Proofs.StdContent
