module

public import Oria.Proofs.Fixtures.Batch.Common
public meta import Oria.Proofs.Fixtures.Batch.Common

namespace Oria.Proofs.Fixtures.Batch
open Oria.Std Oria.Std.Command.Arg

@[expose] public def contentEff : EffRow :=
  Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound ||| Eff.failure
@[expose] public def blockGrade : Grade := ⟨Req.dimension ||| Req.position, contentEff⟩
@[expose] public def playerItemsGrade : Grade := ⟨Req.executor, contentEff⟩
@[expose] public def lootGrade : Grade := ⟨Req.all, contentEff⟩

@[expose] public def bp (x y z : Int32) : BlockPos :=
  .world (.relative (.static x)) (.relative (.static y)) (.relative (.static z))
@[expose] public def bx (x y z u v w : Int32) : BlockBox := ⟨bp x y z, bp u v w⟩
@[expose] public def chest (slots : SlotSource := .range "container.*") : Inventory :=
  ⟨.block (bp 0 0 0), slots⟩
@[expose] public def hands : Inventory := ⟨.entity .self, .range "weapon.*"⟩
@[expose] public def apple : ItemSpec := {id := "minecraft:apple"}
@[expose] public def stone : BlockState := {id := "minecraft:stone"}
@[expose] public def oak : BlockState := {id := "minecraft:oak_planks"}
@[expose] public def appleMatch : ItemPredicate := {target := some (.id "minecraft:apple")}
@[expose] public def chestBlock : BlockState := {
  id := "minecraft:chest"
  properties := [("facing", .word "north")] }
@[expose] public def actor : Target := .selector
  (.allEntities {tags := [.include "content.actor"], limit := some 1})

end Oria.Proofs.Fixtures.Batch
