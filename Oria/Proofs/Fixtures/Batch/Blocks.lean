module

public import Oria.Proofs.Fixtures.Batch.ContentCommon
public meta import Oria.Proofs.Fixtures.Batch.ContentCommon

namespace Oria.Proofs.Fixtures.Batch
open Oria.Std Oria.Std.Command.Arg

@[mcfunction]
public def placeChest := capture (Setblock.set (bp 0 0 0) chestBlock)

@[mcfunction]
public def turnChest := capture (Setblock.set (bp 0 0 0) {chestBlock with properties := [("facing", .word "east")]})

@[mcfunction]
public def clearChestData := capture (Setblock.set (bp 0 0 0) {chestBlock with data := some (.value (nbt% {}))})

@[mcfunction]
public def placeStone := capture (Setblock.set (bp 3 0 0) stone)

@[mcfunction]
public def placeKeep := capture (Setblock.set (bp 3 0 0) oak .keep)

@[mcfunction]
public def placeDestroy := capture (Setblock.set (bp 3 0 0) oak .destroy)

@[mcfunction]
public def placeStrict := capture (Setblock.set (bp 3 0 0) stone .strict)

@[mcfunction]
public def fillStone := capture (Fill.run (bx 3 0 0 5 0 0) stone)

@[mcfunction]
public def fillFiltered := capture (Fill.run (bx 3 0 0 5 0 0) oak (.replace (some {id := .id "minecraft:stone"}) .strict))

@[mcfunction]
public def fillTag := capture (Fill.run (bx 3 0 0 5 0 0) stone (.replace (some {id := .tag "minecraft:planks"})))

@[mcfunction]
public def fillKeep := capture (Fill.run (bx 3 0 0 5 0 0) oak .keep)

@[mcfunction]
public def fillDestroy := capture (Fill.run (bx 3 0 0 5 0 0) oak (.replace none .destroy))

@[mcfunction]
public def fillCube := capture (Fill.run (bx 0 0 4 2 2 6) stone)

@[mcfunction]
public def fillOutline := capture (Fill.run (bx 0 0 4 2 2 6) oak (.replace none .outline))

@[mcfunction]
public def fillHollow := capture (Fill.run (bx 0 0 4 2 2 6) stone (.replace none .hollow))

@[mcfunction]
public def cloneNormal := capture (Clone.run {source := bx 3 0 0 5 0 0, destination := bp 8 0 0})

@[mcfunction]
public def cloneMasked := capture (Clone.run {source := bx 3 0 0 5 0 0, destination := bp 8 0 0, filter := .masked})

@[mcfunction]
public def cloneFiltered := capture (Clone.run {
  source := bx 3 0 0 5 0 0
  destination := bp 8 0 0
  filter := .filtered {id := .tag "minecraft:planks"}
  strict := true})

@[mcfunction]
public def cloneOverlap := capture (Clone.run {source := bx 3 0 0 5 0 0, destination := bp 4 0 0})

@[mcfunction]
public def cloneForce := capture (Clone.run {source := bx 3 0 0 5 0 0, destination := bp 4 0 0, mode := .force})

@[mcfunction]
public def cloneMove := capture (Clone.run {source := bx 3 0 0 5 0 0, destination := bp 8 0 0, mode := .move})

@[mcfunction]
public def cloneChest := capture (Clone.run {source := bx 0 0 0 0 0 0, destination := bp 1 0 0})

@[mcfunction]
public def cloneDimensions := capture (Clone.run {
  source := bx 3 0 0 5 0 0
  destination := bp 8 0 0
  sourceDimension := some "minecraft:overworld"
  targetDimension := some "minecraft:overworld"
  strict := true})

@[mcfunction]
public def cloneCrossDimension := capture (Clone.run {
  source := bx 3 0 0 5 0 0
  destination := .world (.absolute (.static 0)) (.absolute (.static 64)) (.absolute (.static 0))
  targetDimension := some "minecraft:the_nether"
  strict := true })

@[mcfunction]
public def fillProperties := capture (Fill.run (bx 3 0 0 5 0 0) stone (.replace
  (some {id := .id "minecraft:oak_log", properties := [("axis", .word "x")]})))

@[mcfunction]
public def propertyDynamic := input (g := blockGrade) fun n => do
  Setblock.set (bp 3 0 0) {id := "minecraft:light", properties := [("level", .number (.dynamic n))]}

@[mcfunction]
public def fillDynamic := input (g := blockGrade) fun n => do
  Fill.run ⟨bp 3 0 0, .world (.relative (.dynamic n)) (.relative (.static 0)) (.relative (.static 0))⟩ stone

@[mcfunction]
public def blockNbt := capture (g := blockGrade) do
  let data ← Nbt.literal (nbt% {})
  Setblock.set (bp 0 0 0) {chestBlock with data := some (.dynamic data)}

end Oria.Proofs.Fixtures.Batch
