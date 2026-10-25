module

public import Oria.Proofs.Fixtures.Batch.ContentCommon
public meta import Oria.Proofs.Fixtures.Batch.ContentCommon

namespace Oria.Proofs.Fixtures.Batch
open Oria.Std Oria.Std.Command.Arg

@[mcfunction]
public def giveApples := capture (Give.to .all apple (.static 3))

@[mcfunction]
public def giveNamed := capture (Give.to .self {id := "minecraft:apple", components := [
  .ofNbt "minecraft:custom_name" ("Prize" : String),
  .ofNbt "minecraft:custom_data" (nbt% {round: 2})]} (.static 2))

@[mcfunction]
public def giveRemoved := capture (Give.to .self {id := "minecraft:apple", components := [.remove "minecraft:food"]})

@[mcfunction]
public def clearProbe := capture (Clear.run .all appleMatch (some (.static 0)))

@[mcfunction]
public def clearLimited := capture (Clear.run .all appleMatch (some (.static 1)))

@[mcfunction]
public def clearApples := capture (Clear.run .all appleMatch)

@[mcfunction]
public def clearNamed := capture (Clear.run .self {
  target := some (.id "minecraft:apple")
  tests := [.equal "minecraft:custom_name" (.nbt (.string "Prize"))]} (some (.static 0)))

@[mcfunction]
public def clearData := capture (Clear.run .self {tests := [.matches "minecraft:custom_data" (.nbt (nbt% {round: 2}))]} (some (.static 0)))

@[mcfunction]
public def clearNoFood := capture (Clear.run .self {
  target := some (.id "minecraft:apple")
  tests := [.present "minecraft:food" true]} (some (.static 0)))

@[mcfunction]
public def clearEither := capture (Clear.run .self {tests := [.either (.equal "minecraft:custom_name" (.nbt (.string "Prize")))
  (.present "minecraft:food" true)]} (some (.static 0)))

@[mcfunction]
public def clearCount := capture (Clear.run .self {tests := [.matches "minecraft:count" (.nbt (nbt% {min: 2, max: 2})),
  .present "minecraft:custom_name"]} (some (.static 0)))

@[mcfunction]
public def clearTag := capture (Clear.run .self {target := some (.tag "minecraft:logs")} (some (.static 0)))

@[mcfunction]
public def clearAll := capture (Clear.run .all)

@[mcfunction]
public def itemSet := capture (Item.transfer (chest (.single (.indexed "container" (.static 0)))) (.stack apple (.static 4)))

@[mcfunction]
public def itemReplace := capture (Item.transfer (chest) (.from hands none) .replace)

@[mcfunction]
public def itemFill := capture (Item.transfer (chest) (.from hands none) .fill)

@[mcfunction]
public def itemOverride := capture (Item.transfer (chest) (.from hands none) .override)

@[mcfunction]
public def itemNamedSlots := capture (Item.transfer (chest) (.from ⟨.entity .self, .defined (.named "batch:hands")⟩ none))

@[mcfunction]
public def itemInlineSlots := capture (Item.transfer (chest) (.from ⟨.entity .self, .defined (.ofNbt (nbt% {
  type: "minecraft:slot_range", slots: "weapon.*"}))⟩ none))

@[mcfunction]
public def itemNamedModifier := capture (Item.modify (chest (.single (.indexed "container" (.static 0)))) (.named "batch:add_count"))

@[mcfunction]
public def itemInlineModifier := capture (Item.modify (chest (.single (.indexed "container" (.static 0)))) (.ofNbt
  (nbt% {type: "minecraft:set_count", count: 6})))

@[mcfunction]
public def itemModifiedCopy := capture (Item.transfer (chest (.single (.indexed "container" (.static 1))))
  (.from ⟨.entity .self, .range "weapon.mainhand"⟩ (some (ItemModifier.setCount (.static 2) true))))

@[mcfunction]
public def itemEntity := capture (Item.transfer ⟨.entity (.selector .allPlayers), .range "weapon.offhand"⟩
  (.stack {id := "minecraft:diamond"} (.static 2)))

@[mcfunction]
public def itemEntitySource := capture (Item.transfer (chest) (.from ⟨.entity (.selector .allPlayers), .range "weapon.*"⟩ none) .replace)

@[mcfunction]
public def itemBadSlot := capture (Item.transfer ⟨.entity actor, .range "container.0"⟩ (.stack apple (.static 1)))

@[mcfunction]
public def lootGive := capture (Loot.run (.give .all) (.table (.named "batch:fixed")))

@[mcfunction]
public def lootInline := capture (Loot.run (.give .self) (.table (.ofNbt (nbt% {
  type: "minecraft:chest", pools: [{rolls: 1, entries: [{type: "minecraft:item", name: "minecraft:apple"}]}]}))))

@[mcfunction]
public def lootInsert := capture (Loot.run (.insert (bp 0 0 0)) (.table (.named "batch:fixed")))

@[mcfunction]
public def lootBlock := capture (Loot.run (.replace (.block (bp 0 0 0)) (.indexed "container" (.static 0)) (some (.static 3)))
  (.table (.named "batch:fixed")))

@[mcfunction]
public def lootEntity := capture (Loot.run (.replace (.entity (.selector .allPlayers)) (.named "weapon.mainhand") none)
  (.table (.named "batch:fixed")))

@[mcfunction]
public def lootSpawn := capture (Loot.run (.spawn (.world (.relative (.static 0)) (.relative (.static 1)) (.relative (.static 0))))
  (.table (.named "batch:fixed")))

@[mcfunction]
public def lootMine := capture (Loot.run (.give .self) (.mine (bp 3 0 0) (.item {id := "minecraft:diamond_pickaxe"})))

@[mcfunction]
public def lootMineHeld := capture (Loot.run (.give .self) (.mine (bp 3 0 0) (.held .mainhand)))

@[mcfunction]
public def lootKill := capture (Loot.run (.give .self) (.kill actor))

@[mcfunction]
public def lootFish := capture (Loot.run (.give .self) (.fish (.named "batch:fixed") (bp 3 0 0) .empty))

@[mcfunction]
public def giveDynamic := input (g := playerItemsGrade) fun n => do
  Give.to .self apple (.dynamic n)

@[mcfunction]
public def giveComponentDynamic := input (g := playerItemsGrade) fun n => do
  Give.to .self {id := "minecraft:apple", components := [
  .set "minecraft:custom_data" (.nbtCompound [(⟨"round"⟩, .hole .i32 n)])]} (.static 1)

@[mcfunction]
public def clearDynamic := input (g := playerItemsGrade) fun n => do
  Clear.run .self appleMatch (some (.dynamic n))

@[mcfunction]
public def itemCountDynamic := input (g := blockGrade) fun n => do
  Item.transfer (chest (.single (.indexed "container" (.static 0)))) (.stack apple (.dynamic n))

@[mcfunction]
public def itemSlotDynamic := input (g := blockGrade) fun n => do
  Item.transfer (chest (.single (.indexed "container" (.dynamic n)))) (.stack apple (.static 1))

@[mcfunction]
public def modifierDynamic := input (g := blockGrade) fun n => do
  Item.modify (chest (.single (.indexed "container" (.static 0)))) (ItemModifier.setCount (.dynamic n))

@[mcfunction]
public def lootCountDynamic := input (g := lootGrade) fun n => do
  Loot.run (.replace (.block (bp 0 0 0)) (.indexed "container" (.static 0)) (some (.dynamic n)))
    (.table (.named "batch:fixed"))

@[mcfunction]
public def componentNbt := capture (g := playerItemsGrade) do
  let data ← Nbt.literal (nbt% {round: 9})
  Give.to .self {id := "minecraft:apple", components := [
    .set "minecraft:custom_data" (Nbt.native data)]} (.static 1)

end Oria.Proofs.Fixtures.Batch
