module

public import Oria.Proofs.Fixtures.Batch.ControlCommon
public meta import Oria.Proofs.Fixtures.Batch.ControlCommon

namespace Oria.Proofs.Fixtures.Batch
open Oria.Std Oria.Std.Command.Arg

@[mcfunction]
public def ruleRead := capture (Gamerule.get .keepInventory)

@[mcfunction]
public def ruleOn := capture (Gamerule.set .keepInventory true)

@[mcfunction]
public def ruleOff := capture (Gamerule.set .keepInventory false)

@[mcfunction]
public def ruleRandomRead := capture (Gamerule.get .randomTickSpeed)

@[mcfunction]
public def attrGet := capture (Attribute.run rider "minecraft:max_health" (.get (.static 10)))

@[mcfunction]
public def attrNegative := capture (Attribute.run rider "minecraft:max_health" (.get (.static (-10))))

@[mcfunction]
public def attrBase := capture (Attribute.run rider "minecraft:max_health" (.base (.static 10)))

@[mcfunction]
public def attrSet := capture (Attribute.run rider "minecraft:max_health" (.set (.decimal 16.5)))

@[mcfunction]
public def attrReset := capture (Attribute.run rider "minecraft:max_health" .reset)

@[mcfunction]
public def attrAdd := capture (Attribute.run rider "minecraft:max_health" (.add "batch:add" (.static 2) .add))

@[mcfunction]
public def attrMultiplyBase := capture (Attribute.run rider "minecraft:max_health" (.add "batch:base" (.decimal 0.5) .multiplyBase))

@[mcfunction]
public def attrMultiplyTotal := capture (Attribute.run rider "minecraft:max_health" (.add "batch:total" (.static 1) .multiplyTotal))

@[mcfunction]
public def attrModifier := capture (Attribute.run rider "minecraft:max_health" (.modifier "batch:base" (.static 100)))

@[mcfunction]
public def attrRemove := capture (Attribute.run rider "minecraft:max_health" (.remove "batch:add"))

@[mcfunction]
public def attrRemoveBase := capture (Attribute.run rider "minecraft:max_health" (.remove "batch:base"))

@[mcfunction]
public def attrRemoveTotal := capture (Attribute.run rider "minecraft:max_health" (.remove "batch:total"))

@[mcfunction]
public def attrMissing := capture (Attribute.run rider "minecraft:block_interaction_range" (.get (.static 1)))

@[mcfunction]
public def loadAdd := capture (Forceload.run (.add column none))

@[mcfunction]
public def loadRange := capture (Forceload.run (.add column (some ⟨.absolute (.static 31), .absolute (.static 15)⟩)))

@[mcfunction]
public def loadQuery := capture (Forceload.run (.query column))

@[mcfunction]
public def loadList := capture (Forceload.run .list)

@[mcfunction]
public def loadRemove := capture (Forceload.run (.remove column none))

@[mcfunction]
public def loadRemoveRange := capture (Forceload.run (.remove column (some ⟨.absolute (.static 31), .absolute (.static 15)⟩)))

@[mcfunction]
public def loadClear := capture (Forceload.run .clear)

@[mcfunction]
public def ruleDynamic := input (g := Gamerule.grade) fun n => do
  Gamerule.set .randomTickSpeed (.dynamic n)

@[mcfunction]
public def attrDynamic := input (g := Attribute.grade rider) fun n => do
  Attribute.run rider "minecraft:max_health" (.set (.dynamic n))

@[mcfunction]
public def loadDynamic := input (g := ⟨Req.dimension, Eff.world ||| Eff.failure⟩) fun n => do
  Forceload.run (.add column (some ⟨.absolute (.dynamic n), .absolute (.static 0)⟩))

end Oria.Proofs.Fixtures.Batch
