module

public import Oria.Proofs.Fixtures.Batch.ContentCommon
public meta import Oria.Proofs.Fixtures.Batch.ContentCommon

namespace Oria.Proofs.Fixtures.Batch
open Oria.Std Oria.Std.Command.Arg

@[expose] public def executionHits : ScoreSlot := ⟨.named "#hits", points⟩
@[expose] public def executionOne : ScoreSlot := ⟨.named "#one", points⟩
private def probe (steps : List (Execute.Step EncodedVal)) :=
  Execute.forEach steps (Scoreboard.operation executionHits .add executionOne)

@[mcfunction]
public def execBlock := probe [.when (.block (bp 0 0 0) {id := .id "minecraft:chest", properties := [("facing", .word "north")]})]

@[mcfunction]
public def execBlockTag := probe [.when (.block (bp 1 0 0) {id := .tag "minecraft:logs"})]

@[mcfunction]
public def execBlockNbt := probe [.when (.block (bp 0 0 0) {id := .id "minecraft:chest", data := some (.value (nbt% {Items: []}))})]

@[mcfunction]
public def execBlocks := probe [.when (.blocks (bx 1 0 0 2 0 0) (bp 4 0 0) .all)]

@[mcfunction]
public def execMasked := probe [.when (.blocks (bx 1 0 0 2 0 0) (bp 4 0 0) .masked)]

@[mcfunction]
public def execBiome := probe [.when (.biome (bp 0 0 0) (.id "minecraft:plains"))]

@[mcfunction]
public def execBiomeTag := probe [.when (.biome (bp 0 0 0) (.tag "minecraft:is_overworld"))]

@[mcfunction]
public def execDimension := probe [.when (.dimension "minecraft:overworld")]

@[mcfunction]
public def execOtherDimension := probe [.unless (.dimension "minecraft:overworld")]

@[mcfunction]
public def execLoaded := probe [.when (.loaded (bp 0 0 0))]

@[mcfunction]
public def execNotLoaded := probe [.unless (.loaded (.world (.absolute (.static 1000000)) (.absolute (.static 64)) (.absolute (.static 1000000))))]

@[mcfunction]
public def execSlots := probe [.when (.slots (chest (.single (.named "container.1"))))]

@[mcfunction]
public def execNoSlots := probe [.when (.slots (chest (.single (.named "container.53"))))]

@[mcfunction]
public def execItems := probe [.when (.items (chest (.range "container.*")) appleMatch)]

@[mcfunction]
public def execHands := probe [.when (.items hands appleMatch)]

@[mcfunction]
public def execPredicate := probe [.when (.predicate (.named "batch:always"))]

@[mcfunction]
public def execInlinePredicate := probe [.when (.predicate (.ofNbt (nbt% {type: "minecraft:all_of", terms: []})))]

@[mcfunction]
public def selectName := probe [.as (.self {name := some (.include "A \"quoted\" \\ name$")})]

@[mcfunction]
public def selectOtherName := probe [.as (.self {name := some (.exclude "A \"quoted\" \\ name$")})]

@[mcfunction]
public def selectMode := probe [.as (.allPlayers {gameMode := some (.include .adventure), level := some (.between 3 5)})]

@[mcfunction]
public def selectNotMode := probe [.as (.allPlayers {gameMode := some (.exclude .adventure)})]

@[mcfunction]
public def selectRotation := probe [.as (.self {xRotation := some (.between (-10) 10), yRotation := some (.between 170 (-170))})]

@[mcfunction]
public def selectBox := probe [.as (.allEntities {tags := [.include "execution.actor"], dx := some 2, dy := some 2, dz := some 2})]

@[mcfunction]
public def selectOrigin := probe [.as (.nearestPlayer {x := some 20, y := some 70, z := some 20, distance := some (.atMost 1)})]

@[mcfunction]
public def selectPredicate := probe [.as (.self {predicates := [.include "batch:always"]})]

@[mcfunction]
public def selectNbt := probe [.as (.self {nbt := [.include (nbt% {Tags: ["execution.actor"]})]})]

@[mcfunction]
public def selectAdvancement := probe [.as (.allPlayers {advancements := [("batch:root", .criteria [("a", true), ("b", false)])]})]

@[mcfunction]
public def selectCompleted := probe [.as (.allPlayers {advancements := [("batch:root", .completed true)]})]

@[mcfunction]
public def execVehicle := probe [.on .vehicle]

@[mcfunction]
public def execPassengers := probe [.on .passengers]

@[mcfunction]
public def execOwner := probe [.on .owner]

@[mcfunction]
public def execController := probe [.on .controller]

@[mcfunction]
public def execLeasher := probe [.on .leasher]

@[mcfunction]
public def execTarget := probe [.on .target]

@[mcfunction]
public def execAttacker := probe [.on .attacker]

@[mcfunction]
public def execOrigin := probe [.on .origin]

@[mcfunction]
public def execSummon := Execute.forEach [.summon "minecraft:marker"] do
  Scoreboard.set .self points (.static 41)

@[mcfunction]
public def execHeight := Execute.forEach [.positionedOver .worldSurface] do
  Teleport.to victim origin

@[mcfunction]
public def execHeightmaps := probe [
  .positionedOver .motionBlocking, .positionedOver .motionBlockingNoLeaves,
  .positionedOver .oceanFloor]

@[mcfunction]
public def execStoreNumbers :=
  Execute.forEach [
    .storeResult (.nbt (.storage "batch:execute") (.key "b") .byte (.decimal 0.5)),
    .storeResult (.nbt (.storage "batch:execute") (.key "s") .short (.decimal 0.5)),
    .storeResult (.nbt (.storage "batch:execute") (.key "i") .int (.decimal 0.5)),
    .storeResult (.nbt (.storage "batch:execute") (.key "l") .long (.decimal 0.5)),
    .storeResult (.nbt (.storage "batch:execute") (.key "f") .float (.decimal 0.5)),
    .storeResult (.nbt (.storage "batch:execute") (.key "d") .double (.decimal 0.5))] do
      return (-7 : Val Int32)

@[mcfunction]
public def execStoreZero :=
  Execute.forEach [
    .storeSuccess (.nbt (.storage "batch:execute") (.key "ok") .byte (.static 1)),
    .storeResult (.nbt (.storage "batch:execute") (.key "result") .int (.static 1)),
    .storeResult (.bossbar "batch:execute" .value),
    .storeSuccess (.bossbar "batch:execute" .max)] do
      return (0 : Val Int32)

@[mcfunction]
public def execStoreFail :=
  Execute.forEach [
    .storeSuccess (.nbt (.storage "batch:execute") (.key "ok") .byte (.static 1)),
    .storeResult (.nbt (.storage "batch:execute") (.key "result") .int (.static 1)),
    .storeSuccess (.bossbar "batch:execute" .value)] do
      Scoreboard.get (.named "#absent") points

@[mcfunction]
public def execStoreDynamic := input (g := ⟨Req.none, Eff.world⟩) fun i => do
  Execute.forEach [.storeResult (.nbt (.storage "batch:execute")
      ⟨.key ⟨"values"⟩, [.index (.dynamic i)]⟩ .int (.static 2))] do
    return i
  return i

@[mcfunction]
public def execStoreEntity :=
  Execute.forEach [.storeResult (.nbt (.entity victim) (.key "Air") .short (.static 1))] do
    return (123 : Val Int32)

@[mcfunction]
public def execStoreBlock :=
  Execute.forEach [.storeResult (.nbt (.block origin) (.key "TransferCooldown") .int (.static 1))] do
    return (12 : Val Int32)

@[mcfunction]
public def execStoreFork :=
  Execute.forEach [
    .storeResult (.nbt (.entity .self) (.key "Air") .short (.static 1)),
    .as (.allEntities {tags := [.include "execution.child"]}),
    .storeSuccess (.nbt (.entity .self) (.key "Air") .short (.static 1))] do
      Scoreboard.get .self points

@[mcfunction]
public def teleportEntity := capture (Teleport.entity victim (.selector
  (.allEntities {tags := [.include "execution.destination"], limit := some 1})))

@[mcfunction]
public def teleportPlural := capture (Teleport.to (.selector
  (.allEntities {tags := [.include "execution.child"]})) origin
    (some (.angles ⟨.absolute (.decimal 90.5), .absolute (.static 0)⟩)))

@[mcfunction]
public def teleportFacing := capture (Teleport.to victim origin
  (some (.facing (.world (.relative (.static 2)) (.relative (.static 0)) (.relative (.static 0))))))

@[mcfunction]
public def teleportFacingEntity := capture (Teleport.to victim origin
  (some (.entity (.selector (.allEntities {tags := [.include "execution.destination"], limit := some 1})) .eyes)))

@[mcfunction]
public def teleportDynamic := input (g := Teleport.grade victim origin
    (some (.angles ⟨.relative (.static 0), .absolute (.static 0)⟩))) fun n => do
  Teleport.to victim origin (some (.angles ⟨.relative (.dynamic n), .absolute (.static 0)⟩))

end Oria.Proofs.Fixtures.Batch
