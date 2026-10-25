module

public import Oria.Proofs.Fixtures.Batch.Common
public import Oria.Datapack
public meta import Oria.Proofs.Fixtures.Batch.Common
public meta import Oria.Datapack

namespace Oria.Proofs.Fixtures.Utility
open Oria.Std Oria.Std.Command.Arg Oria.Datapack
open Oria.Proofs.Fixtures.Batch (capture input setup)

@[mcfunction]
public def say := capture (Chat.say "Round ready.")

@[mcfunction]
public def emote := capture (Chat.me "waves")

@[mcfunction]
public def tellSelf := capture (Chat.tell .self "Private message.")

@[mcfunction]
public def tellAll := capture (Chat.tell .all "Everyone ready.")

@[mcfunction]
public def tellAbsent := capture (Chat.tell (.selector (.allPlayers {tags := [.include "utility.absent"]})) "Nobody.")

@[mcfunction]
public def team := capture (Chat.team "Team ready.")

@[mcfunction]
public def expanded := capture (Chat.say (Message.join "Hello" [.selector .self, "score", .number (.static 7)]))

@[mcfunction]
public def nativeMessage := capture (Chat.say (Message.native "Native @s"))

@[mcfunction]
public def separated := capture (Chat.say (Message.join (.selector .allPlayers) ["[distance=..1]"]))

@[mcfunction]
public def players := capture (ServerInfo.players)

@[mcfunction]
public def playersUuids := capture (ServerInfo.players true)

@[mcfunction]
public def seed := capture (ServerInfo.seed)

@[mcfunction]
public def version := capture (ServerInfo.version)

@[mcfunction]
public def locateBiome := capture (Locate.biome (.id "minecraft:plains"))

@[mcfunction]
public def locateBiomes := capture (Locate.biome (.tag "utility:biomes"))

@[mcfunction]
public def locatePoi := capture (Locate.poi (.id "minecraft:meeting"))

@[mcfunction]
public def locatePois := capture (Locate.poi (.tag "utility:meeting"))

@[mcfunction]
public def locateEmptyPoi := capture (Locate.poi (.tag "utility:empty"))

@[mcfunction]
public def locateInvalidStructure := capture (Locate.structure (.id "utility:absent"))

@[mcfunction]
public def locateEmptyStructure := capture (Locate.structure (.tag "utility:empty"))

@[mcfunction]
public def locateVillage := capture (Locate.structure (.id "minecraft:village_plains"))

@[mcfunction]
public def add := capture (Scoreboard.add (.one (.named "#utility")) "utility.scores" (.static 2))

@[mcfunction]
public def addZero := capture (Scoreboard.add (.one (.named "#utility")) "utility.scores" (.static 0))

@[mcfunction]
public def remove := capture (Scoreboard.remove (.one (.named "#utility")) "utility.scores" (.static 5))

@[mcfunction]
public def addPlayers := capture (Scoreboard.add (.entities (.selector .allPlayers)) "utility.scores" (.static 2))

@[mcfunction]
public def removePlayers := capture (Scoreboard.remove (.entities (.selector .allPlayers)) "utility.scores" (.static 1))

@[mcfunction]
public def addAll := capture (Scoreboard.add .all "utility.scores" (.static 1))

@[mcfunction]
public def overflowAdd := capture (Scoreboard.add (.one (.named "#overflow")) "utility.scores" (.static 1))

@[mcfunction]
public def overflowRemove := capture (Scoreboard.remove (.one (.named "#overflow")) "utility.scores" (.static 1))

@[mcfunction]
public def addAbsent := capture (Scoreboard.add (.entities (.selector (.allPlayers {tags := [.include "utility.absent"]}))) "utility.scores" (.static 1))

@[mcfunction]
public def addMissingObjective := capture (Scoreboard.add (.one (.named "#utility")) "utility.absent" (.static 1))

@[mcfunction]
public def chatDynamic := input (g := Chat.grade "Round") fun n => do
  Chat.say (Message.join "Round" [.number (.dynamic n)])

@[mcfunction]
public def addDynamic := input (g := Scoreboard.updateGrade (.one (.named "#utility"))) fun n => do
  Scoreboard.add (.one (.named "#utility")) "utility.scores" (.dynamic n)

@[mcfunction]
public def removeDynamic := input (g := Scoreboard.updateGrade (.one (.named "#utility"))) fun n => do
  Scoreboard.remove (.one (.named "#utility")) "utility.scores" (.dynamic n)

@[datapack]
public def specimen : Spec := build {ns := "utility", registerBudget := 6} do
  onLoad setup.ref
  entry "say" say.ref
  entry "emote" emote.ref
  entry "tellself" tellSelf.ref
  entry "tellall" tellAll.ref
  entry "tellabsent" tellAbsent.ref
  entry "team" team.ref
  entry "expanded" expanded.ref
  entry "native" nativeMessage.ref
  entry "separated" separated.ref
  entry "players" players.ref
  entry "playersuuids" playersUuids.ref
  entry "seed" seed.ref
  entry "version" version.ref
  entry "locatebiome" locateBiome.ref
  entry "locatebiomes" locateBiomes.ref
  entry "locatepoi" locatePoi.ref
  entry "locatepois" locatePois.ref
  entry "locateemptypoi" locateEmptyPoi.ref
  entry "locateinvalidstructure" locateInvalidStructure.ref
  entry "locateemptystructure" locateEmptyStructure.ref
  entry "locatevillage" locateVillage.ref
  entry "add" add.ref
  entry "addzero" addZero.ref
  entry "remove" remove.ref
  entry "addplayers" addPlayers.ref
  entry "removeplayers" removePlayers.ref
  entry "addall" addAll.ref
  entry "overflowadd" overflowAdd.ref
  entry "overflowremove" overflowRemove.ref
  entry "addabsent" addAbsent.ref
  entry "addmissingobjective" addMissingObjective.ref
  entry "chatdynamic" chatDynamic.ref
  entry "adddynamic" addDynamic.ref
  entry "removedynamic" removeDynamic.ref

end Oria.Proofs.Fixtures.Utility

