module

import Oria.Std.Command.Declarations
import Oria.Std.Manifest
public meta import Oria.Std.Command.Arg
public meta import Oria.Std.Manifest

public import Oria.Datapack.Resource
public import Oria.Command.Resolve
public meta import Oria.Datapack.Resource
public meta import Oria.Command.Resolve

open Oria.Command (Objective ScoreOp)

namespace Oria.Proofs.Resource

open Oria
open Oria.Datapack
open Oria.Std.Command.Arg

private def resourceNamespace : ResourceNamespace :=
  .ofString "oria"

private def functionPath : ResourcePath :=
  .ofString "games/main"

private def publicPath : PublicFunctionPath :=
  .ofString "games/main"

private def internalPath : ResourcePath :=
  .ofString "__oria/internal/main"

private def functionId : FunctionId :=
  .ofParts resourceNamespace functionPath

#guard Version.dataPackVersion .dp121 == (121, 0)

#guard ResourceNamespace.parse "oria" |>.isOk
#guard !(ResourceNamespace.parse "Oria" |>.isOk)
#guard !(ResourceNamespace.parse "." |>.isOk)
#guard !(ResourceNamespace.parse ".." |>.isOk)
#guard ResourceNamespace.parse "oria.v1" |>.isOk
#guard ResourcePath.parse "games/main" |>.isOk
#guard !(ResourcePath.parse "/games/main" |>.isOk)
#guard !(ResourcePath.parse "games//main" |>.isOk)
#guard !(ResourcePath.parse "games/./main" |>.isOk)
#guard !(ResourcePath.parse "games/../main" |>.isOk)
#guard ResourcePath.parse "games/v1.2/main" |>.isOk
#guard PublicFunctionPath.parse "games/main" |>.isOk
#guard !(PublicFunctionPath.parse "__oria/internal" |>.isOk)

#guard resourceNamespace.render == "oria"
#guard functionPath.render == "games/main"
#guard functionPath.segments == ["games", "main"]
#guard functionId.render == "oria:games/main"

example : ResourceNamespace.Valid resourceNamespace.render :=
  resourceNamespace.property

example : ResourcePath.Valid functionPath.render :=
  functionPath.property

example : ResourcePath.Internal internalPath := by
  native_decide

example : ¬ResourcePath.Internal publicPath.val :=
  publicPath.property

example : Function.Injective FunctionId.render :=
  FunctionId.render_injective

example : Std.Manifest.commandDeclarations =
    Std.Command.Declarations.world ++ Std.Command.Declarations.player ++
    Std.Command.Declarations.management ++ Std.Command.Declarations.control ++
    Std.Command.Declarations.content ++ Std.Command.Declarations.generation ++
    Std.Command.Declarations.utility ++ Std.Command.Declarations.server ++
    Std.Command.Declarations.scores ++ [
    Std.Command.Declarations.tagAdd.declaration,
    Std.Command.Declarations.tagRemove.declaration,
    Std.Command.Declarations.tagList.declaration,
    Std.Command.Declarations.titleShow.declaration,
    Std.Command.Declarations.titleClear.declaration,
    Std.Command.Declarations.titleReset.declaration,
    Std.Command.Declarations.titleTimes.declaration,
    Std.Command.Declarations.soundPlay.declaration,
    Std.Command.Declarations.soundStop.declaration,
    Std.Command.Declarations.soundStopChannel.declaration,
    Std.Command.Declarations.soundStopAny.declaration,
    Std.Command.Declarations.soundStopOne.declaration,
    Std.Command.Declarations.kill.declaration,
    Std.Command.Declarations.summonHere.declaration,
    Std.Command.Declarations.summonAt.declaration,
    Std.Command.Declarations.summonData.declaration,
    Std.Command.Declarations.effectGive.declaration,
    Std.Command.Declarations.effectGiveFor.declaration,
    Std.Command.Declarations.effectClear.declaration,
    Std.Command.Declarations.effectClearOne.declaration,
    Std.Command.Declarations.teleport.declaration,
    Std.Command.Declarations.teleportOriented.declaration,
    Std.Command.Declarations.teleportEntity.declaration,
    Std.Command.Declarations.scoreGet.declaration,
    Std.Command.Declarations.scoreSet.declaration,
    Std.Command.Declarations.scoreOperation.declaration,
    Std.Command.Declarations.objectiveAdd.declaration,
    Std.Command.Declarations.objectiveRemove.declaration,
    Std.Command.Declarations.scoreReset.declaration,
    Std.Command.Declarations.scoreResetAll.declaration,
    Std.Command.Declarations.scoreEnable.declaration,
    Std.Command.Declarations.triggerRun.declaration,
    Std.Command.Declarations.triggerAdd.declaration,
    Std.Command.Declarations.triggerSet.declaration,
    Std.Command.Declarations.randomValue.declaration,
    Std.Command.Declarations.randomValueSequence.declaration,
    Std.Command.Declarations.randomRoll.declaration,
    Std.Command.Declarations.randomRollSequence.declaration,
    Std.Command.Declarations.randomReset.declaration,
    Std.Command.Declarations.randomResetSeed.declaration,
    Std.Command.Declarations.tellraw.declaration,
    Std.Command.Declarations.dataGet.declaration,
    Std.Command.Declarations.dataGetPath.declaration,
    Std.Command.Declarations.dataGetScaled.declaration,
    Std.Command.Declarations.dataMerge.declaration,
    Std.Command.Declarations.dataRemove.declaration,
    Std.Command.Declarations.dataModify.declaration,
    Std.Command.Declarations.compute.declaration,
    Std.Command.Declarations.computeScaled.declaration,
    Std.Command.Declarations.dialogShow.declaration,
    Std.Command.Declarations.dialogClear.declaration
  ] := by native_decide

example : Std.Command.Declarations.teleport.key = `minecraft.teleport.entity_position := rfl
example : Std.Command.Declarations.teleport.template = Std.Command.Declarations.teleport.template := rfl

example : Std.Command.Declarations.scoreGet.key = `minecraft.scoreboard.players.get := rfl
example : Std.Command.Declarations.scoreGet.template = Std.Command.Declarations.scoreGet.template := rfl

example : Std.Command.Declarations.scoreSet.key = `minecraft.scoreboard.players.set := rfl
example : Std.Command.Declarations.scoreSet.template = Std.Command.Declarations.scoreSet.template := rfl

example : Std.Command.Declarations.scoreOperation.key = `minecraft.scoreboard.players.operation := rfl
example : Std.Command.Declarations.scoreOperation.template = Std.Command.Declarations.scoreOperation.template := rfl

#guard Std.Manifest.commandCatalog.isOk

private def objective : Objective :=
  .ofToken (.ofString "points")

private def scoreSlot : ScoreSlot :=
  { holder := .self, objective }

private def teleportRequest := Std.Command.Declarations.teleport.call <|
    .cons (Command.encode (.self : Target)) <|
      .cons (Command.encode (Vec3.world (.absolute (.static 1))
        (.absolute (.static 2)) (.absolute (.static 3)))) .nil

private def getRequest := Std.Command.Declarations.scoreGet.call <|
  .cons (Command.encode (.self : ScoreHolder)) <| .cons (Command.encode objective) .nil

private def setRequest := Std.Command.Declarations.scoreSet.call <|
  .cons (Command.encode (.self : ScoreHolder)) <| .cons (Command.encode objective) <|
    .cons (Command.encode (.static 7 : Scalar)) .nil

private def operationRequest := Std.Command.Declarations.scoreOperation.call <|
  .cons (Command.encode scoreSlot) <| .cons (Command.encode (.add : ScoreOp)) <|
    .cons (Command.encode scoreSlot) .nil

#guard match Std.Manifest.commandCatalog with
  | .error _ => false
  | .ok catalog => (Version.resolve .dp121 catalog teleportRequest).isOk
#guard match Std.Manifest.commandCatalog with
  | .error _ => false
  | .ok catalog => (Version.resolve .dp121 catalog getRequest).isOk
#guard match Std.Manifest.commandCatalog with
  | .error _ => false
  | .ok catalog => (Version.resolve .dp121 catalog setRequest).isOk
#guard match Std.Manifest.commandCatalog with
  | .error _ => false
  | .ok catalog => (Version.resolve .dp121 catalog operationRequest).isOk

end Oria.Proofs.Resource
