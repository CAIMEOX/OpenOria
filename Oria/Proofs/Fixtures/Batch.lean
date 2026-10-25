module
public import Oria.Datapack
public import Oria.Proofs.Fixtures.Batch.World
public import Oria.Proofs.Fixtures.Batch.Player
public import Oria.Proofs.Fixtures.Batch.Management
public import Oria.Proofs.Fixtures.Batch.Control
public import Oria.Proofs.Fixtures.Batch.Movement
public import Oria.Proofs.Fixtures.Batch.Display
public import Oria.Proofs.Fixtures.Batch.Items
public import Oria.Proofs.Fixtures.Batch.Blocks
public import Oria.Proofs.Fixtures.Batch.Execution
meta import Oria.Datapack
meta import Oria.Proofs.Fixtures.Batch.World
meta import Oria.Proofs.Fixtures.Batch.Player
meta import Oria.Proofs.Fixtures.Batch.Management
meta import Oria.Proofs.Fixtures.Batch.Control
meta import Oria.Proofs.Fixtures.Batch.Movement
meta import Oria.Proofs.Fixtures.Batch.Display
meta import Oria.Proofs.Fixtures.Batch.Items
meta import Oria.Proofs.Fixtures.Batch.Blocks
meta import Oria.Proofs.Fixtures.Batch.Execution

namespace Oria.Proofs.Fixtures.Batch
open Oria.Datapack

private def worldEntries : Builder Unit := do
  entry "weatherclear" weatherClear.ref
  entry "weatherrain" weatherRain.ref
  entry "weatherthunder" weatherThunder.ref
  entry "weathersample" weatherSample.ref
  entry "clockpause" clockPause.ref
  entry "clockresume" clockResume.ref
  entry "clockset" clockSet.ref
  entry "clockadd" clockAdd.ref
  entry "clockquery" clockQuery.ref
  entry "clockdefault" clockDefault.ref
  entry "clockmarker" clockMarker.ref
  entry "clockrate" clockRate.ref
  entry "clockresetrate" clockResetRate.ref
  entry "timelineticks" timelineTicks.ref
  entry "timelinerepetition" timelineRepetition.ref
  entry "gametime" gameTime.ref
  entry "difficultyget" difficultyGet.ref
  entry "difficultyset" difficultySet.ref
  entry "defaultmode" defaultMode.ref
  entry "borderget" borderGet.ref
  entry "borderset" borderSet.ref
  entry "borderadd" borderAdd.ref
  entry "bordercenter" borderCenter.ref
  entry "borderbuffer" borderBuffer.ref
  entry "borderdamage" borderDamage.ref
  entry "borderwarningdistance" borderWarningDistance.ref
  entry "borderwarningtime" borderWarningTime.ref
  entry "bordertransition" borderTransition.ref
  entry "weatherdynamic" weatherDynamic.ref
  entry "clockdynamic" clockDynamic.ref
  entry "borderdynamic" borderDynamic.ref
  entry "xpdynamic" xpDynamic.ref
  entry "enchantdynamic" enchantDynamic.ref
  entry "damagedynamic" damageDynamic.ref
  entry "bardynamic" barDynamic.ref

private def playerEntries : Builder Unit := do
  entry "creative" creative.ref
  entry "survival" survival.ref
  entry "xplevels" xpLevels.ref
  entry "xppoints" xpPoints.ref
  entry "xpadd" xpAdd.ref
  entry "xpquery" xpQuery.ref
  entry "xpquerylevels" xpQueryLevels.ref
  entry "xptoomany" xpTooMany.ref
  entry "recipegive" recipeGive.ref
  entry "recipetake" recipeTake.ref
  entry "recipeall" recipeAll.ref
  entry "recipetakeall" recipeTakeAll.ref
  entry "enchant" enchant.ref
  entry "damage" damage.ref
  entry "damagetype" damageType.ref
  entry "damageat" damageAt.ref
  entry "damageby" damageBy.ref
  entry "damagefrom" damageFrom.ref
  entry "grantcriterion" grantCriterion.ref
  entry "grantonly" grantOnly.ref
  entry "grantfrom" grantFrom.ref
  entry "grantuntil" grantUntil.ref
  entry "grantthrough" grantThrough.ref
  entry "granteverything" grantEverything.ref
  entry "revokecriterion" revokeCriterion.ref
  entry "revokeonly" revokeOnly.ref
  entry "revokefrom" revokeFrom.ref
  entry "revokeuntil" revokeUntil.ref
  entry "revokethrough" revokeThrough.ref
  entry "revokeeverything" revokeEverything.ref

private def managementEntries : Builder Unit := do
  entry "barlist" barList.ref
  entry "baradd" barAdd.ref
  entry "barremove" barRemove.ref
  entry "bargetvalue" barGetValue.ref
  entry "bargetmax" barGetMax.ref
  entry "bargetvisible" barGetVisible.ref
  entry "bargetplayers" barGetPlayers.ref
  entry "barvalue" barValue.ref
  entry "barmax" barMax.ref
  entry "barinvisible" barInvisible.ref
  entry "barvisible" barVisible.ref
  entry "barcolor" barColor.ref
  entry "barstyle" barStyle.ref
  entry "barname" barName.ref
  entry "barplayers" barPlayers.ref
  entry "barnoplayers" barNoPlayers.ref
  entry "teamlist" teamList.ref
  entry "teamadd" teamAdd.ref
  entry "teamnamed" teamNamed.ref
  entry "teamjoin" teamJoin.ref
  entry "teamfake" teamFake.ref
  entry "teamwildcard" teamWildcard.ref
  entry "teamself" teamSelf.ref
  entry "teammembers" teamMembers.ref
  entry "teamleave" teamLeave.ref
  entry "teamleavefake" teamLeaveFake.ref
  entry "teamempty" teamEmpty.ref
  entry "teamremove" teamRemove.ref
  entry "teamremoveblue" teamRemoveBlue.ref
  entry "teamcolor" teamColor.ref
  entry "teamresetcolor" teamResetColor.ref
  entry "teamfire" teamFire.ref
  entry "teamsight" teamSight.ref
  entry "teamname" teamName.ref
  entry "teamnametags" teamNameTags.ref
  entry "teamdeathmessages" teamDeathMessages.ref
  entry "teamcollision" teamCollision.ref
  entry "teamprefix" teamPrefix.ref
  entry "teamsuffix" teamSuffix.ref

private def controlEntries : Builder Unit := do
  entry "ruleread" ruleRead.ref
  entry "ruleon" ruleOn.ref
  entry "ruleoff" ruleOff.ref
  entry "rulerandomread" ruleRandomRead.ref
  entry "attrget" attrGet.ref
  entry "attrnegative" attrNegative.ref
  entry "attrbase" attrBase.ref
  entry "attrset" attrSet.ref
  entry "attrreset" attrReset.ref
  entry "attradd" attrAdd.ref
  entry "attrmultiplybase" attrMultiplyBase.ref
  entry "attrmultiplytotal" attrMultiplyTotal.ref
  entry "attrmodifier" attrModifier.ref
  entry "attrremove" attrRemove.ref
  entry "attrremovebase" attrRemoveBase.ref
  entry "attrremovetotal" attrRemoveTotal.ref
  entry "attrmissing" attrMissing.ref
  entry "loadadd" loadAdd.ref
  entry "loadrange" loadRange.ref
  entry "loadquery" loadQuery.ref
  entry "loadlist" loadList.ref
  entry "loadremove" loadRemove.ref
  entry "loadremoverange" loadRemoveRange.ref
  entry "loadclear" loadClear.ref
  entry "ruledynamic" ruleDynamic.ref
  entry "attrdynamic" attrDynamic.ref
  entry "loaddynamic" loadDynamic.ref

private def movementEntries : Builder Unit := do
  entry "respawnhere" respawnHere.ref
  entry "respawnat" respawnAt.ref
  entry "respawnrotation" respawnRotation.ref
  entry "respawnlocal" respawnLocal.ref
  entry "worldspawnhere" worldSpawnHere.ref
  entry "worldspawnat" worldSpawnAt.ref
  entry "worldspawnrotation" worldSpawnRotation.ref
  entry "camerastart" cameraStart.ref
  entry "camerastop" cameraStop.ref
  entry "mount" mount.ref
  entry "dismount" dismount.ref
  entry "mountcycle" mountCycle.ref
  entry "rotateangles" rotateAngles.ref
  entry "rotaterelative" rotateRelative.ref
  entry "rotatefacing" rotateFacing.ref
  entry "rotateentity" rotateEntity.ref
  entry "spreadone" spreadOne.ref
  entry "spreadteams" spreadTeams.ref
  entry "rotationdynamic" rotationDynamic.ref
  entry "spawndynamic" spawnDynamic.ref

private def displayEntries : Builder Unit := do
  entry "particles" particles.ref
  entry "particledust" particleDust.ref
  entry "particleforce" particleForce.ref
  entry "swinghand" swingHand.ref
  entry "swingstab" swingStab.ref
  entry "swingnone" swingNone.ref
  entry "swingmarker" swingMarker.ref
  entry "postadd" postAdd.ref
  entry "postremove" postRemove.ref
  entry "postclear" postClear.ref
  entry "postlist" postList.ref
  entry "sidebar" sidebar.ref
  entry "belowname" belowName.ref
  entry "listdisplay" listDisplay.ref
  entry "teamsidebar" teamSidebar.ref
  entry "clearsidebar" clearSidebar.ref
  entry "objectivename" objectiveName.ref
  entry "objectivehearts" objectiveHearts.ref
  entry "objectiveinteger" objectiveInteger.ref
  entry "objectiveauto" objectiveAuto.ref
  entry "objectiveblank" objectiveBlank.ref
  entry "objectivefixed" objectiveFixed.ref
  entry "objectivestyle" objectiveStyle.ref
  entry "objectiveformatreset" objectiveFormatReset.ref
  entry "scorename" scoreName.ref
  entry "scorenamereset" scoreNameReset.ref
  entry "scoreblank" scoreBlank.ref
  entry "scorefixed" scoreFixed.ref
  entry "scorestyle" scoreStyle.ref
  entry "scoreformatreset" scoreFormatReset.ref
  entry "teamfilter" teamFilter.ref
  entry "teamexclude" teamExclude.ref
  entry "teamemptyfilter" teamEmptyFilter.ref
  entry "teamanyfilter" teamAnyFilter.ref
  entry "particledynamic" particleDynamic.ref
  entry "swingdynamic" swingDynamic.ref
  entry "scoredynamic" scoreDynamic.ref
  entry "particlenbt" particleNbt.ref

private def itemsEntries : Builder Unit := do
  entry "giveapples" giveApples.ref
  entry "givenamed" giveNamed.ref
  entry "giveremoved" giveRemoved.ref
  entry "clearprobe" clearProbe.ref
  entry "clearlimited" clearLimited.ref
  entry "clearapples" clearApples.ref
  entry "clearnamed" clearNamed.ref
  entry "cleardata" clearData.ref
  entry "clearnofood" clearNoFood.ref
  entry "cleareither" clearEither.ref
  entry "clearcount" clearCount.ref
  entry "cleartag" clearTag.ref
  entry "clearall" clearAll.ref
  entry "itemset" itemSet.ref
  entry "itemreplace" itemReplace.ref
  entry "itemfill" itemFill.ref
  entry "itemoverride" itemOverride.ref
  entry "itemnamedslots" itemNamedSlots.ref
  entry "iteminlineslots" itemInlineSlots.ref
  entry "itemnamedmodifier" itemNamedModifier.ref
  entry "iteminlinemodifier" itemInlineModifier.ref
  entry "itemmodifiedcopy" itemModifiedCopy.ref
  entry "itementity" itemEntity.ref
  entry "itementitysource" itemEntitySource.ref
  entry "itembadslot" itemBadSlot.ref
  entry "lootgive" lootGive.ref
  entry "lootinline" lootInline.ref
  entry "lootinsert" lootInsert.ref
  entry "lootblock" lootBlock.ref
  entry "lootentity" lootEntity.ref
  entry "lootspawn" lootSpawn.ref
  entry "lootmine" lootMine.ref
  entry "lootmineheld" lootMineHeld.ref
  entry "lootkill" lootKill.ref
  entry "lootfish" lootFish.ref
  entry "givedynamic" giveDynamic.ref
  entry "givecomponentdynamic" giveComponentDynamic.ref
  entry "cleardynamic" clearDynamic.ref
  entry "itemcountdynamic" itemCountDynamic.ref
  entry "itemslotdynamic" itemSlotDynamic.ref
  entry "modifierdynamic" modifierDynamic.ref
  entry "lootcountdynamic" lootCountDynamic.ref
  entry "componentnbt" componentNbt.ref

private def blocksEntries : Builder Unit := do
  entry "placechest" placeChest.ref
  entry "turnchest" turnChest.ref
  entry "clearchestdata" clearChestData.ref
  entry "placestone" placeStone.ref
  entry "placekeep" placeKeep.ref
  entry "placedestroy" placeDestroy.ref
  entry "placestrict" placeStrict.ref
  entry "fillstone" fillStone.ref
  entry "fillfiltered" fillFiltered.ref
  entry "filltag" fillTag.ref
  entry "fillkeep" fillKeep.ref
  entry "filldestroy" fillDestroy.ref
  entry "fillcube" fillCube.ref
  entry "filloutline" fillOutline.ref
  entry "fillhollow" fillHollow.ref
  entry "clonenormal" cloneNormal.ref
  entry "clonemasked" cloneMasked.ref
  entry "clonefiltered" cloneFiltered.ref
  entry "cloneoverlap" cloneOverlap.ref
  entry "cloneforce" cloneForce.ref
  entry "clonemove" cloneMove.ref
  entry "clonechest" cloneChest.ref
  entry "clonedimensions" cloneDimensions.ref
  entry "clonecrossdimension" cloneCrossDimension.ref
  entry "fillproperties" fillProperties.ref
  entry "propertydynamic" propertyDynamic.ref
  entry "filldynamic" fillDynamic.ref
  entry "blocknbt" blockNbt.ref

private def executionEntries : Builder Unit := do
  entry "execblock" execBlock.ref
  entry "execblocktag" execBlockTag.ref
  entry "execblocknbt" execBlockNbt.ref
  entry "execblocks" execBlocks.ref
  entry "execmasked" execMasked.ref
  entry "execbiome" execBiome.ref
  entry "execbiometag" execBiomeTag.ref
  entry "execdimension" execDimension.ref
  entry "execotherdimension" execOtherDimension.ref
  entry "execloaded" execLoaded.ref
  entry "execnotloaded" execNotLoaded.ref
  entry "execslots" execSlots.ref
  entry "execnoslots" execNoSlots.ref
  entry "execitems" execItems.ref
  entry "exechands" execHands.ref
  entry "execpredicate" execPredicate.ref
  entry "execinlinepredicate" execInlinePredicate.ref
  entry "selectname" selectName.ref
  entry "selectothername" selectOtherName.ref
  entry "selectmode" selectMode.ref
  entry "selectnotmode" selectNotMode.ref
  entry "selectrotation" selectRotation.ref
  entry "selectbox" selectBox.ref
  entry "selectorigin" selectOrigin.ref
  entry "selectpredicate" selectPredicate.ref
  entry "selectnbt" selectNbt.ref
  entry "selectadvancement" selectAdvancement.ref
  entry "selectcompleted" selectCompleted.ref
  entry "execvehicle" execVehicle.ref
  entry "execpassengers" execPassengers.ref
  entry "execowner" execOwner.ref
  entry "execcontroller" execController.ref
  entry "execleasher" execLeasher.ref
  entry "exectarget" execTarget.ref
  entry "execattacker" execAttacker.ref
  entry "execorigin" execOrigin.ref
  entry "execsummon" execSummon.ref
  entry "execheight" execHeight.ref
  entry "execheightmaps" execHeightmaps.ref
  entry "execstorenumbers" execStoreNumbers.ref
  entry "execstorezero" execStoreZero.ref
  entry "execstorefail" execStoreFail.ref
  entry "execstoredynamic" execStoreDynamic.ref
  entry "execstoreentity" execStoreEntity.ref
  entry "execstoreblock" execStoreBlock.ref
  entry "execstorefork" execStoreFork.ref
  entry "teleportentity" teleportEntity.ref
  entry "teleportplural" teleportPlural.ref
  entry "teleportfacing" teleportFacing.ref
  entry "teleportfacingentity" teleportFacingEntity.ref
  entry "teleportdynamic" teleportDynamic.ref

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
@[datapack]
public def specimen : Spec := build {ns := "batch", registerBudget := 6} do
  onLoad setup.ref
  worldEntries
  playerEntries
  managementEntries
  controlEntries
  movementEntries
  displayEntries
  itemsEntries
  blocksEntries
  executionEntries

end Oria.Proofs.Fixtures.Batch
