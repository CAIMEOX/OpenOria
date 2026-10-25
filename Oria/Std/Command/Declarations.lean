module

public import Oria.Command.Syntax
public import Oria.Std.Command.Arg.Data
public import Oria.Std.Command.Arg.Dialog
public import Oria.Std.Command.Arg.Text
public import Oria.Std.Command.Arg.Scoreboard
public import Oria.Std.Command.Arg.Nbt
public import Oria.Std.Command.Arg.Presentation
public import Oria.Std.Command.Declarations.World
public import Oria.Std.Command.Declarations.Player
public import Oria.Std.Command.Declarations.Management
public import Oria.Std.Command.Declarations.Control
public import Oria.Std.Command.Declarations.Content
public import Oria.Std.Command.Declarations.Generation
public import Oria.Std.Command.Declarations.Utility
public import Oria.Std.Command.Declarations.Server
public import Oria.Std.Command.Declarations.Scoreboard

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Standard command declarations

Each declaration fixes a command's identity, argument codecs, text template, and base
effects and context requirements. The standard library function's grade adds requirements
from concrete arguments. The compiler builds its command catalog from
[all](##Oria.Std.Command.Declarations.all). Applications use the command functions listed
in the [standard library guide](##Oria.Std).
-/

namespace Oria.Std.Command.Declarations

open Oria.Std.Command.Arg
open Oria.Command (ArgCodec Objective ScoreOp Word)

/-- Add one native word tag to selected entities. -/
@[expose] public def tagAdd : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target), ArgCodec.key (A := Word)]
    req := Req.none, eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.tag.add
    template := {parts := [.token "tag", .space, .slot ⟨0, by simp⟩,
      .space, .token "add", .space, .slot ⟨1, by simp⟩]} }

/-- Remove one tag from selected entities. -/
@[expose] public def tagRemove : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target), ArgCodec.key (A := Word)]
    req := Req.none, eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.tag.remove
    template := {parts := [.token "tag", .space, .slot ⟨0, by simp⟩,
      .space, .token "remove", .space, .slot ⟨1, by simp⟩]} }

/-- List the union of selected entities' tags. -/
@[expose] public def tagList : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target)]
    req := Req.none, eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.tag.list
    template := {parts := [.token "tag", .space, .slot ⟨0, by simp⟩, .space, .token "list"]} }

/-- Send a component to the selected title location. -/
@[expose] public def titleShow : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := TitlePart), ArgCodec.key (A := TextComponent)]
    req := Req.none, eff := Eff.hud ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.title.show
    template := .positional ["title"] }

/-- Clear title text while retaining animation timings. -/
@[expose] public def titleClear : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players)]
    req := Req.none, eff := Eff.hud ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.title.clear
    template := {parts := [.token "title", .space, .slot ⟨0, by simp⟩, .space, .token "clear"]} }

/-- Clear title text and restore native animation timings. -/
@[expose] public def titleReset : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players)]
    req := Req.none, eff := Eff.hud ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.title.reset
    template := {parts := [.token "title", .space, .slot ⟨0, by simp⟩, .space, .token "reset"]} }

/-- Set native fade-in, stay, and fade-out durations. -/
@[expose] public def titleTimes : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := Time),
      ArgCodec.key (A := Time), ArgCodec.key (A := Time)]
    req := Req.none, eff := Eff.hud ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.title.times
    template := {parts := [.token "title", .space, .slot ⟨0, by simp⟩,
      .space, .token "times", .space, .slot ⟨1, by simp⟩,
      .space, .slot ⟨2, by simp⟩, .space, .slot ⟨3, by simp⟩]} }

/-- Send a positioned sound with an explicit playback parameter tail. -/
@[expose] public def soundPlay : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ResourceId), ArgCodec.key (A := SoundChannel),
      ArgCodec.key (A := Players), ArgCodec.key (A := SoundSettings)]
    req := Req.dimension, eff := Eff.sound ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.playsound
    template := .positional ["playsound"] }

/-- Request stopping every sound category and ID. -/
@[expose] public def soundStop : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players)]
    req := Req.none, eff := Eff.sound ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.stopsound
    template := .positional ["stopsound"] }

/-- Request stopping a sound category. -/
@[expose] public def soundStopChannel : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := SoundChannel)]
    req := Req.none, eff := Eff.sound ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.stopsound.channel
    template := .positional ["stopsound"] }

/-- Request stopping one sound ID in every category. -/
@[expose] public def soundStopAny : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := ResourceId)]
    req := Req.none, eff := Eff.sound ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.stopsound.sound
    template := {parts := [.token "stopsound", .space, .slot ⟨0, by simp⟩,
      .space, .token "*", .space, .slot ⟨1, by simp⟩]} }

/-- Request stopping one sound ID in a particular category. -/
@[expose] public def soundStopOne : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := SoundChannel), ArgCodec.key (A := ResourceId)]
    req := Req.none, eff := Eff.sound ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.stopsound.channel_sound
    template := .positional ["stopsound"] }

/-- Apply native kill to a nonempty entity selection. -/
@[expose] public def kill : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target)]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random
  } := {
    key := `minecraft.kill
    template := .positional ["kill"] }

/-- Summon with native initialization at the source position. -/
@[expose] public def summonHere : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ResourceId)]
    req := Req.dimension ||| Req.position
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random
  } := {
    key := `minecraft.summon
    template := .positional ["summon"] }

/-- Summon with native initialization at an explicit position. -/
@[expose] public def summonAt : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ResourceId), ArgCodec.key (A := Vec3)]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random
  } := {
    key := `minecraft.summon.position
    template := .positional ["summon"] }

/-- Summon using supplied entity NBT, including an explicitly empty compound. -/
@[expose] public def summonData : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ResourceId), ArgCodec.key (A := Vec3), ArgCodec.key (A := Compound)]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random
  } := {
    key := `minecraft.summon.nbt
    template := .positional ["summon"] }

/-- Give an effect with native default duration, amplifier, and visibility. -/
@[expose] public def effectGive : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target), ArgCodec.key (A := ResourceId)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random
  } := {
    key := `minecraft.effect.give
    template := .positional ["effect", "give"] }

/-- Give an effect with explicit duration, amplifier, and visibility. -/
@[expose] public def effectGiveFor : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target), ArgCodec.key (A := ResourceId),
      ArgCodec.key (A := Duration), ArgCodec.key (A := Scalar), ArgCodec.key (A := Bool)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random
  } := {
    key := `minecraft.effect.give.duration
    template := .positional ["effect", "give"] }

/-- Clear every active effect from the selected living entities. -/
@[expose] public def effectClear : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random
  } := {
    key := `minecraft.effect.clear
    template := .positional ["effect", "clear"] }

/-- Clear one registered effect from the selected living entities. -/
@[expose] public def effectClearOne : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target), ArgCodec.key (A := ResourceId)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random
  } := {
    key := `minecraft.effect.clear.single
    template := .positional ["effect", "clear"] }

/-- Entity targets and a three-dimensional destination. -/
@[expose] public def teleport : Oria.Command.Ref {
    schema := [
      ArgCodec.key (A := Target),
      ArgCodec.key (A := Vec3)
    ]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.teleport.entity_position
    template := { parts := [
      .token "teleport", .space, .slot ⟨0, by simp⟩,
      .space, .slot ⟨1, by simp⟩
    ] }
  }

/-- Teleport to coordinates and apply an explicit rotation or facing operation. -/
@[expose] public def teleportOriented : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target), ArgCodec.key (A := Vec3), ArgCodec.key (A := RotationAction)]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.teleport.oriented
    template := .positional ["teleport"] }

/-- Teleport targets to one destination entity, including its dimension and rotation. -/
@[expose] public def teleportEntity : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target), ArgCodec.key (A := Target)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.teleport.entity
    template := .positional ["teleport"] }

/-- Template for reading one score. -/
@[expose] public def scoreGet : Oria.Command.Ref {
    schema := [
      ArgCodec.key (A := ScoreHolder),
      ArgCodec.key (A := Objective)
    ]
    req := Req.none
    eff := Eff.scoreboardRead
  } := {
    key := `minecraft.scoreboard.players.get
    cost := some 1
    template := { parts := [
      .token "scoreboard", .space, .token "players", .space,
      .token "get", .space, .slot ⟨0, by simp⟩,
      .space, .slot ⟨1, by simp⟩
    ] }
  }

/-- Template for setting a score with a possibly dynamic integer argument. -/
@[expose] public def scoreSet : Oria.Command.Ref {
    schema := [
      ArgCodec.key (A := ScoreHolder),
      ArgCodec.key (A := Objective),
      ArgCodec.key (A := Scalar)
    ]
    req := Req.none
    eff := Eff.scoreboardWrite
  } := {
    key := `minecraft.scoreboard.players.set
    cost := some 1
    template := { parts := [
      .token "scoreboard", .space, .token "players", .space,
      .token "set", .space, .slot ⟨0, by simp⟩,
      .space, .slot ⟨1, by simp⟩, .space, .slot ⟨2, by simp⟩
    ] }
  }

/-- Template for arithmetic between two score locations. -/
@[expose] public def scoreOperation : Oria.Command.Ref {
    schema := [
      ArgCodec.key (A := ScoreSlot),
      ArgCodec.key (A := ScoreOp),
      ArgCodec.key (A := ScoreSlot)
    ]
    req := Req.none
    eff := Eff.scoreboardRead ||| Eff.scoreboardWrite
  } := {
    key := `minecraft.scoreboard.players.operation
    cost := some 1
    template := { parts := [
      .token "scoreboard", .space, .token "players", .space,
      .token "operation", .space, .slot ⟨0, by simp⟩,
      .space, .slot ⟨1, by simp⟩, .space, .slot ⟨2, by simp⟩
    ] }
  }

/-- Create an objective with a native criterion. -/
@[expose] public def objectiveAdd : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Objective), ArgCodec.key (A := Criterion)]
    req := Req.none, eff := Eff.scoreboardRead ||| Eff.scoreboardWrite
  } := {
    key := `minecraft.scoreboard.objectives.add
    template := .positional ["scoreboard", "objectives", "add"] }

/-- Remove an objective and all of its scores. -/
@[expose] public def objectiveRemove : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Objective)]
    req := Req.none, eff := Eff.scoreboardRead ||| Eff.scoreboardWrite
  } := {
    key := `minecraft.scoreboard.objectives.remove
    template := .positional ["scoreboard", "objectives", "remove"] }

/-- Remove one holder's score in an objective. -/
@[expose] public def scoreReset : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ScoreHolder), ArgCodec.key (A := Objective)]
    req := Req.none, eff := Eff.scoreboardWrite
  } := {
    key := `minecraft.scoreboard.players.reset
    template := .positional ["scoreboard", "players", "reset"] }

/-- Remove all scores of one holder. -/
@[expose] public def scoreResetAll : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ScoreHolder)]
    req := Req.none, eff := Eff.scoreboardWrite
  } := {
    key := `minecraft.scoreboard.players.reset.all
    template := .positional ["scoreboard", "players", "reset"] }

/-- Unlock one holder's trigger score. -/
@[expose] public def scoreEnable : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ScoreHolder), ArgCodec.key (A := Objective)]
    req := Req.none, eff := Eff.scoreboardRead ||| Eff.scoreboardWrite
  } := {
    key := `minecraft.scoreboard.players.enable
    template := .positional ["scoreboard", "players", "enable"] }

/-- Consume the executing player's trigger authorization and increment its score. -/
@[expose] public def triggerRun : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Objective)]
    req := Req.executor, eff := Eff.scoreboardRead ||| Eff.scoreboardWrite
  } := {
    key := `minecraft.trigger
    template := .positional ["trigger"] }

/-- Consume trigger authorization and add a possibly dynamic integer. -/
@[expose] public def triggerAdd : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Objective), ArgCodec.key (A := Scalar)]
    req := Req.executor, eff := Eff.scoreboardRead ||| Eff.scoreboardWrite
  } := {
    key := `minecraft.trigger.add
    template := {parts := [.token "trigger", .space, .slot ⟨0, by simp⟩,
      .space, .token "add", .space, .slot ⟨1, by simp⟩]} }

/-- Consume trigger authorization and set a possibly dynamic integer. -/
@[expose] public def triggerSet : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Objective), ArgCodec.key (A := Scalar)]
    req := Req.executor, eff := Eff.scoreboardRead ||| Eff.scoreboardWrite
  } := {
    key := `minecraft.trigger.set
    template := {parts := [.token "trigger", .space, .slot ⟨0, by simp⟩,
      .space, .token "set", .space, .slot ⟨1, by simp⟩]} }

/-- Sampling template using the current dimension's random source. -/
@[expose] public def randomValue : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Range)], req := Req.dimension, eff := Eff.random
  } := {
    key := `minecraft.random.value
    template := .positional ["random", "value"] }

/-- Sampling template using a named random sequence. -/
@[expose] public def randomValueSequence : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Range), ArgCodec.key (A := ResourceId)]
    req := Req.none, eff := Eff.random
  } := {
    key := `minecraft.random.value.sequence
    template := .positional ["random", "value"] }

/-- Sampling and broadcasting template using the current dimension's random source. -/
@[expose] public def randomRoll : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Range)], req := Req.dimension, eff := Eff.random ||| Eff.chat
  } := {
    key := `minecraft.random.roll
    template := .positional ["random", "roll"] }

/-- Sampling and broadcasting template using a named random sequence. -/
@[expose] public def randomRollSequence : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Range), ArgCodec.key (A := ResourceId)]
    req := Req.none, eff := Eff.random ||| Eff.chat
  } := {
    key := `minecraft.random.roll.sequence
    template := .positional ["random", "roll"] }

/-- Template for resetting random sequences with existing defaults. -/
@[expose] public def randomReset : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Sequences)], req := Req.none, eff := Eff.random
  } := {
    key := `minecraft.random.reset
    template := .positional ["random", "reset"] }

/-- Template for resetting random sequences with an explicit seed and mixing rules. -/
@[expose] public def randomResetSeed : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Sequences), ArgCodec.key (A := Seed)]
    req := Req.none, eff := Eff.random
  } := {
    key := `minecraft.random.reset.seed
    template := .positional ["random", "reset"] }

/-- Template for sending NBT text components. -/
@[expose] public def tellraw : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := TextComponent)]
    req := Req.none
    eff := Eff.chat ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.tellraw
    template := .positional ["tellraw"] }

/-- Template for measuring a target's root compound. -/
@[expose] public def dataGet : Oria.Command.Ref {
    schema := [ArgCodec.key (A := DataTarget)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.data.get
    cost := some 1
    template := .positional ["data", "get"] }

/-- Template for measuring one NBT value selected by a path. -/
@[expose] public def dataGetPath : Oria.Command.Ref {
    schema := [ArgCodec.key (A := DataTarget), ArgCodec.key (A := Nbt.Path Scalar (Nbt.Value .compound))]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.data.get.path
    cost := some 1
    template := .positional ["data", "get"] }

/-- Template for scaling a selected numeric value and returning an integer. -/
@[expose] public def dataGetScaled : Oria.Command.Ref {
    schema := [ArgCodec.key (A := DataTarget), ArgCodec.key (A := Nbt.Path Scalar (Nbt.Value .compound)), ArgCodec.key (A := Float)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.data.get.scaled
    cost := some 1
    template := .positional ["data", "get"] }

/-- Template for merging NBT compounds. -/
@[expose] public def dataMerge : Oria.Command.Ref {
    schema := [ArgCodec.key (A := DataTarget), ArgCodec.key (A := Nbt.Any)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.data.merge
    cost := some 1
    template := .positional ["data", "merge"] }

/-- Template for removing NBT values selected by a path. -/
@[expose] public def dataRemove : Oria.Command.Ref {
    schema := [ArgCodec.key (A := DataTarget), ArgCodec.key (A := Nbt.Path Scalar (Nbt.Value .compound))]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.data.remove
    cost := some 1
    template := .positional ["data", "remove"] }

/-- NBT modification template combining a target, path, operation, and source. -/
@[expose] public def dataModify : Oria.Command.Ref {
    schema := [ArgCodec.key (A := DataTarget), ArgCodec.key (A := Nbt.Path Scalar (Nbt.Value .compound)),
      ArgCodec.key (A := DataOp), ArgCodec.key (A := DataSource)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.data.modify
    cost := some 1
    template := .positional ["data", "modify"] }

/-- Template for evaluating a number provider in a loot context. -/
@[expose] public def compute : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ComputeContext), ArgCodec.key (A := Calculation)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.compute
    template := .positional ["compute"] }

/-- Template for evaluating a float provider and scaling its result. -/
@[expose] public def computeScaled : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ComputeContext), ArgCodec.key (A := Provider), ArgCodec.key (A := Float32)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.compute.scaled
    template := { parts := [.token "compute", .space, .slot ⟨0, by simp⟩,
      .space, .token "float", .space, .slot ⟨1, by simp⟩, .space, .slot ⟨2, by simp⟩] } }

/-- Template for sending a named or inline dialog. -/
@[expose] public def dialogShow : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := DialogContent)]
    req := Req.none
    eff := Eff.dialog ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.dialog.show
    template := .positional ["dialog", "show"] }

/-- Template for dismissing players' current dialogs. -/
@[expose] public def dialogClear : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players)]
    req := Req.none
    eff := Eff.dialog ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.dialog.clear
    template := .positional ["dialog", "clear"] }

/-- Complete standard declaration set used to build the target command catalog. -/
@[expose] public def all : List Oria.Command.Decl :=
  world ++ player ++ management ++ control ++ content ++ generation ++ utility ++ server ++ scores ++
  [tagAdd.declaration, tagRemove.declaration, tagList.declaration,
    titleShow.declaration, titleClear.declaration, titleReset.declaration, titleTimes.declaration,
    soundPlay.declaration, soundStop.declaration, soundStopChannel.declaration,
    soundStopAny.declaration, soundStopOne.declaration,
    kill.declaration, summonHere.declaration, summonAt.declaration, summonData.declaration,
    effectGive.declaration, effectGiveFor.declaration, effectClear.declaration, effectClearOne.declaration,
    teleport.declaration, teleportOriented.declaration, teleportEntity.declaration,
    scoreGet.declaration, scoreSet.declaration, scoreOperation.declaration,
    objectiveAdd.declaration, objectiveRemove.declaration, scoreReset.declaration,
    scoreResetAll.declaration, scoreEnable.declaration,
    triggerRun.declaration, triggerAdd.declaration, triggerSet.declaration,
    randomValue.declaration, randomValueSequence.declaration,
    randomRoll.declaration, randomRollSequence.declaration,
    randomReset.declaration, randomResetSeed.declaration, tellraw.declaration,
    dataGet.declaration, dataGetPath.declaration, dataGetScaled.declaration,
    dataMerge.declaration, dataRemove.declaration, dataModify.declaration,
    compute.declaration, computeScaled.declaration, dialogShow.declaration, dialogClear.declaration]

end Oria.Std.Command.Declarations
