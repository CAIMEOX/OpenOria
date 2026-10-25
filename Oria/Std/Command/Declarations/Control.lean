module

public import Oria.Std.Command.Arg.Control
public import Oria.Std.Command.Arg.Gamerule
public import Oria.Std.Command.Arg.Display

set_option doc.verso true
set_option linter.missingDocs true

namespace Oria.Std.Command.Declarations
open Oria.Std.Command.Arg
open Oria.Command (ArgCodec)

/-- Query a typed native rule. -/
@[expose] public def ruleGet : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Oria.Command.Word)]
    req := Req.dimension
    eff := Eff.world
  } := {
    key := `minecraft.std.ruleGet
    template := .positional ["gamerule"] }

/-- Assign a typed native rule. -/
@[expose] public def ruleSet : Oria.Command.Ref {
    schema := [ArgCodec.key (A := RuleUpdate)]
    req := Req.dimension
    eff := Eff.world
  } := {
    key := `minecraft.std.ruleSet
    template := .positional ["gamerule"] }

/-- Query or update one entity attribute. -/
@[expose] public def attributeRun : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target), ArgCodec.key (A := ResourceId), ArgCodec.key (A := AttributeAction)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.attribute
    template := .positional ["attribute"] }

/-- Manage forced chunks in the source dimension. -/
@[expose] public def forceload : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ForceloadAction)]
    req := Req.dimension
    eff := Eff.world
  } := {
    key := `minecraft.std.forceload
    template := .positional ["forceload"] }

/-- Set selected players' respawn positions. -/
@[expose] public def spawnpoint : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := SpawnLocation)]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.spawnpoint
    template := .positional ["spawnpoint"] }

/-- Set the world respawn position. -/
@[expose] public def worldSpawn : Oria.Command.Ref {
    schema := [ArgCodec.key (A := SpawnLocation)]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.worldSpawn
    template := .positional ["setworldspawn"] }

/-- Set one spectator's camera target. -/
@[expose] public def spectate : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target), ArgCodec.key (A := Players)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.spectate
    template := .positional ["spectate"] }

/-- Reset the executing spectator's camera. -/
@[expose] public def spectateStop : Oria.Command.Ref {
    schema := []
    req := Req.executor
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.spectateStop
    template := .positional ["spectate"] }

/-- Mount one entity on another. -/
@[expose] public def rideMount : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target), ArgCodec.key (A := Target)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.rideMount
    template := {parts := [.token "ride", .space, .slot ⟨0, by simp⟩, .space, .token "mount", .space, .slot ⟨1, by simp⟩]} }

/-- Dismount one entity. -/
@[expose] public def rideDismount : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.rideDismount
    template := {parts := [.token "ride", .space, .slot ⟨0, by simp⟩, .space, .token "dismount"]} }

/-- Rotate one entity or face a target. -/
@[expose] public def rotate : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target), ArgCodec.key (A := RotationAction)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.rotate
    template := .positional ["rotate"] }

/-- Randomly place entities on safe ground. -/
@[expose] public def spread : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Vec2), ArgCodec.key (A := SpreadSettings), ArgCodec.key (A := Target)]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.spread
    template := .positional ["spreadplayers"] }

/-- Send native particle packets. -/
@[expose] public def particle : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ParticleSpec), ArgCodec.key (A := ParticleSettings)]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.particle
    template := .positional ["particle"] }

/-- Animate selected living entities' hands. -/
@[expose] public def swing : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target), ArgCodec.key (A := SwingSettings)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.swing
    template := .positional ["swing"] }

/-- Add a client post-processing effect. -/
@[expose] public def postAdd : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := ResourceId)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.postAdd
    template := .positional ["posteffect", "add"] }

/-- Remove a client post-processing effect. -/
@[expose] public def postRemove : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := ResourceId)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.postRemove
    template := .positional ["posteffect", "remove"] }

/-- Clear client post-processing effects. -/
@[expose] public def postClear : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.postClear
    template := .positional ["posteffect", "clear"] }

/-- Query one player's active post-processing effects. -/
@[expose] public def postList : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.postList
    template := .positional ["posteffect", "list"] }

/-- Assign an objective to a display slot. -/
@[expose] public def objectiveSetDisplay : Oria.Command.Ref {
    schema := [ArgCodec.key (A := DisplaySlot), ArgCodec.key (A := Oria.Command.Objective)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.objectiveSetDisplay
    template := .positional ["scoreboard", "objectives", "setdisplay"] }

/-- Clear a display slot. -/
@[expose] public def objectiveClearDisplay : Oria.Command.Ref {
    schema := [ArgCodec.key (A := DisplaySlot)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.objectiveClearDisplay
    template := .positional ["scoreboard", "objectives", "setdisplay"] }

/-- Update an objective's presentation. -/
@[expose] public def objectiveModify : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Oria.Command.Objective), ArgCodec.key (A := ObjectiveProperty)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.objectiveModify
    template := .positional ["scoreboard", "objectives", "modify"] }

/-- Set score display names. -/
@[expose] public def scoreDisplayName : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Holders), ArgCodec.key (A := Oria.Command.Objective), ArgCodec.key (A := TextComponent)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.scoreDisplayName
    template := .positional ["scoreboard", "players", "display", "name"] }

/-- Reset score display names. -/
@[expose] public def scoreResetName : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Holders), ArgCodec.key (A := Oria.Command.Objective)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.scoreResetName
    template := .positional ["scoreboard", "players", "display", "name"] }

/-- Set or reset per-score number formats. -/
@[expose] public def scoreNumberFormat : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Holders), ArgCodec.key (A := Oria.Command.Objective), ArgCodec.key (A := ScoreFormat)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.scoreNumberFormat
    template := .positional ["scoreboard", "players", "display", "numberformat"] }

/-- Gameplay control and presentation declarations in the standard catalog. -/
@[expose] public def control : List Oria.Command.Decl :=
  [ruleGet.declaration,
    ruleSet.declaration,
    attributeRun.declaration,
    forceload.declaration,
    spawnpoint.declaration,
    worldSpawn.declaration,
    spectate.declaration,
    spectateStop.declaration,
    rideMount.declaration,
    rideDismount.declaration,
    rotate.declaration,
    spread.declaration,
    particle.declaration,
    swing.declaration,
    postAdd.declaration,
    postRemove.declaration,
    postClear.declaration,
    postList.declaration,
    objectiveSetDisplay.declaration,
    objectiveClearDisplay.declaration,
    objectiveModify.declaration,
    scoreDisplayName.declaration,
    scoreResetName.declaration,
    scoreNumberFormat.declaration]

end Oria.Std.Command.Declarations
