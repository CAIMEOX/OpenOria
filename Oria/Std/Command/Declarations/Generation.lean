module

public import Oria.Std.Command.Arg.Generation
public import Oria.Std.Command.Arg.Waypoint

set_option doc.verso true
set_option linter.missingDocs true

namespace Oria.Std.Command.Declarations
open Oria.Std.Command.Arg
open Oria.Command (ArgCodec)

/-- Replace biome cells in an inclusive block region. -/
@[expose] public def fillBiome : Oria.Command.Ref {
    schema := [ArgCodec.key (A := BlockBox), ArgCodec.key (A := ResourceId)]
    req := Req.dimension
    eff := Eff.world
  } := {
    key := `minecraft.std.fillBiome
    template := .positional ["fillbiome"] }

/-- Replace only cells whose current biome matches an ID or tag. -/
@[expose] public def fillBiomeFiltered : Oria.Command.Ref {
    schema := [ArgCodec.key (A := BlockBox), ArgCodec.key (A := ResourceId), ArgCodec.key (A := Oria.Command.ResourceOrTag)]
    req := Req.dimension
    eff := Eff.world
  } := {
    key := `minecraft.std.fillBiomeFiltered
    template := {parts := [
      .token "fillbiome", .space, .slot ⟨0, by decide⟩, .space, .slot ⟨1, by decide⟩,
      .space, .token "replace", .space, .slot ⟨2, by decide⟩]} }

/-- Place a named or inline world-generation feature. -/
@[expose] public def placeFeature : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Feature), ArgCodec.key (A := BlockPos)]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound
  } := {
    key := `minecraft.std.placeFeature
    template := .positional ["place", "feature"] }

/-- Generate a jigsaw pool from a named connector. -/
@[expose] public def placeJigsaw : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ResourceId), ArgCodec.key (A := ResourceId), ArgCodec.key (A := Scalar), ArgCodec.key (A := BlockPos)]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound
  } := {
    key := `minecraft.std.placeJigsaw
    template := .positional ["place", "jigsaw"] }

/-- Generate a registered structure using the world's generator. -/
@[expose] public def placeStructure : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ResourceId), ArgCodec.key (A := BlockPos)]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound
  } := {
    key := `minecraft.std.placeStructure
    template := .positional ["place", "structure"] }

/-- Place a structure template with explicit transformation and randomness settings. -/
@[expose] public def placeTemplate : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ResourceId), ArgCodec.key (A := BlockPos), ArgCodec.key (A := TemplateSettings)]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound
  } := {
    key := `minecraft.std.placeTemplate
    template := .positional ["place", "template"] }

/-- List the current dimension's tracked waypoint transmitters. -/
@[expose] public def waypointList : Oria.Command.Ref {
    schema := []
    req := Req.dimension
    eff := Eff.world
  } := {
    key := `minecraft.std.waypointList
    template := .positional ["waypoint", "list"] }

/-- Change one transmitter's waypoint icon. -/
@[expose] public def waypointModify : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target), ArgCodec.key (A := WaypointProperty)]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.waypointModify
    template := .positional ["waypoint", "modify"] }

/-- Create a server-wide real-time stopwatch. -/
@[expose] public def stopwatchCreate : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ResourceId)]
    req := Req.none
    eff := Eff.world
  } := {
    key := `minecraft.std.stopwatchCreate
    template := .positional ["stopwatch", "create"] }

/-- Return elapsed seconds multiplied by the scale and truncated to I32. -/
@[expose] public def stopwatchQuery : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ResourceId), ArgCodec.key (A := Decimal)]
    req := Req.none
    eff := Eff.world
  } := {
    key := `minecraft.std.stopwatchQuery
    template := .positional ["stopwatch", "query"] }

/-- Restart an existing real-time stopwatch. -/
@[expose] public def stopwatchRestart : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ResourceId)]
    req := Req.none
    eff := Eff.world
  } := {
    key := `minecraft.std.stopwatchRestart
    template := .positional ["stopwatch", "restart"] }

/-- Remove an existing real-time stopwatch. -/
@[expose] public def stopwatchRemove : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ResourceId)]
    req := Req.none
    eff := Eff.world
  } := {
    key := `minecraft.std.stopwatchRemove
    template := .positional ["stopwatch", "remove"] }

/-- Generation, navigation, and timing declarations in the standard catalog. -/
@[expose] public def generation : List Oria.Command.Decl :=
  [fillBiome.declaration,
    fillBiomeFiltered.declaration,
    placeFeature.declaration,
    placeJigsaw.declaration,
    placeStructure.declaration,
    placeTemplate.declaration,
    waypointList.declaration,
    waypointModify.declaration,
    stopwatchCreate.declaration,
    stopwatchQuery.declaration,
    stopwatchRestart.declaration,
    stopwatchRemove.declaration]

end Oria.Std.Command.Declarations
