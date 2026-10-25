module

public import Oria.Std.Command.Arg.Registry
public import Oria.Std.Command.Arg.Management
public import Oria.Std.Command.Arg.Message

set_option doc.verso true
set_option linter.missingDocs true

namespace Oria.Std.Command.Declarations
open Oria.Std.Command.Arg
open Oria.Command (ArgCodec)

/-- Locate a structure ID or tag and return horizontal distance. -/
@[expose] public def locateStructure : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Oria.Command.ResourceOrTag)]
    req := Req.position ||| Req.dimension
    eff := Eff.world
  } := {
    key := `minecraft.std.locateStructure
    template := .positional ["locate", "structure"] }

/-- Locate a biome ID or tag and return three-dimensional distance. -/
@[expose] public def locateBiome : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Oria.Command.ResourceOrTag)]
    req := Req.position ||| Req.dimension
    eff := Eff.world
  } := {
    key := `minecraft.std.locateBiome
    template := .positional ["locate", "biome"] }

/-- Locate a point of interest and return horizontal distance. -/
@[expose] public def locatePoi : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Oria.Command.ResourceOrTag)]
    req := Req.position ||| Req.dimension
    eff := Eff.world
  } := {
    key := `minecraft.std.locatePoi
    template := .positional ["locate", "poi"] }

/-- Broadcast a native chat message. -/
@[expose] public def chatSay : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Message)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.chat
  } := {
    key := `minecraft.std.chatSay
    template := .positional ["say"] }

/-- Send a private native message to selected players. -/
@[expose] public def chatTell : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := Message)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.chat
  } := {
    key := `minecraft.std.chatTell
    template := .positional ["msg"] }

/-- Send a message to the executor's team. -/
@[expose] public def chatTeam : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Message)]
    req := Req.executor
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.chat
  } := {
    key := `minecraft.std.chatTeam
    template := .positional ["teammsg"] }

/-- Broadcast an emote attributed to the command source. -/
@[expose] public def chatMe : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Message)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.chat
  } := {
    key := `minecraft.std.chatMe
    template := .positional ["me"] }

/-- List online players and return their count. -/
@[expose] public def onlinePlayers : Oria.Command.Ref {
    schema := []
    req := Req.none
    eff := Eff.world
  } := {
    key := `minecraft.std.onlinePlayers
    template := .positional ["list"] }

/-- List online players with UUIDs and return their count. -/
@[expose] public def onlinePlayersUuids : Oria.Command.Ref {
    schema := []
    req := Req.none
    eff := Eff.world
  } := {
    key := `minecraft.std.onlinePlayersUuids
    template := .positional ["list", "uuids"] }

/-- Print the world's full seed and return its low signed I32 bits. -/
@[expose] public def worldSeed : Oria.Command.Ref {
    schema := []
    req := Req.dimension
    eff := Eff.world
  } := {
    key := `minecraft.std.worldSeed
    template := .positional ["seed"] }

/-- Print native version information and return 1. -/
@[expose] public def serverVersion : Oria.Command.Ref {
    schema := []
    req := Req.none
    eff := Eff.world
  } := {
    key := `minecraft.std.serverVersion
    template := .positional ["version"] }

/-- Add a nonnegative amount to selected scores and return their new sum. -/
@[expose] public def scoreAdd : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Holders), ArgCodec.key (A := Oria.Command.Objective), ArgCodec.key (A := Scalar)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random
  } := {
    key := `minecraft.std.scoreAdd
    cost := some 1
    template := .positional ["scoreboard", "players", "add"] }

/-- Subtract a nonnegative amount from selected scores and return their new sum. -/
@[expose] public def scoreRemove : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Holders), ArgCodec.key (A := Oria.Command.Objective), ArgCodec.key (A := Scalar)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random
  } := {
    key := `minecraft.std.scoreRemove
    cost := some 1
    template := .positional ["scoreboard", "players", "remove"] }

/-- Discovery, chat, information, and score updates in the standard catalog. -/
@[expose] public def utility : List Oria.Command.Decl :=
  [locateStructure.declaration,
    locateBiome.declaration,
    locatePoi.declaration,
    chatSay.declaration,
    chatTell.declaration,
    chatTeam.declaration,
    chatMe.declaration,
    onlinePlayers.declaration,
    onlinePlayersUuids.declaration,
    worldSeed.declaration,
    serverVersion.declaration,
    scoreAdd.declaration,
    scoreRemove.declaration]

end Oria.Std.Command.Declarations
