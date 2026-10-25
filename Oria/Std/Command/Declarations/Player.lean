module

public import Oria.Std.Command.Arg.Gameplay

set_option doc.verso true
set_option linter.missingDocs true

namespace Oria.Std.Command.Declarations

open Oria.Std.Command.Arg
open Oria.Command (ArgCodec)

/-- Set selected players' game mode. -/
@[expose] public def gameMode : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Oria.Command.GameMode), ArgCodec.key (A := Players)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.chat
  } := {
    key := `minecraft.std.gameMode
    template := .positional ["gamemode"] }

/-- Set the server's default mode. -/
@[expose] public def defaultGameMode : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Oria.Command.GameMode)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.chat
  } := {
    key := `minecraft.std.defaultGameMode
    template := .positional ["defaultgamemode"] }

/-- Add experience. -/
@[expose] public def experienceAdd : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := Scalar), ArgCodec.key (A := ExperienceUnit)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.chat
  } := {
    key := `minecraft.std.experienceAdd
    template := .positional ["experience", "add"] }

/-- Set experience. -/
@[expose] public def experienceSet : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := Scalar), ArgCodec.key (A := ExperienceUnit)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.chat
  } := {
    key := `minecraft.std.experienceSet
    template := .positional ["experience", "set"] }

/-- Query one player's experience. -/
@[expose] public def experienceQuery : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := ExperienceUnit)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.chat
  } := {
    key := `minecraft.std.experienceQuery
    template := .positional ["experience", "query"] }

/-- Unlock selected recipes. -/
@[expose] public def recipeGive : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := ResourceSet)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.chat
  } := {
    key := `minecraft.std.recipeGive
    template := .positional ["recipe", "give"] }

/-- Remove selected recipes. -/
@[expose] public def recipeTake : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := ResourceSet)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.chat
  } := {
    key := `minecraft.std.recipeTake
    template := .positional ["recipe", "take"] }

/-- Enchant held items. -/
@[expose] public def enchant : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target), ArgCodec.key (A := ResourceId), ArgCodec.key (A := Scalar)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.chat
  } := {
    key := `minecraft.std.enchant
    template := .positional ["enchant"] }

/-- Apply generic damage. -/
@[expose] public def damage : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target), ArgCodec.key (A := Decimal)]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.chat
  } := {
    key := `minecraft.std.damage
    template := .positional ["damage"] }

/-- Apply attributed damage. -/
@[expose] public def damageFrom : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Target), ArgCodec.key (A := Decimal), ArgCodec.key (A := DamageCause)]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.chat
  } := {
    key := `minecraft.std.damageFrom
    template := .positional ["damage"] }

/-- Grant advancement progress and native rewards. -/
@[expose] public def advancementGrant : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := AdvancementScope)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud |||
      Eff.chat ||| Eff.sound ||| Eff.dialog ||| Eff.persistentRead ||| Eff.persistentWrite |||
      Eff.persistentAlloc
  } := {
    key := `minecraft.std.advancementGrant
    template := .positional ["advancement", "grant"] }

/-- Revoke advancement progress. -/
@[expose] public def advancementRevoke : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := AdvancementScope)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.chat
  } := {
    key := `minecraft.std.advancementRevoke
    template := .positional ["advancement", "revoke"] }

/-- Player command declarations included in the standard catalog. -/
@[expose] public def player : List Oria.Command.Decl :=
  [gameMode.declaration,
    defaultGameMode.declaration,
    experienceAdd.declaration,
    experienceSet.declaration,
    experienceQuery.declaration,
    recipeGive.declaration,
    recipeTake.declaration,
    enchant.declaration,
    damage.declaration,
    damageFrom.declaration,
    advancementGrant.declaration,
    advancementRevoke.declaration]

end Oria.Std.Command.Declarations
