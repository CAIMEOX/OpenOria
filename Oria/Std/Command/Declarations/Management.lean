module

public import Oria.Std.Command.Arg.Management

set_option doc.verso true
set_option linter.missingDocs true

namespace Oria.Std.Command.Declarations

open Oria.Std.Command.Arg
open Oria.Command (ArgCodec)

/-- Create a custom boss bar. -/
@[expose] public def barAdd : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ResourceId), ArgCodec.key (A := TextComponent)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.barAdd
    template := .positional ["bossbar", "add"] }

/-- Remove a boss bar. -/
@[expose] public def barRemove : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ResourceId)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.barRemove
    template := .positional ["bossbar", "remove"] }

/-- List boss bars. -/
@[expose] public def barList : Oria.Command.Ref {
    schema := []
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.barList
    template := .positional ["bossbar", "list"] }

/-- Query a boss-bar field. -/
@[expose] public def barGet : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ResourceId), ArgCodec.key (A := BarField)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.barGet
    template := .positional ["bossbar", "get"] }

/-- Set a boss-bar property. -/
@[expose] public def barSet : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ResourceId), ArgCodec.key (A := BarProperty)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.barSet
    template := .positional ["bossbar", "set"] }

/-- Create a team with its default display name. -/
@[expose] public def teamAdd : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Oria.Command.Word)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.teamAdd
    template := .positional ["team", "add"] }

/-- Create a team with a display name. -/
@[expose] public def teamAddNamed : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Oria.Command.Word), ArgCodec.key (A := TextComponent)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.teamAddNamed
    template := .positional ["team", "add"] }

/-- Remove a team. -/
@[expose] public def teamRemove : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Oria.Command.Word)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.teamRemove
    template := .positional ["team", "remove"] }

/-- Remove all team members. -/
@[expose] public def teamEmpty : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Oria.Command.Word)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.teamEmpty
    template := .positional ["team", "empty"] }

/-- List teams. -/
@[expose] public def teamList : Oria.Command.Ref {
    schema := []
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.teamList
    template := .positional ["team", "list"] }

/-- List a team's members. -/
@[expose] public def teamMembers : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Oria.Command.Word)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.teamMembers
    template := .positional ["team", "list"] }

/-- Join selected score holders to a team. -/
@[expose] public def teamJoin : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Oria.Command.Word), ArgCodec.key (A := Holders)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.teamJoin
    template := .positional ["team", "join"] }

/-- Remove holders from their teams. -/
@[expose] public def teamLeave : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Holders)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.teamLeave
    template := .positional ["team", "leave"] }

/-- Change a typed team property. -/
@[expose] public def teamModify : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Oria.Command.Word), ArgCodec.key (A := TeamProperty)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud
  } := {
    key := `minecraft.std.teamModify
    template := .positional ["team", "modify"] }

/-- Management command declarations included in the standard catalog. -/
@[expose] public def management : List Oria.Command.Decl :=
  [barAdd.declaration,
    barRemove.declaration,
    barList.declaration,
    barGet.declaration,
    barSet.declaration,
    teamAdd.declaration,
    teamAddNamed.declaration,
    teamRemove.declaration,
    teamEmpty.declaration,
    teamList.declaration,
    teamMembers.declaration,
    teamJoin.declaration,
    teamLeave.declaration,
    teamModify.declaration]

end Oria.Std.Command.Declarations
