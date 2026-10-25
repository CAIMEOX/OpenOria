module

public import Oria.Std.Command.Arg.Scoreboard

set_option doc.verso true
set_option linter.missingDocs true

namespace Oria.Std.Command.Declarations
open Oria.Std.Command.Arg
open Oria.Command (ArgCodec)

/-- Count native objectives. -/
@[expose] public def objectiveList : Oria.Command.Ref {
    schema := []
    req := Req.none
    eff := Eff.scoreboardRead
  } := {
    key := `minecraft.std.objectiveList
    template := .positional ["scoreboard", "objectives", "list"] }

/-- Count tracked score holders. -/
@[expose] public def scoreList : Oria.Command.Ref {
    schema := []
    req := Req.none
    eff := Eff.scoreboardRead
  } := {
    key := `minecraft.std.scoreList
    template := .positional ["scoreboard", "players", "list"] }

/-- Count a holder's score entries. -/
@[expose] public def scoreListOf : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ScoreHolder)]
    req := Req.none
    eff := Eff.scoreboardRead
  } := {
    key := `minecraft.std.scoreListOf
    template := .positional ["scoreboard", "players", "list"] }

/-- Set selected scores and return their sum. -/
@[expose] public def scoreSetGroup : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Scores), ArgCodec.key (A := Scalar)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random
  } := {
    key := `minecraft.std.scoreSetGroup
    template := .positional ["scoreboard", "players", "set"] }

/-- Remove selected score entries. -/
@[expose] public def scoreResetGroup : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Scores)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random
  } := {
    key := `minecraft.std.scoreResetGroup
    template := .positional ["scoreboard", "players", "reset"] }

/-- Remove selected holders' scores across objectives. -/
@[expose] public def scoreResetGroupAll : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Holders)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random
  } := {
    key := `minecraft.std.scoreResetGroupAll
    template := .positional ["scoreboard", "players", "reset"] }

/-- Unlock selected trigger scores. -/
@[expose] public def scoreEnableGroup : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Scores)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random
  } := {
    key := `minecraft.std.scoreEnableGroup
    template := .positional ["scoreboard", "players", "enable"] }

/-- Apply an operation for every target/source pair. -/
@[expose] public def scoreOperationGroup : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Scores), ArgCodec.key (A := Oria.Command.ScoreOp), ArgCodec.key (A := Scores)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random
  } := {
    key := `minecraft.std.scoreOperationGroup
    template := .positional ["scoreboard", "players", "operation"] }

/-- Score inspection and bulk score mutation declarations. -/
@[expose] public def scores : List Oria.Command.Decl :=
  [objectiveList.declaration,
    scoreList.declaration,
    scoreListOf.declaration,
    scoreSetGroup.declaration,
    scoreResetGroup.declaration,
    scoreResetGroupAll.declaration,
    scoreEnableGroup.declaration,
    scoreOperationGroup.declaration]

end Oria.Std.Command.Declarations
