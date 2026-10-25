module

public import Oria.Std.Command.Arg.World

set_option doc.verso true
set_option linter.missingDocs true

namespace Oria.Std.Command.Declarations

open Oria.Std.Command.Arg
open Oria.Command (ArgCodec)

/-- Choose native weather with a sampled duration. -/
@[expose] public def weather : Oria.Command.Ref {
    schema := [ArgCodec.key (A := WeatherKind)]
    req := Req.dimension
    eff := Eff.world ||| Eff.random
  } := {
    key := `minecraft.std.weather
    template := .positional ["weather"] }

/-- Choose weather for an explicit duration. -/
@[expose] public def weatherFor : Oria.Command.Ref {
    schema := [ArgCodec.key (A := WeatherKind), ArgCodec.key (A := Time)]
    req := Req.none
    eff := Eff.world
  } := {
    key := `minecraft.std.weatherFor
    template := .positional ["weather"] }

/-- Operate on the source dimension's default clock. -/
@[expose] public def clock : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ClockAction)]
    req := Req.dimension
    eff := Eff.world
  } := {
    key := `minecraft.std.clock
    template := .positional ["time"] }

/-- Operate on a named world clock. -/
@[expose] public def clockOf : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ResourceId), ArgCodec.key (A := ClockAction)]
    req := Req.none
    eff := Eff.world
  } := {
    key := `minecraft.std.clockOf
    template := .positional ["time", "of"] }

/-- Query elapsed game ticks. -/
@[expose] public def gameTime : Oria.Command.Ref {
    schema := []
    req := Req.dimension
    eff := Eff.world
  } := {
    key := `minecraft.std.gameTime
    template := .positional ["time", "query", "gametime"] }

/-- Query native difficulty. -/
@[expose] public def difficultyGet : Oria.Command.Ref {
    schema := []
    req := Req.dimension
    eff := Eff.world
  } := {
    key := `minecraft.std.difficultyGet
    template := .positional ["difficulty"] }

/-- Set server difficulty. -/
@[expose] public def difficultySet : Oria.Command.Ref {
    schema := [ArgCodec.key (A := DifficultyLevel)]
    req := Req.none
    eff := Eff.world
  } := {
    key := `minecraft.std.difficultySet
    template := .positional ["difficulty"] }

/-- Operate on the source dimension's border. -/
@[expose] public def border : Oria.Command.Ref {
    schema := [ArgCodec.key (A := BorderAction)]
    req := Req.dimension
    eff := Eff.world
  } := {
    key := `minecraft.std.border
    template := .positional ["worldborder"] }

/-- World command declarations included in the standard catalog. -/
@[expose] public def world : List Oria.Command.Decl :=
  [weather.declaration,
    weatherFor.declaration,
    clock.declaration,
    clockOf.declaration,
    gameTime.declaration,
    difficultyGet.declaration,
    difficultySet.declaration,
    border.declaration]

end Oria.Std.Command.Declarations
