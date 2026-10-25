module

public import Oria
public import Oria.Datapack
meta import Oria
meta import Oria.Datapack

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Rock-paper-scissors

Build with `lake exe oria-rps output/rps` and install the resulting directory as a datapack.
Each player uses `/trigger rps.input set 4` to start or restart a match, then supplies
1 for rock, 2 for paper, or 3 for scissors. The first side to win two rounds wins the match.
Draws preserve the score. A finished match retains its final score until restarted.

`rps.active`, `rps.player`, and `rps.server` are per-player scoreboard values. Minecraft
saves them with the world. Load creates missing objectives; existing games survive reload.
Each tick initializes new players, enables the trigger, and consumes one pending input.
Zero is the empty-input sentinel; other invalid values produce a help message.

`receive` accepts a host-supplied program producing a typed `Choice`. The playable pack
uses a named random sequence, while server acceptance supplies a fixed move or failure.
Both constructions share input handling, scoring, and messages. `judge` demonstrates
multi-scrutinee matching over object enums. Named `.call` sites exercise function calls;
the acceptance pack uses the all-stack register budget.
-/

namespace Oria.Examples.RockPaperScissors

open Oria.Std Oria.Datapack

/-- The three moves accepted by the game. -/
public inductive Choice where
  /-- Beats scissors. -/
  | rock
  /-- Beats rock. -/
  | paper
  /-- Beats paper. -/
  | scissors
  deriving Oria.Object

/-- A round's result from the player's perspective. -/
public inductive Outcome where
  /-- Both sides chose the same move. -/
  | draw
  /-- The player's move wins. -/
  | win
  /-- The computer's move wins. -/
  | lose
  deriving Oria.Object

/-- Compare both moves in one pattern matrix. -/
@[mcfunction]
public def judge (player computer : Val Choice) : Prog .pure Outcome := do
  match player, computer with
  | .rock, .rock => .draw
  | .rock, .paper => .lose
  | .rock, .scissors => .win
  | .paper, .rock => .win
  | .paper, .paper => .draw
  | .paper, .scissors => .lose
  | .scissors, .rock => .lose
  | .scissors, .paper => .win
  | .scissors, .scissors => .draw

/-- Decode the checked input range 1 through 3. -/
@[mcfunction]
public def decode (n : Val Int32) : Prog .pure Choice := do
  match n with
  | 1 => .rock
  | 2 => .paper
  | _ => .scissors

/-- Per-player state and feedback require an executor. -/
@[expose] public def playerGrade : Grade :=
  (Scoreboard.enableGrade .self).seq (Tellraw.grade .self)

/-- The server-scoped random stream used for computer moves. -/
@[expose] public def drawGrade : Grade := Random.grade (some "rps:computer")

/-- Create objectives while preserving scores and trigger locks across reloads. -/
@[mcfunction]
public def setup : Prog (Grade.handled Scoreboard.objectiveGrade) Unit := do
  (Scoreboard.Objectives.add "rps.input" .trigger).ignore
  (Scoreboard.Objectives.add "rps.active" .dummy).ignore
  (Scoreboard.Objectives.add "rps.player" .dummy).ignore
  (Scoreboard.Objectives.add "rps.server" .dummy).ignore

@[mcfunction]
private def start : Prog playerGrade Int32 := do
  Scoreboard.set .self "rps.player" 0
  Scoreboard.set .self "rps.server" 0
  Scoreboard.set .self "rps.active" 1
  (Tellraw.text .self "First to two wins. /trigger rps.input set 1 = rock, 2 = paper, 3 = scissors.").ignore
  return 0

@[mcfunction]
private def prepare : Prog playerGrade Int32 := do
  try
    Scoreboard.get .self "rps.active"
    return 0
  catch _ =>
    Scoreboard.set .self "rps.player" 0
    Scoreboard.set .self "rps.server" 0
    Scoreboard.set .self "rps.active" 0
    (Tellraw.text .self "Rock-paper-scissors: /trigger rps.input set 4 starts a match.").ignore
    return 0

@[mcfunction]
private def announce (computer : Val Choice) : Prog (Grade.handled (Tellraw.grade .self)) Unit := do
  match computer with
  | .rock => (Tellraw.text .self "Server chose rock.").ignore
  | .paper => (Tellraw.text .self "Server chose paper.").ignore
  | .scissors => (Tellraw.text .self "Server chose scissors.").ignore

@[mcfunction]
private def scoreRound (outcome : Val Outcome) : Prog playerGrade Int32 := do
  match outcome with
  | .draw =>
    (Tellraw.text .self "Draw. Choose again.").ignore
    return 0
  | .win =>
    let n ← Scoreboard.get .self "rps.player"
    Scoreboard.set .self "rps.player" (n + 1)
    match n with
    | 1 =>
      Scoreboard.set .self "rps.active" 0
      (Tellraw.text .self "You win the match! /trigger rps.input set 4 starts another.").ignore
      return 3
    | _ =>
      (Tellraw.text .self "You win the round.").ignore
      return 1
  | .lose =>
    let n ← Scoreboard.get .self "rps.server"
    Scoreboard.set .self "rps.server" (n + 1)
    match n with
    | 1 =>
      Scoreboard.set .self "rps.active" 0
      (Tellraw.text .self "The server wins the match. /trigger rps.input set 4 starts another.").ignore
      return 4
    | _ =>
      (Tellraw.text .self "The server wins the round.").ignore
      return 2

@[mcfunction]
private def play (p : Val Int32) (computer : Val Choice) : Prog playerGrade Int32 := do
  let player ← decode.call p
  announce.call computer
  let outcome ← judge.call player computer
  scoreRound.call outcome

/-- Process one player's input. The draw action runs once for a valid move in an active match.
Supplying it at construction time lets acceptance tests select each computer move while
sharing the complete input and scoring logic with the random game. The input is consumed
before drawing; a failed draw propagates failure and leaves the match score unchanged.
Message failures are ignored, while scoreboard failures stop processing. -/
public def receive (draw : Prog drawGrade Choice) : Prog playerGrade Int32 := do
  prepare.call
  (Scoreboard.enable .self "rps.input").ignore
  let input ← Scoreboard.get .self "rps.input"
  match input with
  | 0 => return 0
  | input =>
    Scoreboard.set .self "rps.input" 0
    match input with
    | 4 => start.call
    | input =>
      if (input >= 1) && (input <= 3) then
        let active ← Scoreboard.get .self "rps.active"
        match active with
        | 1 =>
          let computer ← draw
          play.call input computer
        | _ =>
          (Tellraw.text .self "Start a match with /trigger rps.input set 4.").ignore
          return -1
      else
        (Tellraw.text .self "Choose 1 = rock, 2 = paper, 3 = scissors, or 4 = start/restart.").ignore
        return -1

@[mcfunction]
private def poll : Prog playerGrade Int32 :=
  receive (do
    let n ← Random.value (.between 1 3) (some "rps:computer")
    let computer ← decode.call n
    return computer)

/-- Tick callback: each online player has an independent match. -/
@[mcfunction]
public def tick : Prog (Grade.handled ⟨Req.none, playerGrade.eff⟩) Unit := do
  Execute.forEach [.as .allPlayers] do
    poll.call

/-- The playable datapack. Player input uses the native, permission-free trigger command. -/
@[datapack]
public def game : Spec := build { ns := "rps", description := "Oria rock-paper-scissors: first to two wins" } do
  onLoad setup.ref
  onTick tick.ref

end Oria.Examples.RockPaperScissors
