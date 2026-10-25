module

public import Oria
public meta import Oria

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Standard library examples

These declarations use public interfaces and ordinary `do` notation. During compilation,
`@[mcfunction]` constructs and checks each Tree, so the examples are checked as interfaces
evolve. The application's initialization must prepare the objectives and external storage.
The generated programs run in Minecraft; compiling these Lean declarations constructs code.
-/

namespace Oria.Examples.StandardLibrary

open Oria Oria.Std Oria.Std.Command.Arg

private def points : Command.Objective := "demo.points"
/-- Application-owned NBT storage used by these examples. -/
public def store : DataTarget := .storage "demo:state"
/-- A reusable host coordinate constructor that preserves the type of a dynamic X component. -/
@[expose] public def ground (x : Scalar) : Vec3 :=
  .world (.absolute x) (.absolute 64) (.relative 0)

/-- Read a named score and add one. The do block propagates failure if the score is absent. -/
@[mcfunction]
public def readNext : Prog (Scoreboard.readGrade (.named "#counter")) Int32 := do
  let n ← Scoreboard.get (.named "#counter") points
  return n + 1

/-- Compose object programs through a named call, propagating the callee's failure. -/
@[mcfunction]
public def twiceNext : Prog (Scoreboard.readGrade (.named "#counter")) Int32 := do
  let n ← readNext.call
  return n * 2

/-- Recover an absent counter with zero, producing an ordinary object value. -/
@[mcfunction]
public def readDefault : Prog (Scoreboard.readGrade (.named "#counter")).handled Int32 :=
  Prog.getD (Scoreboard.get (.named "#counter") points) 0

/-- Write a runtime arithmetic expression directly as a numeric command parameter. -/
@[mcfunction]
public def writeNext (n : Val Int32) : Prog (Scoreboard.writeGrade (.named "#counter")) Int32 :=
  Scoreboard.set (.named "#counter") points (n + 1)

/-- Map a successful score while retaining the command's failure outcome. -/
@[mcfunction]
public def mapScore : Prog (Scoreboard.readGrade (.named "#counter")) Int32 :=
  Prog.map (fun n => n * 2) (Scoreboard.get (.named "#counter") points)

/-- Retry an absent counter using another score; both reads execute at most once. -/
@[mcfunction]
public def readFallback : Prog (Scoreboard.readGrade (.named "#counter")) Int32 :=
  Prog.orElse (Scoreboard.get (.named "#counter") points)
    (Scoreboard.get (.named "#backup") points)

/-- Mix a dynamic X with a static Y and relative Z.
The calling context supplies the executor and relative position. -/
@[mcfunction]
public def moveX (x : Val Int32) : Prog
    ⟨Req.executor ||| Req.position ||| Req.dimension,
      Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩ Int32 := do
  Teleport.to .self (ground x)

/-- Combine a runtime X coordinate with host decimal Y and relative Z components. -/
@[mcfunction]
public def movePrecisely (x : Val Int32) : Prog
    ⟨Req.executor ||| Req.position ||| Req.dimension,
      Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩ Int32 := do
  Teleport.to .self (.world (.absolute x) (.absolute 64.25) (.relative (-0.5)))

/-- Use the uniform absolute-coordinate constructor with a runtime X and host fractions. -/
@[mcfunction]
public def moveAbsolute (x : Val Int32) : Prog
    ⟨Req.executor ||| Req.dimension,
      Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩ Int32 := do
  Teleport.to .self (Vec3.absolute x 64.25 0.0)

/-- Offset all three world axes from the current execution position. -/
@[mcfunction]
public def moveRelative (x : Val Int32) : Prog
    ⟨Req.executor ||| Req.position ||| Req.dimension,
      Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩ Int32 := do
  Teleport.to .self (Vec3.relative x 0 (-1.5))

/-- Broadcast literal text from a server context, suitable for a load or tick callback. -/
@[mcfunction]
public def announce : Prog (Grade.handled (Tellraw.grade .all)) Unit :=
  (Tellraw.text .all "Loaded").ignore

/-- Sample a value, send it as a dynamic number, and return it.
Failure at either step ends this invocation. -/
@[mcfunction]
public def announceRoll : Prog ((Random.grade none).seq (Tellraw.grade .self)) Int32 := do
  let n ← Random.value (.between 1 6)
  Tellraw.number .self n
  return n

/-- Read a number by dynamic index from a statically filtered selection.
The unique read fails for an empty collection or an out-of-bounds index. -/
@[mcfunction]
public def selectedNumber (i : Val Int32) : Prog (Data.grade store) Int32 := do
  let path := ((Nbt.Path.key "tasks").matching (nbt% {owner: "Ada"})).field "n"
  let values ← Data.readAll store (some path)
  let value ← Nbt.readOne values (some ⟨.index (.dynamic i), []⟩)
  Nbt.toI32 value

/-- Run the body once per player. The as step supplies an executor for self in the body. -/
@[mcfunction]
public def initializePlayers : Prog
    ⟨Req.none, Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random⟩ Unit :=
  Execute.forEach [.as .allPlayers] do
    Scoreboard.set .self points 1

/-- Reuse structured tag and score filters without requiring a caller-side executor. -/
@[mcfunction]
public def initializePlaying : Prog
    ⟨Req.none, Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random⟩ Unit := do
  let players : Command.Selector := .allPlayers {
    tags := [.include "playing"]
    scores := [(points, .between 1 3)] }
  Execute.forEach [.as players] do
    Scoreboard.set .self points 1

/-- Inspect each player's held item, then store the last matching player's score.
The as/at chain supplies the context used by self and the slot selection. -/
@[mcfunction]
public def recordHeldItemScore : Prog
    ⟨Req.none, Eff.world ||| Eff.scoreboardRead ||| Eff.random⟩ Unit := do
  Execute.forEach [
    .as (.allPlayers {gameMode := some (.exclude .spectator)}),
    .at .self,
    .when (.items ⟨.entity .self, .range "weapon.mainhand"⟩ {target := some (.id "minecraft:apple")}),
    .storeResult (.nbt (.storage "demo:state") (.key "score") .int 1)] do
      Scoreboard.get .self points

/-- Follow a passenger's vehicle; use at explicitly to move the execution position with it. -/
@[mcfunction]
public def tagVehicle :=
  Execute.forEach [.on .vehicle, .at .self] do
    Tag.add .self "occupied"

/-- Place an entity at the column's heightmap height and initialize its score. -/
@[mcfunction]
public def markSurface :=
  Execute.forEach [.positionedOver .motionBlockingNoLeaves, .summon "minecraft:marker"] do
    Scoreboard.set .self points 1

/-- Copy a target entity's dimension, coordinates, and rotation. -/
@[mcfunction]
public def returnToCheckpoint := Teleport.entity .self
  (.selector (.allEntities {tags := [.include "checkpoint"], limit := some 1}))

/-- Apply fractional angles while teleporting; both commands share RotationAction. -/
@[mcfunction]
public def faceArena := Teleport.to .self (ground 0)
  (some (.angles ⟨.absolute 90.5, .absolute 0⟩))

/-- Replace an arena's biome samples, filtering existing overworld biome entries. -/
@[mcfunction]
public def desertArena := FillBiome.run
  ⟨.here, .relative 15 7 15⟩
  "minecraft:desert" (some (.tag "minecraft:is_overworld"))

/-- Place a room with native template settings in a single host record. -/
@[mcfunction]
public def buildRoom := Place.template "demo:room" .here {
  rotation := .clockwise90
  mirror := .frontBack
  integrity := 0.95
  seed := 42
  strict := true }

/-- Construct a feature with the shared NBT syntax and placement-supplied context. -/
@[mcfunction]
public def placePrize := Place.feature (Feature.ofNbt
  (nbt% {type: "minecraft:simple_block", to_place: {id: "minecraft:gold_block"}}))

/-- Give each player's locator-bar icon the same host RGB color. Successful zero is retained. -/
@[mcfunction]
public def colorPlayerWaypoints : Prog
    ⟨Req.dimension, Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.hud⟩ Unit := do
  Execute.forEach [.as .allPlayers] do
    Waypoint.modify .self (.hex "6495ED")

/-- Measure one placement using server-running real time and return elapsed milliseconds.
The create result is discarded so an existing stopwatch can be reused before restart. -/
@[mcfunction]
public def timedRoom : Prog (Place.grade .here) Int32 := do
  (Stopwatch.create "demo:placement").ignore
  Stopwatch.restart "demo:placement"
  Place.template "demo:room" .here {seed := .static 42}
  Stopwatch.query "demo:placement" (.static 1000)

/-- Broadcast plain chat without requiring an executor, suitable for a load callback. -/
@[mcfunction]
public def announceReady := Chat.say "The arena is ready."

/-- Compose entity-name expansion with a runtime integer. Message.join keeps selector
boundaries separate from surrounding native message text. -/
@[mcfunction]
public def announcePoints (n : Val Int32) :
    Prog (Chat.grade (.selector .self)) Int32 := do
  Chat.say (Message.join "Player" [.selector .self, "scored", .number (.dynamic n)])

/-- Add a native amount to every selected score; the payload is their resulting sum. -/
@[mcfunction]
public def rewardPlayers := Scoreboard.add (.entities (.selector .allPlayers)) points (.static 1)

/-- Query a native POI distance from each player's own position and report it privately. -/
@[mcfunction]
public def reportMeetingDistance := Execute.forEach [.as .allPlayers, .at .self] do
  let distance ← Locate.poi (.id "minecraft:meeting")
  Chat.tell .self (Message.join "Meeting distance:" [.number (.dynamic distance)])

/-- Obtain a player count as an ordinary runtime I32. -/
@[mcfunction]
public def recordOnlinePlayers : Prog
    ⟨Req.none, Eff.world ||| Eff.scoreboardWrite ||| Eff.failure⟩ Int32 := do
  let n ← ServerInfo.players
  Scoreboard.set (.named "#online") points (.dynamic n)

/-- Evaluate a constant provider with the native position/dimension context requirement. -/
@[mcfunction]
public def computeSeven : Prog (Compute.grade .default) Int32 := do
  Compute.run .default (.integer (.ofNbt (7 : Int32)))

/-- Send a notice and return immediately. The result describes the send operation. -/
@[mcfunction]
public def welcome : Prog (Dialog.grade .all) Int32 :=
  Dialog.notice .all "Ready" "Choose your next action."

/-- Create a player input objective while preserving its scores across reloads. -/
@[mcfunction]
public def prepareInput : Prog (Grade.handled Scoreboard.objectiveGrade) Unit :=
  (Scoreboard.Objectives.add "game.choice" .trigger).ignore

/-- Enable the executing player's input and read its current value.
An already-enabled score is retained; input consumption and reset belong to the caller. -/
@[mcfunction]
public def readInput : Prog (Scoreboard.enableGrade .self) Int32 := do
  (Scoreboard.enable .self "game.choice").ignore
  Scoreboard.get .self "game.choice"

/-- Select entities carrying the temporary tag used by the spawning example. -/
@[expose] public def temporary : Target := .selector (.allEntities { tags := [.include "demo.temporary"] })

/-- Remove temporary entities; cleanup can continue when the selection is already empty. -/
@[mcfunction]
public def cleanup : Prog (Grade.handled (Kill.grade temporary)) Unit := (Kill.run temporary).ignore

/-- Supply a dynamic offset and age while preserving static NBT fields and decimal coordinates. -/
@[mcfunction]
public def spawnYoungPig (offset age : Val Int32) : Prog
    ⟨Req.dimension ||| Req.position,
      Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.failure⟩ Int32 := do
  let pos := Vec3.world (.relative (.dynamic offset))
    (.relative (.decimal 0.25)) (.relative (.decimal 0.5))
  Summon.at "minecraft:pig" pos (some (.fields [
    (⟨"Tags"⟩, .nbt (nbt% ["demo.temporary"])),
    (⟨"Age"⟩, .hole .i32 age)]))

/-- Apply a dynamic-duration speed effect to the executor, with zero-based amplifier one. -/
@[mcfunction]
public def speedBoost (seconds : Val Int32) : Prog (Effect.grade .self) Int32 :=
  Effect.giveFor .self "minecraft:speed" (.finite (.dynamic seconds)) (.static 1)

/-- Announce a round, mark participating players, and play a cue from each player's position.
The execution chain supplies the body's executor and positional context. -/
@[mcfunction]
public def announceRound : Prog
    ⟨Req.none, Eff.hud ||| Eff.sound ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random⟩ Unit := do
  (Title.times .all (.ticks (.static 5)) (.seconds (.static 2)) (.ticks (.static 10))).ignore
  (Title.show .all (.literal "Round start")).ignore
  Execute.forEach [.as .allPlayers, .at .self] do
    (Tag.add .self "game.playing").ignore
    Sound.play .self "minecraft:entity.player.levelup" .player

/-- Display a computed counter without an executor requirement at the caller. -/
@[mcfunction]
public def countdown (remaining : Val Int32) : Prog (Title.grade .all) Int32 := do
  Title.show .all (.number (.dynamic remaining)) .actionbar

/-- Prepare native arena settings, a team, and a round boss bar. Repeated setup discards
unchanged/existing-state failures while preserving the commands' effects. -/
@[mcfunction]
public def prepareArena : Prog
    ⟨Req.dimension, Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud⟩ Unit := do
  (Weather.set .clear (some (.seconds (.static 60)))).ignore
  (WorldBorder.run (.set (.static 256) none)).ignore
  (Team.add "arena.red" (some (.literal "Red team"))).ignore
  (Bossbar.add "arena:round" (.literal "Round progress")).ignore
  (Bossbar.set "arena:round" (.max (.static 3))).ignore

/-- Join a team, select adventure mode, and award one level. A successful zero from an
unchanged game-mode request still allows experience to be added. -/
@[mcfunction]
public def joinArena : Prog (GameMode.grade .self) Int32 := do
  (Team.join "arena.red").ignore
  GameMode.set .adventure
  Experience.add .self (.static 1) .levels

/-- Select one team's members using the shared structured selector. -/
@[expose] public def redTeam : Players :=
  .selector (.allPlayers {team := some (.include "arena.red")})

/-- Configure death behavior and the rate of native random block updates. Boolean rule
values are host data; integer values can also be supplied dynamically. -/
@[mcfunction]
public def arenaRules : Prog (Grade.handled Gamerule.grade) Unit := do
  (Gamerule.set .keepInventory true).ignore
  (Gamerule.set .immediateRespawn true).ignore
  (Gamerule.set .randomTickSpeed (.static 0)).ignore

/-- Update a typed game rule from an object integer. -/
@[mcfunction]
public def randomTickRate (n : Val Int32) : Prog Gamerule.grade Int32 := do
  Gamerule.set .randomTickSpeed (.dynamic n)

/-- Give the red team a respawn point at the command position and an explicit rotation. -/
@[mcfunction]
public def teamRespawn := Spawnpoint.set redTeam
  (.atPos (.world (.relative (.static 0)) (.relative (.static 0)) (.relative (.static 0)))
    (some ⟨.absolute (.static 90), .absolute (.static 0)⟩))

/-- Create a sidebar and choose a fixed label instead of its numeric column. -/
@[mcfunction]
public def showRoundSidebar : Prog (Grade.handled Scoreboard.displayGrade) Unit := do
  (Scoreboard.Objectives.add "arena.round" .dummy).ignore
  (Scoreboard.Objectives.modify "arena.round" (.displayName (.literal "Round"))).ignore
  (Scoreboard.Objectives.modify "arena.round" (.numberFormat (.fixed (.literal "★")))).ignore
  (Scoreboard.Objectives.setDisplay .sidebar (some "arena.round")).ignore

/-- Send a dust particle whose native options mix static NBT with a computed scale.
Minecraft checks the scale range after macro substitution. -/
@[mcfunction]
public def dust (scale : Val Int32) : Prog
    ⟨Req.dimension ||| Req.position,
      Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.hud ||| Eff.failure⟩ Int32 := do
  Particle.send {
    id := "minecraft:dust"
    options := .fields [
      (⟨"color"⟩, .nbt (nbt% [1.0, 0.0, 0.0])),
      (⟨"scale"⟩, .hole .i32 scale)] }

/-- Give an item whose component patch contains host text and object-level NBT numbers. -/
@[mcfunction]
public def prize (round : Val Int32) : Prog
    ⟨Req.executor, Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite |||
      Eff.random ||| Eff.hud ||| Eff.sound ||| Eff.failure⟩ Int32 := do
  Give.to .self {id := "minecraft:apple", components := [
    .ofNbt "minecraft:custom_name" ("Round prize" : String),
    .set "minecraft:custom_data" (.nbtCompound [(⟨"round"⟩, .hole .i32 round)])]} (.static 1)

/-- Copy the executor's two hand slots into a block inventory, repeating the source sequence. -/
@[mcfunction]
public def stockChest := Item.transfer
  ⟨.block (.world (.relative (.static 0)) (.relative (.static 0)) (.relative (.static 0))),
    .range "container.*"⟩
  (.from ⟨.entity .self, .range "weapon.*"⟩ none) .fill

/-- Replace matching planks in an inclusive region without neighbor updates. -/
@[mcfunction]
public def resetFloor := Fill.run {
  start := .world (.relative (.static (-4))) (.relative (.static (-1))) (.relative (.static (-4)))
  finish := .world (.relative (.static 4)) (.relative (.static (-1))) (.relative (.static 4)) }
  {id := "minecraft:stone"} (.replace (some {id := .tag "minecraft:planks"}) .strict)

/-- Reset online players' scores and enable one trigger input each. Both objectives must exist. -/
@[mcfunction]
public def preparePlayers : Prog (Scoreboard.Group.grade Req.none) Int32 := do
  Scoreboard.Group.set {holders := .entities (.selector .allPlayers), objective := "game.score"} (.static 0)
  Scoreboard.Group.enable {holders := .entities (.selector .allPlayers), objective := "game.input"}

/-- Transfer the executor to a host, computing only the port at runtime. Requires native
administrator permissions and a destination that accepts transfers. -/
@[mcfunction]
public def handoff (port : Val Int32) : Prog (Admin.Transfer.grade .self) Int32 :=
  Admin.Transfer.to {host := "play.example.invalid", port := .dynamic port}

/-- Change the simulation rate through a runtime integer. Requires administrator permission. -/
@[mcfunction]
public def tickRate (rate : Val Int32) : Prog Admin.Tick.grade Int32 :=
  Admin.Tick.run (.rate (.dynamic rate))

/-- Add a named account to the whitelist, including an offline account known to the server. -/
@[mcfunction]
public def allowAccount : Prog (Admin.Whitelist.grade Req.none) Int32 :=
  Admin.Whitelist.add (.named "Alex")

end Oria.Examples.StandardLibrary
