# Gameplay control and presentation

The standard library targets Minecraft Java 26.3 / DP121. The interfaces below cover gameplay
control and scoreboard presentation.
Operation arguments select the native variants. See the
[Lean-checked examples](../Oria/Examples/StandardLibrary.lean) for complete object functions.

## Interfaces

| Module | Operations | Shared arguments |
| --- | --- | --- |
| Gamerule | query and typed assignment | GameRule, Scalar |
| Attribute | computed/base/modifier query; base set/reset; modifier add/remove | AttributeAction, AttributeOperation |
| Forceload | add/remove rectangle, query, list, clear | ForceloadAction, ColumnPos |
| Spawnpoint | player respawn position and rotation | Players, SpawnLocation |
| SetWorldSpawn | world respawn position and rotation | SpawnLocation |
| Spectate | start and stop a spectator camera | Target, Players |
| Ride | mount and dismount | Target |
| Rotate | angles, facing a point, facing an entity | RotationAction, Rotation, Anchor |
| SpreadPlayers | random safe-ground placement and team grouping | Vec2, SpreadSettings |
| Particle | parameterized particles and viewer settings | ParticleSpec, ParticleSettings, Compound |
| Swing | hand, animation, duration | SwingSettings, Hand, Time |
| PostEffect | add/remove/clear/list client post effects | Players, ResourceId |
| Scoreboard | objective slots/properties and per-score display names/formats | DisplaySlot, ObjectiveProperty, ScoreFormat, Holders |

These are standard-library descriptions over the existing Fragment and ArgCodec interfaces.
Angles and anchors live in `Std.Command.Arg.Position`; Execute uses the same types. Numeric
leaves use Scalar or Decimal, so static text and runtime I32 holes can coexist in one command.
The receiving native parser checks ranges, resources, and selection cardinality.

## Typed game rules

`GameRule a` fixes the assignment type. The 59 descriptors are taken from the pinned
server's registry: Boolean rules accept host Bool, and integer rules accept Scalar.
Examples include `keepInventory : GameRule Bool` and `randomTickSpeed : GameRule Scalar`.

```lean
example := Gamerule.set .keepInventory true
example := Gamerule.set .immediateRespawn true
example (n : Val Int32) := Gamerule.set .randomTickSpeed (.dynamic n)
example := Gamerule.get .keepInventory
```

Gamerule reads the execution dimension's rules. Query and assignment return the native value,
with false represented by successful zero. Assignment to the current value fails. Rule-specific
integer bounds and feature availability remain native checks; an experimental rule may require
its feature flag. Keep command execution limits sufficient for the generated program.

Rule constructors are private. The assignment interface relates the value type to its rule.
The interface theorem states that assigning a rule retains precisely the value codec's context
requirements. Thus the checker can normalize a concrete assignment without inspecting its
representation. To choose a Boolean at runtime, branch in Prog and assign a host Bool in each arm.

## Positions, rotation, and camera control

`BlockPos.world` takes integer absolute or relative block coordinates. `BlockPos.local`
takes decimal local offsets, which Minecraft resolves and floors. `ColumnPos` supplies X/Z
block coordinates for forceload. `Rotation` is ordered yaw then pitch; relative angles read
the command source's rotation. `SpawnLocation.here` uses the execution position and zero
rotation. `.atPos p none` also selects zero rotation.

```lean
example := Spawnpoint.set .all
  (.atPos (.world (.absolute (.static 0)) (.absolute (.static 64)) (.absolute (.static 0)))
    (some ⟨.absolute (.static 90), .absolute (.static 0)⟩))
example := Rotate.run .self
  (.angles ⟨.relative (.static 15), .absolute (.static 0)⟩)
example := Rotate.run .self (.entity (.selector .nearestEntity) .eyes)
```

Player respawn settings retain the source dimension; native yaw wrapping and pitch clamping
apply. World respawn settings use native world storage. Setting either does not teleport a
player immediately.

Rotate's facing forms use the execution anchor on the rotated entity. The destination
entity's anchor is a separate argument. Spectate requires one spectator player and a distinct
camera target; `Spectate.stop` resets the executing player's camera. Ride requires singular
targets and preserves native restrictions on cycles, vehicles, and dimensions.

SpreadPlayers searches for safe ground in the source dimension. Its numeric settings can
be dynamic. Team grouping changes the result from an entity count to a count of placement
groups. The operation may fail when the requested separation and terrain cannot be satisfied.

Forceload records chunk-loading tickets. Success does not establish that the chunks have
finished loading. Coordinates are block coordinates, and ranges select the containing
inclusive chunk rectangle. Callers must arrange ready terrain before operations that require it.

## Attributes

```lean
example := Attribute.run .self "minecraft:max_health" (.set (.decimal 24.5))
example := Attribute.run .self "minecraft:max_health"
  (.add "arena:bonus" (.static 4) .add)
example := Attribute.run .self "minecraft:max_health" (.get (.static 10))
```

The target must be one living entity with the selected attribute. Modifier IDs name native
entity state, independent of the Oria invocation arena. Reset changes the base value; modifier
removal is explicit.

Native calculation first applies flat additions. The multiply-base operation uses that
post-addition value; multiply-total operations then scale the running total. The attribute's
bounds apply afterward. Queries multiply by the supplied scale and use Java's Double-to-int
conversion, which truncates toward zero and saturates at I32 bounds. For example, 27.75 scaled
by -10 returns -277. Static fractions and dynamic I32 amounts reuse Decimal.

## Particles and animations

`ParticleSpec` combines a registry ID with Compound options. It accepts host NBT, fields with
typed dynamic holes, or a runtime compound snapshot. Particle options follow the ID directly,
for example `minecraft:dust{color:[1d,0d,0d],scale:1d}`.

```lean
example := Particle.send {
  id := "minecraft:dust"
  options := .value (nbt% {color: [1.0, 0.0, 0.0], scale: 1.0}) }
example := Swing.run .self
  {hand := .offhand, animation := .stab, duration := .seconds (.decimal 0.5)}
example := PostEffect.add .all "arena:highlight"
```

Particle settings include origin, delta, speed, count, normal/force delivery, and viewers.
The origin uses ordinary coordinate centering; delta uses the native non-centered vector parser.
Count zero requests the native directional behavior. Successful results count recipient
packets, not particles. Client configuration determines the rendered output.

Swing supports none, whack, and stab, with a positive duration in native time units. It counts
living targets, even when their current animation state suppresses a restart. PostEffect manages
client effect IDs and marks them for a subsequent player-update packet. The server cannot
check that a referenced resource-pack
shader exists or is rendered. Add, remove, and clear fail when no selected player's state changes.

## Scoreboard display and team selection

```lean
example := Scoreboard.Objectives.setDisplay .sidebar (some "arena.round")
example := Scoreboard.Objectives.modify "arena.round" (.displayName (.literal "Round"))
example := Scoreboard.Objectives.modify "arena.round" (.numberFormat .blank)
example := Scoreboard.numberFormat (.one (.named "#round")) "arena.round"
  (.fixed (.literal "Final"))
```

Display slots cover list, sidebar, belowName (native below_name), and team-colored sidebars. Omitting the objective
clears the slot. Objective properties cover name, integer/heart rendering, automatic score-name
updates, and number format. Number formats can be reset, blank, fixed text, or styled NBT.
Style decoding adds no implicit context beyond the supplied NBT fragment. Fixed text retains
the TextComponent requirement, including any native selector or NBT resolution.
Per-score formats override the objective format; resetting an override restores inheritance.
`Scoreboard.setName` similarly sets or resets per-score display names. These native setters
can create missing score entries.

The shared selector accepts one positive or negative team filter:

```lean
def red : Players := .selector (.allPlayers {team := some (.include "arena.red")})
def unassigned : Players := .selector (.allPlayers {team := some (.include "")})
def assigned : Players := .selector (.allPlayers {team := some (.exclude "")})
```

The empty team name selects entities without a team; its negation selects entities with one.
Team filters add no implicit context requirement. Names use the existing unquoted-word
validation, rejecting embedded selector punctuation.

## Results and verification

The success bit is independent of the result integer and of native feedback messages.
Forceload list can print failure feedback for an empty set while returning normally with
success and result 0. Clearing forced chunks and updating several scoreboard properties
also return successful zero. Missing forced-chunk queries, invalid dynamic bounds, and
unavailable native targets follow command failure.

`Oria.Proofs.StdControl` proves context contracts and checks selector encoding.
The batch fixture combines compiled entries across world, player, management, control,
movement, display, item, block, and execution groups. Its golden records command text and macro writes, normalizing
terminal whitespace as the native function loader does. The artifact's elaboration budget is
set locally for this large fixture.

`scripts/rps-test` checks native rules, attribute arithmetic, forced chunks, respawn data,
riding/cameras, placement, particle and post-effect packets, scoreboard state, and team filters.
It also runs the existing command and rock-paper-scissors acceptance, including reload.
The post-effect check inspects immediate server state and flushes the native packet sender
used by the later player update.
Rendered particles, shaders, and client animation appearance remain client behavior.

The semantic reference is the server pinned by
[`minecraft-26.3.lock.json`](../minecraft-26.3.lock.json), together with the
[official 26.3 command changes](https://www.minecraft.net/en-us/article/minecraft-java-edition-26-3).
