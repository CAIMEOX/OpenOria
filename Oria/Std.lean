module

public import Oria.Std.Command
public import Oria.Std.Nbt

/-!
# Oria standard library

Oria composes Minecraft commands into typed object programs. Lean constructs the code;
Minecraft executes it when a datapack function runs. The target is Minecraft
26.3 / DP121.

## Getting started

| Task | Interface |
| --- | --- |
| Teleport an entity | [Teleport](##Oria.Std.Teleport) |
| Spawn entities with optional NBT | [Summon](##Oria.Std.Summon) |
| Kill selected entities | [Kill](##Oria.Std.Kill) |
| Give and remove status effects | [Effect](##Oria.Std.Effect) |
| Group entities with tags | [Tag](##Oria.Std.Tag) |
| Show titles and action bars | [Title](##Oria.Std.Title) |
| Play and stop sounds | [Sound](##Oria.Std.Sound) |
| Set weather and world clocks | [Weather](##Oria.Std.Weather), [Time](##Oria.Std.Time) |
| Set difficulty and world borders | [Difficulty](##Oria.Std.Difficulty), [WorldBorder](##Oria.Std.WorldBorder) |
| Set player and default game modes | [GameMode](##Oria.Std.GameMode) |
| Add, assign, and query experience | [Experience](##Oria.Std.Experience) |
| Unlock and remove recipes | [Recipe](##Oria.Std.Recipe) |
| Enchant held items | [Enchant](##Oria.Std.Enchant) |
| Apply attributed damage | [Damage](##Oria.Std.Damage) |
| Grant and revoke advancement progress | [Advancement](##Oria.Std.Advancement) |
| Manage boss bars and viewers | [Bossbar](##Oria.Std.Bossbar) |
| Manage teams and membership | [Team](##Oria.Std.Team) |
| Query and assign typed game rules | [Gamerule](##Oria.Std.Gamerule) |
| Query and modify entity attributes | [Attribute](##Oria.Std.Attribute) |
| Manage forced chunks | [Forceload](##Oria.Std.Forceload) |
| Set player and world respawn positions | [Spawnpoint](##Oria.Std.Spawnpoint), [SetWorldSpawn](##Oria.Std.SetWorldSpawn) |
| Control spectator cameras | [Spectate](##Oria.Std.Spectate) |
| Mount and dismount entities | [Ride](##Oria.Std.Ride) |
| Rotate and distribute entities | [Rotate](##Oria.Std.Rotate), [SpreadPlayers](##Oria.Std.SpreadPlayers) |
| Send particles and hand animations | [Particle](##Oria.Std.Particle), [Swing](##Oria.Std.Swing) |
| Manage client post-processing effects | [PostEffect](##Oria.Std.PostEffect) |
| Construct and match inventory items | [Give](##Oria.Std.Give), [Clear](##Oria.Std.Clear) |
| Transfer and modify selected slots | [Item](##Oria.Std.Item) |
| Generate and distribute loot | [Loot](##Oria.Std.Loot) |
| Place, fill, and clone blocks | [Setblock](##Oria.Std.Setblock), [Fill](##Oria.Std.Fill), [Clone](##Oria.Std.Clone) |
| Replace biome cells | [FillBiome](##Oria.Std.FillBiome) |
| Generate features, pools, structures, and templates | [Place](##Oria.Std.Place) |
| Style locator-bar transmitters | [Waypoint](##Oria.Std.Waypoint) |
| Measure server-running real time | [Stopwatch](##Oria.Std.Stopwatch) |
| Locate structures, biomes, and POIs | [Locate](##Oria.Std.Locate) |
| Broadcast, whisper, and send team chat | [Chat](##Oria.Std.Chat) |
| Query online count, seed feedback, and version | [ServerInfo](##Oria.Std.ServerInfo) |
| Inspect installed datapacks | [PackControl](##Oria.Std.PackControl) |
| Control simulation rate and stepping | [Admin.Tick](##Oria.Std.Admin.Tick) |
| Disconnect and transfer players | [Admin.Kick](##Oria.Std.Admin.Kick), [Admin.Transfer](##Oria.Std.Admin.Transfer) |
| Manage admission and permissions | [Admin.Whitelist](##Oria.Std.Admin.Whitelist), [Admin.Ban](##Oria.Std.Admin.Ban), [Admin.Operator](##Oria.Std.Admin.Operator) |
| Set player idle timeout | [Admin.IdleTimeout](##Oria.Std.Admin.IdleTimeout) |
| Read, write, and compute scores | [Scoreboard](##Oria.Std.Scoreboard) |
| Submit enabled player input | [Trigger](##Oria.Std.Trigger) |
| Sample and manage random sequences | [Random](##Oria.Std.Random) |
| Send text components | [Tellraw](##Oria.Std.Tellraw) |
| Modify NBT and read snapshots | [Data](##Oria.Std.Data) |
| Evaluate number providers | [Compute](##Oria.Std.Compute) |
| Send dialogs | [Dialog](##Oria.Std.Dialog) |
| Change execution context and iterate over entities | [Execute](##Oria.Std.Execute) |

Shared argument types live in [Command.Arg](##Oria.Std.Command.Arg).
Integer and decimal inputs share the
[numeric argument interfaces](##Oria.Std.Command.Arg.Numeric).
Compound NBT parameters live in [Command.Arg.Nbt](##Oria.Std.Command.Arg.Nbt).
Title locations, sound categories, and playback settings live in
[Command.Arg.Presentation](##Oria.Std.Command.Arg.Presentation).
World operations, player actions, and management properties live in
[Command.Arg.World](##Oria.Std.Command.Arg.World),
[Command.Arg.Gameplay](##Oria.Std.Command.Arg.Gameplay), and
[Command.Arg.Management](##Oria.Std.Command.Arg.Management).
Block positions, angles, and anchors live in
[Command.Arg.Position](##Oria.Std.Command.Arg.Position); entity-control and particle arguments
live in [Command.Arg.Control](##Oria.Std.Command.Arg.Control). Typed rule descriptors and
scoreboard presentation types live in [Command.Arg.Gamerule](##Oria.Std.Command.Arg.Gamerule)
and [Command.Arg.Display](##Oria.Std.Command.Arg.Display).
Item descriptions, predicates, and inventories live in [Command.Arg.Item](##Oria.Std.Command.Arg.Item).
Blocks share [Command.Arg.Block](##Oria.Std.Command.Arg.Block), and loot sources/destinations use
[Command.Arg.Loot](##Oria.Std.Command.Arg.Loot). The
[registry descriptions](##Oria.Std.Command.Arg.Registry) preserve resource-specific types and context summaries.
See the [standard library examples](##Oria.Examples.StandardLibrary) for complete programs.
Account selection, addresses, transfer destinations, and tick operations share
[Command.Arg.Server](##Oria.Std.Command.Arg.Server). Administrative commands require native
administrator permissions, including permission to compile their containing functions.
[Rock-paper-scissors](##Oria.Examples.RockPaperScissors) combines player input, random draws,
per-player scoring, and chat feedback in a playable datapack.

## Command results

Ordinary commands return `Prog g Int32`; their grades include the recoverable failure
effect. Reading a score returns the score; sending a message returns the recipient count.
A successful result of 0 is still a normal completion.

In `do`, `let n ← action` binds the normal result, and failure skips the continuation.
A bare statement discards its normal value while propagating failure.
`try ... catch _ => ...` recovers in a lexical scope.

| Operation | Behavior |
| --- | --- |
| `action.map f` | Transform the normal value. |
| `action.getD value` | Recover with an object expression. |
| `action.orElse fallback` | Run a fallback computation on failure. |
| `action.isSuccess` | Observe completion as a Boolean. |
| `action.ignore` | Suppress failure and discard the normal value. |
| `Prog.attempt action` | Capture completion as ordinary Option data. |

Recovery removes the body's failure effect and retains the fallback's effects. Earlier
world changes remain observable. Named calls retain failure control flow inside the callee.
`Data.readOne` and `readAll` return NBT snapshots through the same computation interface.

`let action := ...` binds code at the host stage; `let value ← action` binds a runtime result.
Ordinary Lean calls expand code generators; `.call` emits a named object-level call.

## Context and effects

In a Grade, req describes the implicit inputs required to execute the code; eff is a static
upper bound on observable effects. `.self` requires an executor. Relative coordinates read
the position; local coordinates also read rotation and anchor.
`Execute.forEach [.as .allPlayers] body` supplies an executor to the body while retaining
the caller's position. Add `.at .self` to use each player's position. Step order matters.

Literal text, integer messages, and literal dialog notices require only their targets' context,
so broadcasting them to all players is valid in load and tick callbacks. Raw command text, full text components,
and providers can read several parts of the environment.
Their interfaces use conservative bounds. Each module's grade function states the contract;
these bit sets are checked statically.

Titles use the hud effect and sound commands use sound. These distinguish their client-facing
effects from chat. Sound playback reads its source dimension and coordinate context. An as
step alone retains the caller's position; use as/at together for per-player sound origins.

Weather with an explicit duration and named-clock operations need no implicit context.
Default-clock selection and world-border operations read the dimension. Boss-bar and team
properties derive requirements from their text and target arguments. Advancement grants can
execute external reward functions and retain all current effect labels. Such callbacks must
respect invocation boundaries: a reward must not re-enter the active pack's public entries
before the current invocation returns.

## Static arguments and dynamic values

Integer literals and host `Int32` values enter `Scalar` directly and emit integer text.
Runtime `Val Int32` expressions introduce function macro arguments. `Decimal` additionally
accepts decimal/scientific literals and host `Float` or `Float32` values. Negative inputs
preserve their numeric form. Integer coordinates such as `1` use native X/Z centering;
`1.0` retains an exact coordinate. `Vec3.absolute x y z` and `Vec3.relative x y z` construct
uniform world coordinates; `Vec3.world` marks mixed axes individually. `BlockPos` provides
the same absolute/relative constructors for integer block coordinates.

Coordinates and NBT descriptions can mix static and dynamic components.
Ordinary String and `Nbt.Value` are host data; `Val Int32` and `Val (Nbt.Data t)` are runtime
object values.

Native NBT copies preserve tags and values. `Nbt.native` explicitly uses Minecraft's macro
serialization: strings become raw text, numbers use the native format, and compounds,
lists, and arrays produce SNBT. Account for floating-point precision and string quoting
according to the receiving argument's grammar.

## Parsing and failure

Lean checks argument types, scopes, and effect contracts. Minecraft parses static commands
when loading functions and dynamic commands when invoking macros. A valid command can still
fail during execution: a target may be absent, a score uninitialized, a path unmatched, or
an NBT update unchanged. Each function documents its conditions.

Lean code blocks in declaration docstrings are checked during compilation. GameTest checks
game behavior against the target version. Command library authors can also consult
[Declarations](##Oria.Std.Command.Declarations) and [Manifest](##Oria.Std.Manifest).
-/
