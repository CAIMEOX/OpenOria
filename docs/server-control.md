# Server control and bulk scores

The standard library targets Minecraft Java 26.3 / DP121. Public interfaces are available
through `import Oria`.

| Module | Operations |
| --- | --- |
| `Scoreboard` | List tracked holders or one holder's scores. |
| `Scoreboard.Objectives` | List objectives. |
| `Scoreboard.Group` | Set, reset, reset all, enable triggers, and apply binary operations. |
| `PackControl` | List enabled packs, compatible available packs, or both. |
| `Admin.Tick` | Query/rate, freeze/unfreeze, step/stop, sprint/stop. |
| `Admin.Kick` | Disconnect selected players, optionally with a native message reason. |
| `Admin.Transfer` | Request a transfer to a host and port. |
| `Admin.Whitelist` | Enable/disable, list, reload, add, and remove profiles. |
| `Admin.Ban` | Profile and IP bans, lists, and corresponding pardons. |
| `Admin.Operator` | Grant or revoke operator status. |
| `Admin.IdleTimeout` | Set the server's player idle timeout. |

All operations return `Prog g Int32`. A successful zero result remains distinguishable from
failure. `.ignore` executes the command without retaining either result component.

## Bulk scores

`Scores` pairs a `Holders` selection with an objective. It is shared by the two operands of
`Scoreboard.Group.operation` and by the other group operations. `Holders.one`, `entities`, and
`all` represent a single holder, an entity selection, and the native tracked-holder wildcard.
The existing single-score functions retain their narrower context and effect contracts.

The following program is checked in `Oria.Examples.StandardLibrary`:

```lean
@[mcfunction]
def preparePlayers : Prog (Scoreboard.Group.grade Req.none) Int32 := do
  Scoreboard.Group.set
    {holders := .entities (.selector .allPlayers), objective := "game.score"} (.static 0)
  Scoreboard.Group.enable
    {holders := .entities (.selector .allPlayers), objective := "game.input"}
```

The objectives must exist; `game.input` must use the trigger criterion. The do block stops
on command failure. Successful execution returns the number of newly enabled scores.

| Operation | Success payload |
| --- | --- |
| `Objectives.list` | Objective count. |
| `list none` | Tracked-holder count. |
| `list (some holder)` | Number of that holder's score entries. |
| `Group.set` | I32 sum of written scores, including overflow. |
| `Group.reset`, `resetAll` | Selected-holder count, including absent score entries. |
| `Group.enable` | Newly unlocked trigger-score count; zero changes fails. |
| `Group.operation` | I32 sum of final target scores. |

Binary operations visit each target and apply every source in native iteration order. Swap
also changes source scores. Selection order is relevant for noncommutative operations and
overlapping operands. Division by zero can fail after earlier writes, and native creation of
missing zero-valued entries can survive failure. `Prog.fail` provides control flow, not rollback.

`Group.resetAll .all` can include compiler-owned fake holders. Applications should select their
players or explicitly named scores when modifying score state during an Oria invocation.

## Administrative arguments and context

`Std.Command.Arg.Server` supplies `Profiles`, `IpTarget`, `Destination`, and `TickAction`.
`Profiles.named` uses native account lookup, which can resolve an offline account according to
server configuration. `Profiles.players` reuses the online-player argument. Named profiles need
no implicit context; `.players .self` needs an executor, and structured selectors retain their
requirements.

`IpTarget.address` and `Ban.pardonIp` use Lean's `Std.Net.IPv4Addr`. The native IP command grammar
is an unquoted word, so this interface exposes dotted IPv4 addresses. `IpTarget.player` asks
Minecraft for an online named player's current address. The address parser and formatter come
from Lean's standard library.

`Destination` contains a host string and a `Scalar` port, defaulting to 25565. The host uses the
existing Brigadier quoted-string serializer. A dynamic port becomes one I32 macro hole; its native
range is 1 through 65535. Each command argument keeps its own static or dynamic representation.

```lean
@[mcfunction]
def handoff (port : Val Int32) : Prog (Admin.Transfer.grade .self) Int32 :=
  Admin.Transfer.to {host := "play.example.invalid", port := .dynamic port}
```

Its command contains `transfer "play.example.invalid" $(p0) @s`. The result counts recipients
of the transfer request. Connecting to the destination happens afterward, under the destination's
transfer-admission policy. The native command exists in the dedicated-server command set; see
the [1.20.5 release notes](https://www.minecraft.net/en-us/article/minecraft-java-edition-1-20-5).

Kick and ban reasons use `Message`, including its plain text, selector expansion, and integer
fragments. Omitting a reason selects the native default. Arbitrary NBT text components belong
to commands with a text-component parser; these reason arguments use Minecraft's message parser.

Effects retain conservative world, selection, and message bounds. Permission levels are deployment
requirements; coeffects continue to track executor, position, dimension, rotation, and anchor.

## Native results and state changes

| Operation | Result and failure behavior |
| --- | --- |
| `PackControl.list` | Count of the chosen packs; an empty list succeeds with zero. Available excludes enabled packs and incompatible feature requirements. |
| `Tick.run .query`, `.rate` | Target rate truncated to I32. Rate accepts 1 through 10000, including host fractions. |
| `Tick.run .freeze`, `.unfreeze` | Successful 1 and 0 respectively. Freeze stops active stepping and sprinting. |
| `Tick.run (.step time)` | 1; requires frozen simulation and a duration rounding to at least one tick. |
| `Tick.run (.sprint time)` | 1; requires a positive rounded duration. |
| `Tick.run .stopStep`, `.stopSprint` | 1; an inactive request fails. |
| `Kick.run` | Disconnected-player count; an unpublished server or no eligible players fails. The singleplayer owner is skipped. |
| `Transfer.to` | Selected-recipient count; unresolved targets or invalid ports fail. |
| `Whitelist.set` | 1; an unchanged setting fails. |
| `Whitelist.add`, `.remove` | Changed-profile count; zero changes fails. |
| `Whitelist.list`, `Ban.list` | Entry count, including successful zero. Names are source feedback. |
| `Whitelist.reload` | 1 after reloading and enforcing admission. |
| `Ban.players`, `.pardon` | Changed-profile count; zero changes fails. |
| `Ban.ip` | Disconnected-player count; zero succeeds when a new ban affects no online players. An existing ban fails. |
| `Ban.pardonIp` | 1; an absent ban fails. |
| `Operator.grant`, `.revoke` | Changed-profile count; zero changes fails. |
| `IdleTimeout.set` | Nonnegative minutes; zero disables the timeout. |

Enabling or reloading a whitelist, removing whitelist entries, and revoking operator status may
disconnect players under native admission rules. Native listing and query feedback is suppressed
inside functions. The integer result is available to the program; textual reports are not returned
as an object-level collection.

Tick commands change the simulation scheduler. They do not suspend the current invocation.
Freeze can prevent subsequent ordinary tick callbacks from running, so a thaw operation must
remain reachable through a suitable external invocation. See the
[1.20.3 tick-command specification](https://www.minecraft.net/en-us/article/minecraft-java-edition-1-20-3).

## Deployment and verification

Scoreboard and datapack inspection use native gamemaster permission (level 2). Administrative
commands require administrator permission (level 3). Minecraft parses static function lines
using the configured function-compilation permissions. Insufficient permissions can prevent a
function from loading; this is distinct from execution-time `Prog.fail`. Server configuration
remains under the operator's control.

`Oria.Proofs.StdServer` proves argument requirement preservation and checks representative native
rendering. `Fixtures.Server` exercises generated programs, including a six-register budget and
dynamic arguments. `tests/golden/server.dp121` fixes their command text.

Run `scripts/rps-test --admin` for an isolated native GameTest world. Minecraft's GameTestServer
selects dedicated commands and owner-level function-compilation permissions. The suite also checks
that the native compiler rejects `tick query` under gamemaster permissions and accepts it under
administrator permissions.

The suite checks tick-manager state, group scores, overflow, persistent native writes on failure,
transfer packets, whitelist state, bans/pardons, operator status, and idle timeout. It restores
administrative state before shutdown. Transfer tests inspect requests without connecting to a
destination server. GameTestServer is unpublished, so Kick is checked against its publication
guard; successful disconnection on a published server needs separate acceptance coverage.

The shared command pipeline remains responsible for command-component demand pruning, numeric macro holes,
register allocation, and stack handling. These interfaces add standard-library declarations and
codecs; the compiler IRs and calling convention are unchanged.
