# World, player, and management commands

These interfaces target the pinned Minecraft Java 26.3 / DP121 server. They use the existing
command-fragment codecs, `Prog g Int32`, and ordinary do notation. The
[checked examples](../Oria/Examples/StandardLibrary.lean) include arena preparation and
player admission.

## Interface coverage

| Module | Operations | Shared arguments |
| --- | --- | --- |
| `Weather` | clear, rain, thunder; sampled or explicit duration | `WeatherKind`, `Time` |
| `Time` | set, add, marker, pause, resume, rate, clock/timeline queries, game time | `ClockAction`, `Time`, `ResourceId` |
| `Difficulty` | query and set | `DifficultyLevel` |
| `WorldBorder` | query, center, set/add size, transition, damage, buffer, warnings | `BorderAction`, `Vec2`, `Decimal`, `Time` |
| `GameMode` | selected players and server default | `GameMode`, `Players` |
| `Experience` | add, set, query points or levels | `ExperienceUnit`, `Scalar` |
| `Recipe` | give or take one recipe or all recipes | `ResourceSet`, `Players` |
| `Enchant` | enchant selected entities' held items | `Target`, `ResourceId`, `Scalar` |
| `Damage` | generic, typed, positional, attacker/source attribution | `DamageCause`, `Target`, `Vec3`, `Decimal` |
| `Advancement` | grant/revoke everything, one advancement/criterion, graph scopes | `AdvancementScope`, `Players` |
| `Bossbar` | add, remove, list, query, update every native property | `BarField`, `BarProperty` |
| `Team` | add, remove, empty, list, join, leave, update every native property | `Holders`, `TeamProperty` |

Typed operation arguments expand to the native subcommands described by each interface.

`Arg.World`, `Arg.Gameplay`, and `Arg.Management` own the argument descriptions and codecs.
They reuse the existing target, resource, text, numeric, and coordinate types. The three
matching declaration modules contain checked templates. Each command module imports its
declaration group and uses the existing Prog elaborator to check its grade.

## Static structure and runtime parameters

Operation choices, resource names, property names, and units are Lean host values. Numeric
leaves can contain runtime I32 expressions. Each dynamic leaf becomes one macro hole; the
rest of the command remains static.

```lean
open Oria Oria.Std Oria.Std.Command.Arg

example (n : Val Int32) := Bossbar.set "arena:round" (.value (.dynamic n))
example (n : Val Int32) := Experience.add .self (.dynamic n) .levels
example := WorldBorder.run (.center
  ⟨.absolute (.decimal 10.5), .absolute (.decimal 20.5)⟩)
example := Team.modify "arena.red" (.prefix (.literal "[Red] "))
```

The first example produces a macro command with the shape
`bossbar set arena:round value $(p0)`. `Decimal` also supports host fractions; the receiving
native parser determines Float32 or Double interpretation and bounds. `Time` supports ticks,
seconds, and days with native Float32 scaling and rounding. Dynamic floating-point computation
is not introduced by these interfaces.

Minecraft checks resource existence, numeric ranges, target cardinality, and current state.
An invalid static command may prevent its function from loading. An invalid dynamic argument
fails when the macro is invoked. A well-parsed command can still fail because its target is
missing or its update is unchanged. Partial native updates are not rolled back on failure.

## World clocks and weather

```lean
example := Time.run .pause (some "minecraft:overworld")
example := Time.run (.set (.ticks (.static 6000))) (some "minecraft:overworld")
example := Time.run (.timeline "minecraft:day" false) (some "minecraft:overworld")
example := Time.run (.rate (.decimal 0.5)) (some "minecraft:overworld")
example := Time.run .resume (some "minecraft:overworld")
example := Weather.set .clear (some (.seconds (.static 60)))
```

A named clock emits `time of <clock> ...`; omitting the clock uses the source dimension's
default clock. `.query` emits `query time`. `.timeline id false` queries ticks within a
timeline; `true` queries its repetition count. `.marker id` sets a registered time marker.
`Time.gameTime` reads game time independently of clock rate and pause state. These operations
modify native clocks while the current Oria invocation continues synchronously.

Named-clock operations need no implicit context. Default-clock selection and game-time queries
read the dimension. World-border operations also read the dimension, plus position when
relative coordinates are present. Weather with an explicit duration reads no context;
omitting the duration consumes the source dimension's random generator.

Setting total ticks returns the supplied tick count. Add and total-clock queries return the
native remainder modulo 2147483647. Pause, resume, and rate return 1; requests that leave
their state unchanged can fail.
Explicit weather duration returns its rounded tick count; sampled duration returns a
successful -1. World-border transition and warning durations use the native time parser.

## Player state and command results

Game-mode selection, experience, recipes, and advancements accept `Players`; damage and
enchantment accept entity targets. `Experience.query` and `Damage.apply` require a single
native target. `.self` requires an executor; `.all` is available in server callbacks.
Spatial selector filters add their own requirements.

The success bit is independent of the result integer. These cases are checked on the server:

| Operation | Successful result | State-sensitive behavior |
| --- | --- | --- |
| `Difficulty.set` | 0 | unchanged difficulty fails |
| `GameMode.set` | changed player count | already-selected mode succeeds with 0 |
| `Experience.query` | points within the level, or level count | target must be one player |
| `Recipe.give` / `take` | recipe modifications summed across players | no change fails |
| `Enchant.apply` | changed entity count | held item, compatibility, and level are checked |
| `Damage.apply` | 1 | immunity and damage handling can reject a hit |
| `Team.join` | selected holder count | rejoining the same team succeeds |
| `Team.leave` | changed holder count | a named holder without a team succeeds with 0 |
| `Bossbar.get .visible` | 0 or 1 | unknown bar fails |

Use `.ignore` for setup operations that may already be satisfied. In a fallible do block,
failure exits the function while successful zero or negative results continue normally.
Experience addition is signed. Experience assignment must be nonnegative; point assignment
is constrained by each player's current level capacity.

## Boss bars and teams

Boss-bar properties cover name, color, style, value, maximum, visibility, and viewers.
`Bossbar.set id (.players none)` clears viewers. Names reuse `TextComponent`, including
literal text, dynamic integer text, and complete NBT descriptions. Literal text adds no
context requirement; arbitrary NBT components retain the existing conservative requirement.

Boss-bar add/list/remove return total or remaining bar counts. Setting value/max returns the
assigned number; setting name/color/style/visibility returns successful zero. Replacing
viewers returns their new count. Repeating an unchanged setter generally fails.

Teams accept `Command.Word` names. `Holders` selects one name or executor, an entity selector,
or the tracked-score-holder wildcard. Team properties cover display name, prefix, suffix,
the 16 native named colors, friendly fire, invisible teammates, visibility, and collision.
`.color none` resets the team color. Most property updates return zero and fail when
unchanged; prefix and suffix retain native successful result 1 even on repetition.

## Advancement rewards and invocation boundaries

An advancement scope selects everything, one advancement or criterion, or the ancestors and
descendants of a named advancement. A criterion is native greedy text. Revoke changes progress
and leaves previously issued rewards in place.

Grant may execute an external reward function under the rewarded player's command source.
Its grade therefore includes all currently defined observable effects. Those effects are
an upper bound; the command catalog does not inspect external reward bodies.

Public Oria entries initialize the pack's invocation arena. A reward function must not call
the active pack's public entries before the current invocation returns. Use a native reward
function that respects compiler-owned storage and scores, or arrange a subsequent entry call
after the active invocation. Reentrant public-entry support requires a separate runtime
protocol. The native acceptance reward updates an application scoreboard directly.

## Verification and sources

`Oria.Proofs.StdBatch` checks context summaries and catalog composition.
`Oria.Proofs.Fixtures.Batch` compiles 311 public acceptance entries, including dynamic
weather, clock, border, experience, enchantment, damage, and boss-bar inputs.
`tests/golden/batch.dp121` fixes their emitted commands and macro argument writes.

`scripts/rps-test` executes the world, player, and management groups through compiled entries,
checks native state and return values, then runs the other command and rock-paper-scissors
checks, including reload. The border, difficulty, and default game mode are restored before
the player tests; clocks resume at normal rate and weather returns to clear. Damage forms
use independent entities to isolate native hit cooldown. Grant-everything and the tracked
holder wildcard have compile/load coverage; the runtime checks use controlled advancement
graphs and explicit holder selections. Client rendering remains outside these assertions.

The semantic reference is the server identified by
[`minecraft-26.3.lock.json`](../minecraft-26.3.lock.json): `WeatherCommand`, `TimeCommand`,
`WorldBorderCommand`, `DifficultyCommand`, `GameModeCommand`, `DefaultGameModeCommands`,
`ExperienceCommand`, `RecipeCommand`, `EnchantCommand`, `DamageCommand`,
`AdvancementCommands`, `BossBarCommands`, `TeamCommand`, and their native argument parsers.
The harness and resource fixtures are in [`integration/rps`](../integration/rps).
