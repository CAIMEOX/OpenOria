# Standard library commands

Import `Oria` and `meta import Oria`, then open the namespaces needed by the source module.
Command functions construct object computations. Their declaration docstrings specify
parameters, native success/result behavior, effects, context requirements, and argument stages.

The generated reference guide is [Oria.Std](../Oria/Std.lean); composed, Lean-checked programs
are in [StandardLibrary](../Oria/Examples/StandardLibrary.lean).
See [documentation builds](../docbuild/README.md) for the searchable HTML reference.

## Results and composition

Commands return `Prog g Int32` with the failure effect. Ordinary `do` binds normal results
and propagates failure. `try ... catch _ => ...` recovers locally; `action.ignore` suppresses
failure and discards the normal value. `Prog.attempt action` captures completion as ordinary
Option data. See [failure and recovery](failure.md).

The compiler captures only demanded result components. A directly ignored command emits
the command itself. Failure-propagating code needs its success bit; code observing its
numeric result also needs the payload.
Ignoring a named call preserves control flow inside that function.

## Context and argument stages

Each command combines its intrinsic requirements with those of its actual arguments.
Explicit targets and constant providers can have fewer requirements than `.self`,
relative positions, or resource-backed providers.
[Execute](execute.md) supplies and transforms context for a complete Prog body.

Shared argument types are defined in [Std.Command.Arg](../Oria/Std/Command/Arg.lean).
Expected-type elaboration accepts host numbers and `Val Int32` expressions for numeric
arguments. Structured selectors express target cardinality and filters.
Host decimal coordinates retain their fractional value.

Static fragments remain literal command text. Dynamic inputs become typed macro holes;
one dynamic input does not make the other arguments dynamic.
Host NBT, mixed-field compounds, and runtime NBT snapshots share the NBT argument codecs.
Minecraft's native macro serialization has its own numeric and string behavior;
[NBT transport](nbt.md#native-macro-transport) describes the boundary.

## Command families

| Task | Guide |
| --- | --- |
| Discover structures, query server state, open dialogs, send chat | [Discovery and interaction](discovery-and-interaction.md) |
| Scores, objectives, player trigger input | [Scoreboard and trigger](scoreboard-trigger.md) |
| Teleport, spawn, remove entities, apply effects | [Entity commands](entity-commands.md) |
| Tags, titles, action bars, sounds | [Presentation](presentation-commands.md) |
| Weather, clocks, borders, players, teams, bossbars | [World and player commands](world-and-player-commands.md) |
| Game rules, attributes, movement, particles, scoreboard display | [Gameplay control](gameplay-control.md) |
| Items, components, inventories, loot, blocks, copying | [Items and blocks](items-and-blocks.md) |
| Biomes, structures, waypoints, stopwatches | [Generation, navigation, and timing](generation-navigation-timing.md) |
| Data access, immutable NBT values, typed host codecs | [NBT](nbt.md) |
| Ordered Execute chains, selectors, conditions, receivers | [Execute](execute.md) |
| Administrative state and server operations | [Server control](server-control.md) |

The default declarations are assembled by [Std.Manifest](../Oria/Std/Manifest.lean).
A datapack may supply an explicit catalog through its settings.
Command-library authors use `Command.Decl`, `Command.Ref`, `ArgCodec`, and `Command.emit`;
the core compiler consumes their typed signatures and fragment algebra.

## Acceptance

`scripts/quality` checks docstring examples, diagnostics, codecs, and emitted artifacts.
`scripts/gametest` executes the language runtime, memory protocols, and core commands.
`scripts/rps-test` executes player interactions and the command-family fixtures.
Its `--language` and `--admin` modes run the record/control-flow and administrative suites.

The fixtures check chosen native results and state changes, including empty selections,
unchanged-data failures, macro arguments, and storage cleanup.
Packet inspection checks server-side presentation behavior; client rendering and audio
require client acceptance. The [integration guide](../integration/datapack/README.md)
lists the suites and their limits.
