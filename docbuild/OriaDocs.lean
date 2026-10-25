module

public import Oria.Std
public import Oria.Examples.StandardLibrary
public import Oria.Examples.RockPaperScissors
public import Oria.Examples.MergeSort
public import Oria.Examples.Elaboration
public import Oria.Examples.GlobalNbt
public import Oria.Examples.Calls
public import Oria.Std.Compute.Number
public import Oria.Std.Manifest
public import Oria.Std.DP121

/-!
# Oria documentation

Oria is a Lean 4 embedded language for Minecraft datapacks.

- Read the [standard library guide](##Oria.Std) for commands, results, and context requirements.
- Browse the [examples](##Oria.Examples.StandardLibrary) for checked object functions;
  follow their source links for complete code.
- Play [rock-paper-scissors](##Oria.Examples.RockPaperScissors), a per-player best-of-three
  game combining input, random moves, ADT matching, and persistent scoreboard state.
- Explore [function calls](##Oria.Examples.Calls): long chains, shared-callee trees,
  wide parameter lists, and values retained across calls.
- Sort runtime I32 input with [NBT merge sort](##Oria.Examples.MergeSort), using derived
  typed native lists, cached scalar heads, and cooperative task checkpoints.
- Follow [type-directed elaboration](##Oria.Examples.Elaboration) for shared pure values,
  nested records, local recursion, and typed native paths.
- Use [global native documents](##Oria.Examples.GlobalNbt) for mutable typed storage
  retained across invocations and matching-schema reloads.
- Look up coordinates, targets, ranges, and score locations in
  [shared arguments](##Oria.Std.Command.Arg).
- Configure [world clocks](##Oria.Std.Time), [world borders](##Oria.Std.WorldBorder),
  [teams](##Oria.Std.Team), and [boss bars](##Oria.Std.Bossbar) through typed command arguments.
- Use [typed rules](##Oria.Std.Gamerule), [particle options](##Oria.Std.Particle),
  [respawn settings](##Oria.Std.Spawnpoint), and
  [scoreboard presentation](##Oria.Std.Scoreboard) for gameplay control.
- Compose [inventory transfers](##Oria.Std.Item), [loot](##Oria.Std.Loot), and
  [block regions](##Oria.Std.Fill) with shared typed descriptions.

This site is generated from source documentation. Search by Lean declaration name,
for example Oria.Std.Scoreboard.get. The repository's docs directory describes the
compiler architecture and memory protocols.
-/
