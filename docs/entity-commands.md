# Entity commands

`import Oria` provides Kill, Summon, and Effect for Minecraft Java 26.3 / DP121. They use the
same `Prog g Int32`, do notation, and recovery semantics as other standard commands.

## Interfaces and results

| Interface | Successful payload | Required context |
| --- | --- | --- |
| `Kill.run targets` | Number of selected entities processed | Dimension and target selection |
| `Summon.here entity` | 1 | Position and dimension |
| `Summon.at entity position data?` | 1, including when passengers are created | Dimension, coordinates, and NBT fragments |
| `Effect.give targets effect` | Number of living entities whose effect state changed | Target selection |
| `Effect.giveFor targets effect duration amplifier hideParticles` | Number of changed living entities | Target selection |
| `Effect.clear targets effect?` | Number of changed living entities | Target selection |

Target cardinality belongs to the receiving native command. `Target` describes the same
names, UUID text, and structured selectors for these commands and for single-target commands
such as Teleport. A structured self target requires an executor; a filtered all-player target
can be used directly from a server callback. Native Effect attribution uses the source entity
when one exists; server execution is also valid.

The effect bound includes world mutation, scoreboard reads/writes, and randomness. It covers
selector evaluation, spawn initialization, and death processing that may update statistics.

```lean
open Oria Oria.Std Oria.Std.Command.Arg

def temporary : Target := .selector (.allEntities {
  tags := [.include "game.temporary"]
})

@[mcfunction]
def cleanup : Prog (Kill.grade temporary).handled Unit :=
  (Kill.run temporary).ignore
```

Kill fails on an empty selection. Effect ignores non-living entities and fails when no
living entity changes. Clearing several effects on one entity still contributes one to
the result. Giving an equal or weaker effect may leave its state unchanged. Summon fails
for invalid spawn bounds, disallowed peaceful-mode entity types, creation failures, or
duplicate UUIDs.

## Summon data and staging

`Summon.here` uses the current position. `Summon.at` accepts world or local coordinates,
including host decimals and runtime I32 components. Its final argument is `Option Compound`.
Omitting it invokes Minecraft's mob spawn initialization. Supplying `.value (nbt% {})` follows
the explicit-NBT form and skips that initialization.

`Std.Command.Arg.Compound` is shared argument syntax:

- `.value nbt` embeds a host `Nbt.Value .compound`.
- `.fields fields` combines static NBT leaves and typed holes with the existing fragment algebra.
- `.dynamic value` accepts a runtime `Val (Nbt.Data (some .compound))` from any arena region.

The latter uses native macro SNBT serialization; its numeric formatting follows Minecraft.
The original snapshot remains immutable. A caller reading untyped NBT must establish that it
is a compound before using the typed dynamic constructor.

```lean
def markerPosition : Vec3 := .world
  (.relative (.static 0)) (.relative (.decimal 0.25)) (.relative (.decimal 0.5))

@[mcfunction]
def marker : Prog (Summon.grade (some markerPosition)) Int32 := do
  Summon.at "minecraft:marker" markerPosition
    (some (.value (nbt% {Tags: ["game.temporary"]})))
```

The checked `spawnYoungPig` example in
[StandardLibrary](../Oria/Examples/StandardLibrary.lean) mixes a runtime offset and age with
static tags and fractional coordinates. The acceptance fixture also materializes a compound
snapshot with passengers and passes the entire value through one native NBT macro hole.

## Effect duration

`Effect.give` preserves Minecraft's omitted arguments: amplifier zero, visible particles,
and a duration of 600 ticks for ordinary effects or 1 tick for instantaneous effects.
`Effect.giveFor` supplies the full argument tail:

```lean
example (seconds : Val Int32) :=
  Effect.giveFor .self "minecraft:speed" (.finite (.dynamic seconds)) (.static 1) true

example := Effect.giveFor .self "minecraft:night_vision" .infinite
example := Effect.clear .self (some "minecraft:speed")
example := Effect.clear .self
```

Finite counts range from 1 to 1000000 in DP121. For ordinary effects they count seconds; for
instantaneous effects they count ticks. Amplifiers range from 0 to 255 and are zero-based.
Both integers can be static or dynamic. The particle flag is a host Bool and also controls
the HUD icon. Infinite duration is a native token, introduced in
[Java Edition 1.19.4](https://www.minecraft.net/en-us/article/minecraft-java-edition-1-19-4).

Minecraft parses static command syntax when loading a function. An unknown resource or
invalid static argument can prevent that function from loading. Dynamic arguments are parsed
after macro substitution; an invalid duration or amplifier then produces command failure.
Normal do notation propagates failure. Explicit discard permits cleanup to continue.

## Implementation and verification

The wrappers contribute declarations and ordinary command calls. Duration, Bool, entity
targets, and compound NBT use shared argument codecs. `ArgCodec (A : Type u)` permits host
descriptions that quantify over arena regions, while encoding still produces the existing
`Fragment EncodedVal`. This universe parameter has no runtime representation.

`StdEntities` checks context contracts and command text. The
[entity snapshot](../tests/golden/entities.dp121) fixes generated commands, result capture,
and macro fields for a stack-backed compilation. `scripts/rps-test` runs
`integration/rps/EntityAcceptance.java` before the player-game checks. Native assertions cover
spawn positions, dynamic fields, runtime snapshots, passengers, duplicate UUIDs, mixed
living/non-living selections, effect counts, finite/infinite/instantaneous durations, dynamic
bounds failures, kill-self cleanup, short-circuiting, and explicit recovery.

Contracts were checked against `KillCommand`, `SummonCommand`, `EffectCommands`, and
`CommandResponseTracker` in the server pinned by
[minecraft-26.3.lock.json](../minecraft-26.3.lock.json). The
[26.3 release notes](https://www.minecraft.net/en-us/article/minecraft-java-edition-26-3)
also record the corrected effect-command feedback for partially affected selections.
