# Generation, navigation, and timing

These interfaces target Minecraft Java 26.3 / DP121. They reuse block coordinates, resource
IDs/tags, registry descriptions, named colors, numeric holes, and the Failure protocol.

| Module | Interface | Native result |
| --- | --- | --- |
| FillBiome | run region biome optional-filter | Number of changed biome samples |
| Place | feature, jigsaw, structure, template | 1 on successful generation or placement |
| Waypoint | list, modify | Tracked count for list; successful 0 for modify |
| Stopwatch | create, query, restart, remove | 1 for lifecycle operations; scaled elapsed time for query |

## Biome cells

`FillBiome.run box biome filter` accepts an inclusive BlockBox. The target biome is a
ResourceId; the optional filter is a ResourceOrTag matching the existing biome.

Minecraft quantizes each corner down to a multiple of four. One sample represents a
4 by 4 by 4 block cell. An aligned region from (0,0,0) through (7,7,7) therefore contains
eight samples. Replacing those samples with their current biome fails because none change.
A filter counts changed matching samples, not all matching samples.

The receiving dimension and coordinate requirements determine the grade. Explicit absolute
corners need dimension; relative corners also need position; local corners retain the shared
local-coordinate requirements. Registry IDs and filters are host values. Runtime I32
coordinates use existing macro holes.

The native region limit and loaded-chunk checks apply. Block-level biome queries use
Minecraft's neighboring-sample selection, so their boundary does not exactly follow the
quart-cell grid.

## Placement

The four Place operations have distinct native contracts:

| Operation | Description | Parameters |
| --- | --- | --- |
| feature | Run a world-generation feature | Named/inline Feature and block position |
| jigsaw | Generate a template pool from a named connector | Pool, connector, depth, position |
| structure | Generate a registered structure | Structure ID and position |
| template | Place a saved template | Template ID, position, TemplateSettings |

BlockPos.here is the default destination. It emits relative zero coordinates and is resolved
to a block position by Minecraft. Absolute coordinates remove the caller-position
requirement. The dimension requirement remains.

Feature descriptions use RegistryValue, with the existing nominal argument identity and
fragment planner. Feature.named and Feature.ofNbt establish a placement-context contract:
the native generator receives its own world, origin, generator, and random source.
Feature.inline preserves any explicit requirements on supplied command fragments.
This information is recorded during construction and retained by the codec.

```lean
Place.feature (Feature.named "demo:tree")
Place.feature (Feature.ofNbt
  (nbt% {type: "minecraft:simple_block", to_place: {id: "minecraft:gold_block"}}))
```

Feature placement requires the surrounding 3 by 3 chunks. Jigsaw depth is an integer in
1..20 and may come from a runtime I32. Pool, connector, structure, and template IDs are host
resources. Structure generation uses the world's generator, seed, and terrain, and need not
put the first block at the supplied position.

TemplateSettings contains:

| Field | Default | Interpretation |
| --- | --- | --- |
| rotation | none | None, clockwise 90/180, or counterclockwise 90 degrees |
| mirror | none | Reflect X with frontBack or Z with leftRight, before rotation |
| integrity | 1 | Float32 block-retention probability in 0..1 |
| seed | 0 | Signed I32; nonzero seeds select repeatable native randomness |
| strict | false | Suppress neighbor and shape updates |

Seed zero uses Minecraft's time-derived random source. Integrity and seed accept dynamic
I32 holes; integrity also accepts host decimals. The codec emits the numeric settings before
the optional strict token, preserving the native grammar. The
[1.21.5 release notes](https://www.minecraft.net/en-us/article/minecraft-java-edition-1-21-5)
describe strict placement and its argument order.

```lean
Place.template "demo:room" .here {
  rotation := .clockwise90
  mirror := .frontBack
  integrity := .decimal 0.95
  seed := .static 42
  strict := true }
```

A placement result of 1 describes native success, not the number of changed blocks.
For example, a valid template with integrity zero can succeed while placing no blocks.
Generators can modify world state before reporting failure; failure does not roll back changes.
Placement retains the existing conservative world/score/random/HUD/sound effect bound.

## Waypoint icons

Waypoint.list returns the count tracked by the current dimension's waypoint manager.
An empty manager succeeds with zero. Waypoint.modify selects one transmitter and changes
its icon; native success also returns zero, including repeated assignments.

```lean
Waypoint.modify .self (.color (some .gold))
Waypoint.modify .self (.hex "6495ED")
Waypoint.modify .self (.hex "f0A")
Waypoint.modify .self (.color none)
Waypoint.modify .self (.style (some "minecraft:bowtie"))
Waypoint.modify .self (.style none)
```

Named colors reuse TeamColor. HexColor accepts exactly three or six ASCII hexadecimal
digits without a prefix. It uses Lean's character predicate, a Prop contract, checked
literals, and parse for computed host strings. The three-digit form expands each digit;
f0A denotes FF00AA.

Minecraft's parser requires a singular target. Missing targets and entities that do not
implement the transmitter interface fail during execution. A living transmitter with zero
transmission range can still have its icon changed. The grade combines dimension, selector
requirements, and world/HUD effects with the existing selector effect bound.

The command changes icon properties. Transmission/reception ranges remain Attribute
operations; visibility also depends on the locator-bar rule, teams, and player state.
A style names a client resource-pack asset. The
[1.21.6 release notes](https://www.minecraft.net/en-us/article/minecraft-java-edition-1-21-6)
describe the server-controlled locator bar and waypoint-style assets.

## Real-time stopwatches

Stopwatch IDs are server-wide resources. Create starts a new clock; duplicate creation fails
and retains the existing clock. Restart resets an existing clock. Remove deletes it.
All three successful operations return 1; a missing name fails for query/restart/remove.

Stopwatches measure server-running real time, including paused time, independently of tick
rate. The world saves accumulated elapsed time and excludes offline time on restoration.
The native clock's resolution is milliseconds. These semantics are documented in the
[1.21.11 release notes](https://www.minecraft.net/en-us/article/minecraft-java-edition-1-21-11).

Query computes:

\[
r = \operatorname{I32Cast}
    \left(\operatorname{elapsedSeconds}\cdot\operatorname{scale}\right).
\]

The Java conversion truncates toward zero and saturates at the I32 bounds. The default
scale is 1; scale 1000 returns milliseconds. Larger scales retain millisecond resolution.
Zero and negative scales are accepted. A valid zero result remains successful.

```lean
let ms ← Stopwatch.query "demo:lap" (.static 1000)
Scoreboard.set .self "demo.elapsed_ms" (.dynamic ms)
```

IDs are host resources. Scale accepts host decimals and runtime I32 values. The operations
have Req.none and Eff.world: they access server-wide state rather than the executor's
dimension or position. Effectful query computations remain ordinary Prog actions.

## Compilation and verification

The four modules use existing command declarations and ArgCodec instances. Their output
passes through the existing Tree, Cont, Machine, and DP121 command paths. Static leaves
stay literal; each dynamic integer gets a macro hole. Command success/result demand remains
the existing analysis, including successful zero from Waypoint and Stopwatch.

[StandardLibrary](../Oria/Examples/StandardLibrary.lean) contains checked examples for arena
biomes, seeded room placement, inline features, waypoint iteration, and timed placement.

[StdGeneration](../Oria/Proofs/StdGeneration.lean) checks context contracts, lexical color
validation, and exact encoding. The
[generation fixture](../Oria/Proofs/Fixtures/Generation.lean) contains 43 entries with a
separate [golden](../tests/golden/generation.dp121). The
[native acceptance](../integration/rps/GenerationAcceptance.java) checks changed biome cells,
named/inline features, connector success/failure, structure generation, template transforms,
block-entity NBT, seed repeatability, dynamic bounds, waypoint fields, and stopwatch outcomes.
Clock assertions bracket each query with native clock readings instead of assuming elapsed
wall time.

The command registrations and implementations in the server pinned by
[minecraft-26.3.lock.json](../minecraft-26.3.lock.json) are the reference for the current
syntax, conversion rules, return values, and generation behavior.
