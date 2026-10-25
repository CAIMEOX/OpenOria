# Items, inventories, loot, and blocks

These interfaces target Minecraft Java 26.3 / DP121. They share argument descriptions over
the existing Fragment, ArgCodec, and NBT facilities. Typed operation arguments select native
variants within the command families below.

| Module | Interface | Native scope |
| --- | --- | --- |
| Give | `to players item count` | Item IDs, component patches, dynamic count |
| Clear | `run players predicate limit` | IDs/tags, component tests, counting and removal |
| Item | `transfer target source mode`, `modify target modifier` | Multi-slot replace/fill/override and modifiers |
| Loot | `run target source` | Give/spawn/insert/replace; table/mine/kill/fish |
| Setblock | `set position block mode` | Replace/destroy/keep/strict and block-entity NBT |
| Fill | `run box block mode` | Keep or filtered normal/destroy/hollow/outline/strict |
| Clone | `run request` | Dimensions, filters, overlap, move, strict, block-entity copying |

The [checked examples](../Oria/Examples/StandardLibrary.lean) include item prizes, chest
stocking, and arena-floor replacement.

## Item construction and matching

`ItemSpec` holds an item ID and a component patch. Count is a separate command argument.
A patch sets a component to an SNBT fragment or removes a default component. Host values use
`ComponentPatch.ofNbt`; mixed fields use existing Fragment operations.

```lean
example (round : Val Int32) := Give.to .self {
  id := "minecraft:apple"
  components := [
    .ofNbt "minecraft:custom_name" ("Round prize" : String),
    .set "minecraft:custom_data" (.nbtCompound [(⟨"round"⟩, .hole .i32 round)])] }
```

This description emits an item argument with native bracket syntax:
`minecraft:apple[minecraft:custom_name="Round prize",minecraft:custom_data={round:$(p0)}]`.
Static text stays in the command; only the computed integer becomes a macro argument.
Minecraft checks component names, schemas, duplicate patches, and stack invariants.

`ItemPredicate` selects an item ID, a tag, or every item type. Its list of tests is a conjunction;
`ItemTest.either` expresses alternatives within a test. Presence, exact component equality,
and component sub-predicates each support atomic negation.

```lean
example := Clear.run .self {
  target := some (.id "minecraft:apple")
  tests := [.matches "minecraft:custom_data" (.nbt (nbt% {round: 2}))] }
  (some (.static 0))
```

Count zero is a native non-mutating query. An omitted limit removes all matches; a positive
limit applies per selected player. The result sums matching or removed items. No matches
fails, including in count-only mode. Exact equality and sub-predicate matching have different
native semantics; custom-data matching can inspect a subset of a compound.

## Slots and native inventory transfers

`Inventory` pairs an `InventoryTarget` with a `SlotSource`. Targets are block inventories or
entity selections. Slot sources accept native literal ranges, one dynamically indexed Slot,
or a named/inline SlotDefinition. Single Slot arguments accept a static name or a named group
with a Scalar index.

```lean
example (i : Val Int32) := Item.transfer
  ⟨.entity .self, .single (.indexed "hotbar" (.dynamic i))⟩
  (.stack {id := "minecraft:apple"} (.static 4))
```

The native item command constructs a slot-source context containing position, dimension,
and container even for a literal range. The current executor is an optional native input;
a named or arbitrary inline definition conservatively requires the full context.
`Item.grade` retains these requirements together with target/source requirements.

For destination slots containing `[A,B,C,D,E]` and two source entries `[X,Y]`:

| Distribution | Result |
| --- | --- |
| replace | `[X,Y,C,D,E]` |
| fill | `[X,Y,X,Y,X]` |
| override | `[X,Y,empty,empty,empty]` |

Source slot order is significant. Multi-entity sources concatenate their slot sequences.
Source modifiers operate on copied stacks, leaving the source inventory unchanged.
Native slot selection, stack limits, and target compatibility determine success. A command
can update part of a selection; failure does not roll back earlier native changes.

`ItemModifier.setCount n add` is a semantic constructor for a constant/runtime integer count.
Its proof states that the modifier adds no context requirements. The item command still
constructs the native position/dimension context.

## Registry descriptions and loot

`RegistryValue k` shares named and inline description syntax while its registry index
distinguishes ItemModifier, SlotDefinition, and LootTable. The constructor establishes a
context summary that encoding preserves. Named resources and arbitrary inline NBT retain
a conservative summary; semantic constructors can give a smaller one.

```lean
example := Item.modify
  ⟨.entity .self, .range "weapon.mainhand"⟩
  (ItemModifier.setCount (.static 2) true)
example := Loot.run (.give .self) (.table (.named "game:round_reward"))
```

Loot source evaluation is separate from distribution. Sources cover a named/inline table,
a living entity's death table, block mining, and fishing with an optional explicit or held tool.
Mining and kill sources evaluate drops without removing the block or killing the entity.

Loot destinations cover players, item entities, insertion into a block inventory, and
replacement in block/entity inventories. DP121 `loot replace` starts at one Slot and optionally
supplies a consecutive-slot count. This differs from `item`, which evaluates a multi-slot
SlotSource. Results retain native successful-distribution counts and partial-update behavior;
they do not uniformly count individual items.

External loot resources can trigger native gameplay and advancement behavior. Reward functions
must respect the [invocation constraints](world-and-player-commands.md#advancement-rewards-and-invocation-boundaries)
while an Oria entry is active.

## Block descriptions and regions

Concrete BlockState and BlockPredicate share `BlockDesc a`: a head, properties, and optional NBT.
The head type permits a single block ID for placement and an ID-or-tag selector for matching.
Properties use native words or Scalar integers. Minecraft validates each property's existence
and allowed values.

```lean
example (level : Val Int32) := Setblock.set
  (.world (.relative (.static 0)) (.relative (.static 0)) (.relative (.static 0)))
  {id := "minecraft:light", properties := [("level", .number (.dynamic level))]}
```

Omitted block-entity NBT preserves data when native placement retains the block entity.
An explicit empty compound supplies empty data and can clear inventory contents.
The same Compound interface accepts host NBT, mixed fields, or runtime compound snapshots.

BlockBox specifies two inclusive corners. FillMode makes keep a separate case; replacement
combines an optional BlockPredicate with a FillStyle. This represents the native legal
combinations and orders filter syntax before placement style.

CloneSpec records a source box, destination, optional source/destination dimensions, filtering,
strict placement, and normal/force/move behavior. Omitted dimensions each use the command
dimension. Relative coordinates resolve against the command source; explicit dimensions
do not imply portal-style coordinate scaling. The command also reads its source context's
block-modification game rule.

Normal clone rejects overlap; force permits it; move clears selected source blocks. Masked
clone skips air. Filtered clone preserves destination cells outside the source predicate.
Native block-entity data is copied independently. Strict suppresses neighbor and shape updates.

## Serialization and failure

Static NBT uses the shared formatter and escaping rules. Dynamic I32 fields and slot/property
indices use existing macro holes. A runtime compound can be supplied as a complete component
value or block-entity suffix through Minecraft's native macro serialization.

A fragment supplied as a component value must encode SNBT. Native macro serialization of a
runtime string produces raw text, so a bare string snapshot is not a general quoted SNBT value.
Keep such text static or carry it inside a serialized compound when the component schema accepts
that compound. These interfaces do not add runtime string escaping.

Static syntax is parsed when functions load; malformed static descriptions may prevent loading.
Dynamic syntax is parsed after macro substitution and can fail on invocation. Loaded chunks,
world bounds, registry entries, native count/region limits, and current state remain runtime
conditions. Commands retain native success and result; ignore retains execution without
requesting the result.

## Verification

`StdContent` checks context contracts and exact encoding for component patches, item predicates,
and block descriptions. The batch fixture's golden fixes command
text and macro writes. `scripts/rps-test` checks inventory contents, component matching,
slot distributions, named/inline resources, modifiers, runtime NBT, block placement modes,
filtered fills, block-entity copying, overlap, move, and cross-dimension cloning.

The reference is the server pinned in
[`minecraft-26.3.lock.json`](../minecraft-26.3.lock.json), including ItemCommands, LootCommand,
ItemParser, ComponentPredicateParser, SlotSourceArgument, BlockStateParser, SetBlockCommand,
FillCommand, and CloneCommands. The official
[26.3 release notes](https://www.minecraft.net/en-us/article/minecraft-java-edition-26-3)
describe multi-slot item sources and resource-or-inline registry values; the
[block command syntax](https://feedback.minecraft.net/hc/en-us/articles/33310041339789-Minecraft-Java-Edition-Snapshot-25w02a)
documents strict placement and filter ordering.
