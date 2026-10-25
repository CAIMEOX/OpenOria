# Execution scopes, selectors, and receivers

Oria targets Minecraft Java 26.3 / DP121. An execution scope transforms the command context
and runs a complete body in each resulting context. This supports player iteration,
inventory conditions, entity relationships, and native result storage within ordinary Prog.

## Context requirements

In `Prog ⟨ρ, ε⟩ A`, ρ records required implicit inputs and ε records observable effects.
Sequential composition and branch joins take the union of their requirements and effects.

| Requirement | Implicit input |
| --- | --- |
| `Req.executor` | Executing entity, used by self |
| `Req.position` | Execution position, used by relative coordinates |
| `Req.rotation` | Execution rotation, used by local coordinates and relative angles |
| `Req.dimension` | Execution world, used by block queries and coordinate teleportation |
| `Req.anchor` | Feet/eyes anchor, used by local coordinates and facing |

A command call combines its declared requirement with those of its argument encoders:

\[
\rho_{\mathrm{call}}
  = \rho_{\mathrm{command}}
    \cup \bigcup_i \rho_{\mathrm{argument}_i}.
\]

Thus reading a named score holder has no executor requirement; reading self does.
Structured descriptions establish their dependencies when constructed. Arbitrary external
predicates and raw selector text retain conservative requirements because Minecraft
interprets their definitions at runtime.

This is a flat coeffect discipline in the sense of
[Petricek, Orchard, and Mycroft, §§2.4, 3.5](https://tomasp.net/academic/papers/structural/coeffects-icfp.pdf):
one requirement set annotates a computation. Value liveness remains a separate analysis.
The use/supply relationship also corresponds to the IVAR/WITH rules of
[Implicit Parameters](https://launchbury.blog/wp-content/uploads/2019/01/implicit-paramters.pdf).

## Ordered context transformations

A step records the context it reads, N, and supplies, G. Its transformation of body
requirements is

\[
T_{N,G}(\rho)=N\cup(\rho\setminus G).
\]

For a followed by b:

\[
\begin{aligned}
N_{a;b} &= N_a\cup(N_b\setminus G_a),\\
G_{a;b} &= G_a\cup G_b.
\end{aligned}
\]

Consequently, `T(a;b, ρ) = T(a, T(b, ρ))`. ContextChange proves this composition law,
associativity, identity, monotonicity, and the correspondence between required and available
context. Argument requirements enter at the step where the argument is resolved.

| Step | Context behavior |
| --- | --- |
| as | Supply executor; retain position, rotation, dimension, anchor |
| at | Supply position, rotation, dimension; retain executor and anchor |
| positioned | Supply position and feet anchor |
| positionedAs | Supply position; retain anchor |
| positionedOver | Read position/dimension and replace Y with a heightmap height; retain anchor |
| rotated / rotatedAs | Supply rotation; relative angles read the original rotation |
| in | Read position/dimension and apply native dimension scaling |
| anchored | Supply the anchor |
| align | Read position and floor selected axes |
| facing / facingEntity | Read position, anchor, and executor; supply rotation |
| on | Read executor and follow a relationship; retain all other context |
| summon | Read position/dimension, spawn, and supply the new executor |
| when / unless | Filter branches using the condition's requirements |
| storeResult / storeSuccess | Capture a receiver at this point in the chain |

For example, as-all-players followed by at-self needs no incoming executor. Reversing the
steps needs one. Likewise, on-vehicle changes self but retains the caller's position;
an explicit at-self step follows the vehicle's location.

Relationships are owner, leasher, target, attacker, vehicle, controller, origin, and direct
passengers. Missing relations produce zero contexts; passengers can produce several.
Heightmaps are world surface, motion blocking, motion blocking without leaves, and ocean
floor. Native chunk availability is required.

## Prog composition

`Execute.forEach steps body` accepts `Prog g Unit` or `Prog g Int32` and returns Unit.
Unit completion supplies native result zero; Int32 completion supplies its normal result.
The outer grade masks body failure while retaining its remaining effects.
Each final context runs the whole body. Body failure ends that invocation; Minecraft
continues the other contexts. Multiple as/passengers steps can multiply the branch count.
The body is synchronous: its grade must satisfy `g.canSuspend = false`. Cooperative task
suspension occurs outside Execute scopes; the current task cost model diagnoses Execute
traversal as unknown. See [cooperative tasks](tasks.md).

```lean
Execute.forEach [
  .as (.allPlayers {gameMode := some (.exclude .spectator)}),
  .at .self,
  .when (.items ⟨.entity .self, .range "weapon.mainhand"⟩
    {target := some (.id "minecraft:apple")}),
  .storeResult (.nbt (.storage "demo:state") (.key "score") .int (.static 1))] do
    Scoreboard.get .self points
```

The enclosing as/at pair supplies the executor, position, and dimension used by the body
and inventory condition. The storage receiver gets each matching player's result in native
execution order. The Lean-checked example is
[recordHeldItemScore](../Oria/Examples/StandardLibrary.lean).

Ordinary do notation normalizes static grade expressions at composition boundaries.
A host let constructs a computation and retains its latent requirements; a do bind executes
it. Captured Val arguments are values, whereas self and relative coordinates are resolved
inside each invocation. This resembles the Reader-indexed treatment in
[Embedding effect systems in Haskell, §8](https://tomasp.net/academic/papers/haskell-effects/haskell-effects.pdf).

Load/tick entries provide `Req.server`: position, rotation, dimension, and anchor.
The entry builder checks that the function's required inputs are available.

## Conditions and shared arguments

| Condition | Meaning |
| --- | --- |
| entity | A selector has a match |
| matches / compare | Native score comparison, including missing-score behavior |
| data | An NBT path selects at least one node |
| block | Block ID/tag, property constraints, and optional block-entity NBT |
| blocks | Equal block states and block-entity data in two regions; masked ignores source air |
| biome | Biome ID or tag at a block position |
| dimension | The current dimension equals the named dimension |
| loaded | The chunk has ENTITY_TICKING status and its entities are loaded |
| items | At least one selected slot's item matches an ItemPredicate |
| slots | At least one slot exists, even if its item stack is empty |
| predicate | A named or inline predicate holds |

Block queries reuse BlockPos, BlockBox, and BlockPredicate. Inventory queries reuse Inventory,
SlotSource, and ItemPredicate, including dynamic slot indices and resource/inline slot
definitions. Both inventory conditions retain the native slot context's position/dimension
requirements. Predicate descriptions reuse RegistryValue and retain conservative
requirements for external definitions.

Loaded is a readiness query, not a chunk-loading operation. Condition errors retain
Minecraft's behavior; unless does not turn every resolution error into a passing branch.

## Structured selectors

Filters cover tags, teams, entity type, quoted name, game mode, experience level, score
ranges, limit, sort order, distance, explicit X/Y/Z origin, DX/DY/DZ box extents, pitch/yaw
ranges, named predicates, NBT, and advancements or individual advancement criteria.

A full explicit origin removes the execution-position requirement from spatial selection.
Any omitted component comes from the caller. Explicit coordinates and spatial constraints
retain a dimension requirement. Box extents use Minecraft's native bounding-box
intersection rules; rotation intervals use its angle wrapping.

Rotation, NBT, and advancement filters inspect candidates. Selector predicates receive
each candidate's entity, position, and world through Minecraft's SELECTOR loot context;
they do not read the incoming executor. This differs from execute-predicate, which uses
the current execution context.

Entity names use Brigadier quoted strings: quote and backslash
are escaped. This grammar differs from SNBT strings. Shared literal validation rejects
physical control characters and function-macro substitutions before emission.
Tag/team words and advancement criterion names use the native unquoted-word grammar.
Criterion names use the shared checked Word type. Range bounds, resource contents,
and selector cardinality are checked by Minecraft.

## Store receivers and results

The receiver is explicit:

```lean
.storeResult (.score ⟨.self, points⟩)
.storeSuccess (.nbt (.storage "demo:state") (.key "ok") .byte (.static 1))
.storeResult (.nbt (.entity .self) (.key "Air") .short (.static 1))
.storeResult (.nbt (.block position) (.key "TransferCooldown") .int (.static 1))
.storeResult (.bossbar "demo:progress" .value)
```

Score stores carry world/scoreboard-write effects; NBT stores carry world effects; bossbar
stores carry world/HUD effects. These classifications travel with the existing Scope
metadata through IR maps. The backend continues to use the shared command-fragment planner.

StoreSuccess demands only the success component. StoreResult demands both components to
export the native failure result correctly. Successful zero and failure remain distinct.
The NBT result is multiplied by its scale and converted to byte, short, int, long, float,
or double using the server's Java conversions. Integer conversions truncate toward zero
before narrowing; for example, -7 scaled by 0.5 becomes integer -3 or floating-point -3.5.
Dynamic integer path indices and scales use the existing macro-hole protocol.

A receiver before a fork is resolved in the pre-fork context. A receiver after a fork is
resolved separately in each produced context. Repeated deliveries overwrite; accumulation
requires an explicit operation in the body. Destination callback errors follow native
handling and do not become an Oria body failure. Entity writes retain Minecraft's
restrictions, including its restriction on writing player NBT.

## Teleportation

`Teleport.to target position orientation` accepts an optional RotationAction:
explicit angles, facing coordinates, or facing a singular entity/anchor. It reuses the same
rotation codec as Rotate. The default orientation preserves native teleport behavior.

`Teleport.entity target destination` copies the destination entity's dimension,
position, and rotation. It needs only the two selectors' context requirements.
The moved target set can contain multiple entities; entity destinations and facing entities
must be singular. Native success returns the teleported count.

Static decimals and dynamic I32 components can be mixed. Integer X/Z coordinates retain
native block centering; decimal spelling selects exact coordinates.

## Compilation and verification

1. Tree retains a scoped body with its grade and captured values.
2. Lower.Scope extracts an internal function with the lexical environment as arguments,
   following [lambda lifting](https://link.springer.com/chapter/10.1007/3-540-15975-4_37).
   Parameter demand removes unused capture components.
3. Cont and Machine retain scoped invocation. Liveness and allocation account for the body's
   clobbers and the receiver's result demand.
4. DP121 freezes the used captures. Each native branch invokes a wrapper that restores them,
   calls the body, cleans its frame, and exports the demanded native channels.
5. The caller resumes after all branches and releases the frozen frame. Temporary objects
   share the public invocation's arena.

Fragment planning reuses ordinary literal checks, macro-hole collection, and bounded
argument indexing. A dynamic prefix is expanded before its body runs; nested commands may
then reuse the macro buffer.

The pinned server's ExecuteCommand, EntitySelectorOptions, TeleportCommand, and
CommandSourceStack establish the native behavior. The
[26.3 release notes](https://www.minecraft.net/en-us/article/minecraft-java-edition-26-3)
describe the current slot-source grammar; the
[1.19.4 release notes](https://www.minecraft.net/en-us/article/minecraft-java-edition-1-19-4)
give the background for relationship and heightmap operations.

[ExecuteSyntax](../Oria/Proofs/ExecuteSyntax.lean) and
[CommandArguments](../Oria/Proofs/CommandArguments.lean) check static contracts.
The [execution fixture](../Oria/Proofs/Fixtures/Batch/Execution.lean) and
[native acceptance](../integration/rps/ExecutionAcceptance.java) check filtering,
empty slots, relationships, heightmaps, all numeric NBT tags, dynamic paths, receiver
binding around forks, failure/zero outcomes, and teleport destinations/rotations.
The batch golden records emitted command text and macro writes.
