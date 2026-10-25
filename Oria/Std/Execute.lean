module

public import Oria.Std.Command.Arg.Data
public import Oria.Std.Command.Arg.Position
public import Oria.Std.Command.Arg.Block
public import Oria.Std.Command.Arg.Item
public import Oria.Command.Execute

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Execution scopes

`Execute.forEach steps body` runs the complete body once per context produced by the native
execution chain. The body returns Unit or Int32; the enclosing computation returns Unit.
Normal Unit completion supplies native result zero. The scope masks body failure from
its outward effect grade.
Body failure ends the current branch, while other branches continue. If no final context
remains, the body runs zero times.

Steps are interpreted in order. `as` supplies an executor; `at` supplies position, rotation,
and dimension. For example, `as @a; at @s` selects players and then uses each player's
position. `as @a` alone retains the caller's position. Relative coordinates, local coordinates,
and `.self` therefore have distinct context requirements. Selector descriptions are shared
with other commands: `.allPlayers { tags := [.include "playing"] }` filters without reading
the caller's executor. Distance and spatial ordering read dimension and any omitted origin
components; supplying X, Y, and Z removes the execution-position requirement.

Conditions filter the current branches. A store registers its receiver at its position in
the chain and receives each body result. Repeated writes follow native overwrite order.
Use Scoreboard explicitly in the body when accumulation is needed.
Receivers include scores, numeric storage/entity/block NBT, and bossbar value/max fields.
NBT stores multiply by their scale before native numeric conversion. Integer tags truncate
toward zero before narrowing; floating-point tags retain fractions. Destination-write errors
follow native callback handling and do not become an Oria body failure.

Conditions reuse item predicates, slot sources, block predicates, and registry descriptions.
The slots condition counts existing slots, including empty ones; items tests their contents.
Loaded checks ENTITY_TICKING chunk status and loaded entities. Relationship steps change the
executor only; positionedOver changes Y while retaining the anchor.
See the [standard library examples](##Oria.Examples.StandardLibrary) for composition.
-/

namespace Oria.Execute

open Oria.Command Oria.Std.Command.Arg

/-- Axes selected for alignment to the block grid. -/
public inductive Axes where
  /-- The X axis. -/
  | x
  /-- The Y axis. -/
  | y
  /-- The Z axis. -/
  | z
  /-- The X and Y axes. -/
  | xy
  /-- The X and Z axes. -/
  | xz
  /-- The Y and Z axes. -/
  | yz
  /-- All three axes. -/
  | xyz

/-- A comparison between two native scores. -/
public inductive Relation where
  /-- Equal. -/
  | eq
  /-- Strictly less than. -/
  | lt
  /-- Less than or equal. -/
  | le
  /-- Strictly greater than. -/
  | gt
  /-- Greater than or equal. -/
  | ge

/-- Native region comparison, including block state and block-entity data. -/
public inductive BlockComparison where
  /-- Compare every source block, including air. -/
  | all
  /-- Ignore air in the source region. -/
  | masked

/-- A native branch condition for when or unless. Conditions filter contexts;
the execution scope determines result handling. -/
public inductive Condition where
  /-- At least one entity matches. -/
  | entity : Selector → Condition
  /-- The score exists and lies within the given range. -/
  | matches : ScoreSlot → Range → Condition
  /-- Two scores satisfy the relation. Missing scores do not satisfy the comparison. -/
  | compare : ScoreSlot → Relation → ScoreSlot → Condition
  /-- The NBT path matches at least one node. A list itself is one node, even when empty. -/
  | data : DataTarget → Nbt.Path Scalar (Nbt.Value .compound) → Condition
  /-- Match a block ID/tag, properties, and optional block-entity NBT. -/
  | block : BlockPos → BlockPredicate → Condition
  /-- Compare an inclusive source region with the region beginning at the destination. -/
  | blocks : BlockBox → BlockPos → BlockComparison → Condition
  /-- Match the position's biome against an ID or biome tag. -/
  | biome : BlockPos → ResourceOrTag → Condition
  /-- Compare the execution dimension. -/
  | dimension : ResourceId → Condition
  /-- Check native full-chunk readiness at the position, without loading the chunk. -/
  | loaded : BlockPos → Condition
  /-- At least one selected slot contains an item satisfying the predicate. -/
  | items : Inventory → ItemPredicate → Condition
  /-- At least one slot exists in the selection; an existing empty slot also counts. -/
  | slots : Inventory → Condition
  /-- Evaluate a named or inline native predicate with its declared context requirements. -/
  | predicate : Predicate → Condition

namespace Condition

/-- Encode a condition and its requirements for use by execution steps.
Applications use the condition constructors. -/
@[expose] public def fragment : Condition → Fragment EncodedVal
  | .entity selector => .spaced [.token "entity", selector.fragment]
  | .matches score range => .spaced [
      .token "score", (encode score).fragment,
      .token "matches", (encode range).fragment]
  | .compare left relation right =>
      let token : SyntaxToken := match relation with
        | .eq => "="
        | .lt => "<"
        | .le => "<="
        | .gt => ">"
        | .ge => ">="
      .spaced [.token "score", (encode left).fragment,
        .token token, (encode right).fragment]
  | .data target path => .spaced [
      .token "data", (encode target).fragment, (encode path).fragment]
  | .block position id => .require Req.dimension <| .spaced [
      .token "block", (encode position).fragment, (encode id).fragment]
  | .blocks box destination mode => .require Req.dimension <| .spaced [
      .token "blocks", (encode box).fragment, (encode destination).fragment,
      .token (match mode with | .all => "all" | .masked => "masked")]
  | .biome position id => .require Req.dimension <| .spaced [
      .token "biome", (encode position).fragment, (encode id).fragment]
  | .dimension id => .require Req.dimension <| .spaced [.token "dimension", (encode id).fragment]
  | .loaded position => .require Req.dimension <| .spaced [.token "loaded", (encode position).fragment]
  | .items inventory item => .require (Req.position ||| Req.dimension) <| .spaced [
      .token "items", (encode inventory).fragment, (encode item).fragment]
  | .slots inventory => .require (Req.position ||| Req.dimension) <| .spaced [
      .token "slots", (encode inventory).fragment]
  | .predicate id => .spaced [
      .token "predicate", (encode id).fragment]

end Condition

/-- An entity relationship followed from the current executor. -/
public inductive EntityRelation where
  /-- Tameable entity owner. -/
  | owner
  /-- Entity holding the leash. -/
  | leasher
  /-- Current attack target. -/
  | target
  /-- Last attacker within the native tracking window. -/
  | attacker
  /-- Vehicle currently carrying the entity. -/
  | vehicle
  /-- Controlling passenger. -/
  | controller
  /-- Source of a projectile, item, or other supported entity. -/
  | origin
  /-- Each direct passenger, producing a branch per passenger. -/
  | passengers

/-- Native heightmap selected by positioned over. -/
public inductive Heightmap where
  /-- Highest non-air block. -/
  | worldSurface
  /-- Highest motion-blocking block or fluid. -/
  | motionBlocking
  /-- Motion-blocking height, excluding leaves. -/
  | motionBlockingNoLeaves
  /-- Highest motion-blocking block, excluding fluids. -/
  | oceanFloor

/-- Numeric bossbar fields accepted by execute store. -/
public inductive BossbarField where
  /-- Current value. -/
  | value
  /-- Maximum value. -/
  | max

/-- Receiver captured at its position in an execution chain. -/
public inductive StoreTarget where
  /-- One score holder and objective. -/
  | score : ScoreSlot → StoreTarget
  /-- Store a scaled native result as a numeric NBT tag. Entity mutation follows data rules.
  The game performs numeric conversion; paths and scale may contain dynamic integer holes. -/
  | nbt : DataTarget → Nbt.Path Scalar (Nbt.Value .compound) → NumericTag → Decimal → StoreTarget
  /-- Write a bossbar's current or maximum value. -/
  | bossbar : ResourceId → BossbarField → StoreTarget

/-- Receiver class determines the store effect bound. -/
@[expose] public def StoreTarget.kind : StoreTarget → StoreKind
  | .score _ => .score
  | .nbt .. => .nbt
  | .bossbar .. => .bossbar

/-- Encode the destination using shared score, NBT path, numeric, and resource codecs. -/
@[expose] public def StoreTarget.fragment : StoreTarget → Fragment EncodedVal
  | .score slot => .spaced [.token "score", (encode slot).fragment]
  | .nbt target path tag scale => .spaced [
      (encode target).fragment, (encode path).fragment, (encode tag).fragment, (encode scale).fragment]
  | .bossbar id field => .spaced [.token "bossbar", (encode id).fragment,
      .token (match field with | .value => "value" | .max => "max")]

namespace Step

/-- Follow a relationship, supplying the related executor and retaining position, rotation,
dimension, and anchor. An absent relationship produces zero branches. -/
@[expose] public def on (relation : EntityRelation) : Step EncodedVal :=
  ⟨.onEntity, .token (match relation with
    | .owner => "owner" | .leasher => "leasher" | .target => "target" | .attacker => "attacker"
    | .vehicle => "vehicle" | .controller => "controller" | .origin => "origin" | .passengers => "passengers")⟩

/-- Spawn an entity at the execution position and make it the executor for following steps.
Position, rotation, dimension, and anchor are retained. Spawn failure ends the branch. -/
@[expose] public def summon (type : ResourceId) : Step EncodedVal :=
  ⟨.summon, (encode type).fragment⟩

/-- Set Y to the native heightmap height at the execution X/Z. Retains the anchor.
An unloaded chunk causes native failure. -/
@[expose] public def positionedOver (heightmap : Heightmap) : Step EncodedVal :=
  ⟨.positionedOver, .token (match heightmap with
    | .worldSurface => "world_surface" | .motionBlocking => "motion_blocking"
    | .motionBlockingNoLeaves => "motion_blocking_no_leaves" | .oceanFloor => "ocean_floor")⟩

/-- Set the command position and supply the feet anchor.
Coordinate arguments read their required context before the transformation. -/
@[expose] public def positioned (position : Vec3) : Step EncodedVal :=
  ⟨.positioned, (encode position).fragment⟩

/-- Use selected entities' positions, retaining executor and anchor.
Multiple matches may produce multiple branches. -/
@[expose] public def positionedAs (selector : Selector) : Step EncodedVal :=
  ⟨.positionedAs, selector.fragment⟩

/-- Set yaw and pitch, supplying rotation context. Relative angles read the original rotation. -/
@[expose] public def rotated (yaw pitch : Angle) : Step EncodedVal :=
  ⟨.rotated, (encode (Rotation.mk yaw pitch)).fragment⟩

/-- Use selected entities' rotations, retaining executor and position.
Multiple matches may produce multiple branches. -/
@[expose] public def rotatedAs (selector : Selector) : Step EncodedVal :=
  ⟨.rotatedAs, selector.fragment⟩

/-- Change dimension using native coordinate-scaling rules.
Reads the original dimension and position, and supplies the new dimension context. -/
@[expose] public def «in» (dimension : ResourceId) : Step EncodedVal :=
  ⟨.inDimension, (encode dimension).fragment⟩

/-- Set the anchor for local-coordinate and facing calculations. -/
@[expose] public def anchored (anchor : Anchor) : Step EncodedVal :=
  ⟨.anchored, (encode anchor).fragment⟩

/-- Floor the selected position axes to the block grid.
Reads position and preserves the remaining context. -/
@[expose] public def align (axes : Axes) : Step EncodedVal :=
  ⟨.align, .token (match axes with
    | .x => "x" | .y => "y" | .z => "z"
    | .xy => "xy" | .xz => "xz" | .yz => "yz"
    | .xyz => "xyz")⟩

/-- Face the given position. Reads position, anchor, executor, and coordinate requirements;
supplies the new rotation. -/
@[expose] public def facing (position : Vec3) : Step EncodedVal :=
  ⟨.facing, (encode position).fragment⟩

/-- Face the selected entities' given anchor, defaulting to their feet.
Reads the original position, anchor, executor, and selector requirements. -/
@[expose] public def facingEntity (selector : Selector) (anchor : Anchor := .feet) : Step EncodedVal :=
  ⟨.facingEntity, .spaced [selector.fragment,
    (encode anchor).fragment]⟩

/-- Continue subsequent steps and the body only for branches satisfying the condition. -/
@[expose] public def when (condition : Condition) : Step EncodedVal :=
  ⟨.ifCondition, condition.fragment⟩

/-- Continue only for branches that do not satisfy the condition,
following Minecraft's handling of condition errors. -/
@[expose] public def «unless» (condition : Condition) : Step EncodedVal :=
  ⟨.unlessCondition, condition.fragment⟩

/-- Register a receiver at this position in the chain for each subsequent body result.
Body failure writes the native failure result. Repeated deliveries overwrite the score;
accumulation must be explicit. -/
@[expose] public def storeResult (target : StoreTarget) : Step EncodedVal :=
  ⟨.storeResult target.kind, target.fragment⟩

/-- Register a receiver at this position, writing 1 for success and 0 for failure.
Retains only the demand for the success component. -/
@[expose] public def storeSuccess (target : StoreTarget) : Step EncodedVal :=
  ⟨.storeSuccess target.kind, target.fragment⟩

end Step

end Oria.Execute
