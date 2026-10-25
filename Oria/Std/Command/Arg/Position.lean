module

public import Oria.Std.Command.Arg

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Position and rotation arguments

World block coordinates use integers. Local block offsets use the existing decimal codec
and Minecraft floors their resolved position. Rotation is ordered yaw then pitch. These
host descriptions preserve the context requirements of every relative or local component.
-/

namespace Oria.Std.Command.Arg
open Oria.Command (encode)

/-- Entity anchor shared by Execute and rotation commands. -/
public inductive Anchor where
  /-- Feet. -/
  | feet
  /-- Eyes. -/
  | eyes
  deriving BEq, DecidableEq, Repr

public instance : Oria.Command.ArgCodec Anchor where
  key := ⟨`minecraft.argument.anchor⟩
  encode a := .token (match a with | .feet => "feet" | .eyes => "eyes")

/-- A rotation component in degrees. -/
public inductive Angle where
  /-- Absolute angle. -/
  | absolute : Decimal → Angle
  /-- Offset from the execution rotation. -/
  | relative : Decimal → Angle

public instance : Oria.Command.ArgCodec Angle where
  key := ⟨`minecraft.argument.angle⟩
  encode
    | .absolute n => (encode n).fragment
    | .relative n => .require Req.rotation (.prepend "~" (encode n).fragment)

/-- Yaw and pitch, in native argument order. -/
public structure Rotation where
  /-- Horizontal rotation in degrees. -/
  yaw : Angle
  /-- Vertical rotation in degrees. -/
  pitch : Angle

public instance : Oria.Command.ArgCodec Rotation where
  key := ⟨`minecraft.argument.rotation⟩
  encode r := .spaced [(encode r.yaw).fragment, (encode r.pitch).fragment]

/-- Integer world-block coordinate. -/
public inductive BlockCoord where
  /-- Absolute block coordinate. -/
  | absolute : Scalar → BlockCoord
  /-- Integer offset from the execution position. -/
  | relative : Scalar → BlockCoord

public instance : Oria.Command.ArgCodec BlockCoord where
  key := ⟨`minecraft.argument.block_coord⟩
  encode
    | .absolute n => (encode n).fragment
    | .relative n => .require Req.position (.prepend "~" (encode n).fragment)

/-- Block position with integer world coordinates or fractional local offsets. -/
public inductive BlockPos where
  /-- World coordinates, each absolute or relative. -/
  | world : BlockCoord → BlockCoord → BlockCoord → BlockPos
  /-- Local left, up, and forward offsets. -/
  | local : Decimal → Decimal → Decimal → BlockPos

/-- Absolute world-block coordinates. Integer literals, host I32 values, and runtime
I32 expressions use the same component interface. -/
@[expose] public def BlockPos.absolute (x y z : Scalar) : BlockPos :=
  .world (.absolute x) (.absolute y) (.absolute z)

/-- Integer world-block offsets from the execution position. -/
@[expose] public def BlockPos.relative (x y z : Scalar) : BlockPos :=
  .world (.relative x) (.relative y) (.relative z)

/-- The execution position, resolved to block coordinates by Minecraft. -/
@[expose] public def BlockPos.here : BlockPos :=
  .relative 0 0 0

public instance : Oria.Command.ArgCodec BlockPos where
  key := ⟨`minecraft.argument.block_pos⟩
  encode
    | .world x y z => .spaced [(encode x).fragment, (encode y).fragment, (encode z).fragment]
    | .local x y z => (encode (Vec3.local x y z)).fragment

/-- X/Z block coordinates; the receiving command resolves the containing chunk. -/
public structure ColumnPos where
  /-- X block coordinate. -/
  x : BlockCoord
  /-- Z block coordinate. -/
  z : BlockCoord

public instance : Oria.Command.ArgCodec ColumnPos where
  key := ⟨`minecraft.argument.column_pos⟩
  encode p := .spaced [(encode p.x).fragment, (encode p.z).fragment]

/-- Position and optional rotation used by player and world spawn commands. -/
public inductive SpawnLocation where
  /-- Current execution position with native zero yaw and pitch. -/
  | here
  /-- Explicit position; omitted rotation uses zero yaw and pitch. -/
  | atPos : BlockPos → Option Rotation → SpawnLocation

public instance : Oria.Command.ArgCodec SpawnLocation where
  key := ⟨`minecraft.argument.spawn_location⟩
  encode
    | .here => .require Req.position .empty
    | .atPos p r => .spaced ((encode p).fragment :: r.toList.map (fun r => (encode r).fragment))

/-- Requirements read while resolving a spawn location. -/
@[expose] public def SpawnLocation.requirements (p : SpawnLocation) : ReqRow :=
  (encode p).requirements

/-- Rotation assignment or facing operation for one entity. -/
public inductive RotationAction where
  /-- Set explicit yaw and pitch. -/
  | angles : Rotation → RotationAction
  /-- Face a point using the execution anchor on the rotated entity. -/
  | facing : Vec3 → RotationAction
  /-- Face an entity's given anchor. -/
  | entity : Target → Anchor → RotationAction

public instance : Oria.Command.ArgCodec RotationAction where
  key := ⟨`minecraft.argument.rotation_action⟩
  encode
    | .angles r => (encode r).fragment
    | .facing p => .require Req.anchor (.spaced [.token "facing", (encode p).fragment])
    | .entity t a => .require Req.anchor
        (.spaced [.token "facing", .token "entity", (encode t).fragment, (encode a).fragment])

/-- Context used by angles, facing coordinates, and entity selection. -/
@[expose] public def RotationAction.requirements (r : RotationAction) : ReqRow :=
  (encode r).requirements

end Oria.Std.Command.Arg
