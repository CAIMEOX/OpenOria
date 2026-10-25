module

public import Oria.Std.Command.Arg.Management
public import Oria.Std.Command.Arg.Color

set_option doc.verso true
set_option linter.missingDocs true

namespace Oria.Std.Command.Arg
open Oria.Command (encode)

/-- A waypoint icon update. The receiving command selects one native transmitter. -/
public inductive WaypointProperty where
  /-- Set a named color, or restore the automatic color with none. -/
  | color : Option TeamColor → WaypointProperty
  /-- Set a three- or six-digit host RGB color. -/
  | hex : HexColor → WaypointProperty
  /-- Set a client waypoint-style asset, or restore the default style with none. -/
  | style : Option ResourceId → WaypointProperty

public instance : Oria.Command.ArgCodec WaypointProperty where
  key := ⟨`minecraft.argument.waypoint_property⟩
  encode p :=
    let f : Oria.Command.Fragment EncodedVal := match p with
      | .color none => .spaced [.token "color", .token "reset"]
      | .color (some c) => .spaced [.token "color", (encode c).fragment]
      | .hex c => .spaced [.token "color", .token "hex", (encode c).fragment]
      | .style none => .spaced [.token "style", .token "reset"]
      | .style (some id) => .spaced [.token "style", .token "set", (encode id).fragment]
    ⟨f.segments, Req.none⟩

@[simp] public theorem WaypointProperty.encode_requirements (p : WaypointProperty) :
    (encode p).requirements = Req.none := rfl

@[simp] public theorem WaypointProperty.encode_fragment_requirements (p : WaypointProperty) :
    (encode p).fragment.requirements = Req.none := rfl

end Oria.Std.Command.Arg
