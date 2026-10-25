module

public import Oria.Std.Command.Arg.Waypoint
import Oria.Std.Command.Declarations.Generation
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Waypoint

The locator bar displays server-tracked waypoint transmitters. Modify changes one
transmitter's icon; its native success result is 0. A transmitter can be modified while its
transmission range is zero. List counts the current dimension's tracked transmitters.

Visibility and range also depend on attributes, game rules, teams, and player state.
Use Attribute for transmission/reception range. A style names a client waypoint-style asset;
providing that asset remains a resource-pack concern.
-/

namespace Oria.Std.Waypoint
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- The current dimension's waypoint manager and the target selector's requirements. -/
@[expose] public def grade (target : Target) : Grade :=
  ⟨Req.dimension ||| target.requirements, Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.hud ||| Eff.failure⟩

/-- Return the number of tracked transmitters in this dimension. An empty list succeeds
with result 0. The command also emits native operator feedback. -/
public def list : Prog ⟨Req.dimension, Eff.world ||| Eff.failure⟩ Int32 := do
  emit <| Command.Declarations.waypointList.call .nil

/-- Change the named/hex color or client style of one transmitter. Returns successful 0,
including repeated assignments. The native parser requires a singular selector.
Missing targets or a non-transmitter entity fail during execution.
The update is constructed at the host stage; target selectors use the shared context model. -/
public def modify (target : Target) (property : WaypointProperty) :
    Prog (grade target) Int32 := do
  emit <| Command.Declarations.waypointModify.call <|
    .cons (encode target) <| .cons (encode property) .nil

end Oria.Std.Waypoint
