module

public import Oria.Std.Command.Arg.Control
import Oria.Std.Command.Declarations.Control
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Ride

Mount and dismount operate on one entity at a time. Native rules reject riding cycles,
ineligible vehicles, cross-dimension mounting, already-mounted riders, and dismounting
an entity without a vehicle. Successful results are 1.
-/

namespace Oria.Std.Ride
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Selection requirements and riding effects. -/
@[expose] public def grade (rider : Target) (vehicle : Option Target := none) : Grade :=
  ⟨rider.requirements ||| (vehicle.map Target.requirements).getD Req.none,
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.failure⟩

/-- Mount the rider on a native vehicle. Both selections must identify one entity. -/
public def mount (rider vehicle : Target) : Prog (grade rider (some vehicle)) Int32 := do
  emit <| Command.Declarations.rideMount.call <|
    .cons (encode rider) <| .cons (encode vehicle) <| .nil

/-- Dismount one rider, failing when it has no vehicle. -/
public def dismount (rider : Target := .self) : Prog (grade rider) Int32 := do
  emit <| Command.Declarations.rideDismount.call <|
    .cons (encode rider) <| .nil

end Oria.Std.Ride
