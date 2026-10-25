module

public import Oria.Std.Command.Arg.Position
import Oria.Std.Command.Declarations

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Teleportation

`Teleport.to` teleports selected entities to coordinates. `Target` describes the entities and `Vec3` the
destination. Coordinates accept integer literals, decimal literals, host numeric values,
and runtime `Val Int32` expressions. Minecraft interprets them when executing the command.
Absolute X/Z integers use native block centering; a decimal point retains the exact position,
so `Vec3.absolute 1 64 1` and `Vec3.absolute 1.0 64 1.0` denote different destinations.

`Target.self` requires an executor. Relative coordinates read the current position; local
coordinates also read rotation and anchor. `Teleport.grade` computes these requirements,
which an enclosing Execute scope can supply. The command returns `Int32`; see the
[standard library guide](##Oria.Std) for composition rules.

An optional `RotationAction` selects explicit angles, facing a position, or facing one entity.
`Teleport.entity` copies a destination entity's position, rotation, and dimension. Native
target cardinality is checked by Minecraft: the moved set may be plural, while an entity
destination or facing entity must be singular. The result counts teleported entities.
-/

namespace Oria.Std.Teleport

open Oria.Std.Command.Arg

/-- Combine the target and coordinate requirements with the teleport effect bound.
The current dimension is always required. {name}`Oria.Eff.world`,
{name}`Oria.Eff.scoreboardRead`, and {name}`Oria.Eff.random` form the library's
conservative effect bound. -/
@[expose] public def grade (target : Target) (position : Vec3)
    (orientation : Option RotationAction := none) : Grade :=
  ⟨Req.dimension ||| target.requirements ||| position.requirements |||
      (orientation.map RotationAction.requirements).getD Req.none,
    Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩

/--
Teleport entities to the given coordinates. The success payload counts teleported entities. Execution fails if
the target is absent or the game rejects the destination. The target Minecraft version
enforces selector cardinality and coordinate parsing. All local components use {lit}`^`;
world coordinates may choose absolute or relative form independently for each component.

Static components appear directly in the command. Dynamic components use function macros.

```lean
open Oria Oria.Std Oria.Std.Command.Arg
example (x : Val Int32) :=
  Teleport.to .self (Vec3.absolute x 64.25 0.0)
example (x : Val Int32) :=
  Teleport.to .self (.world (.absolute x) (.absolute 64.25) (.relative (-0.5)))
```
-/
public def to (target : Target) (position : Vec3) (orientation : Option RotationAction := none) :
    Prog (grade target position orientation) Int32 := by
  cases orientation with
  | none =>
    simpa [Eff.failure, Grade.seq, Grade.failure, grade, Target.requirements, Vec3.requirements, Oria.Command.Call.grade,
      Oria.Command.Call.requirements, Oria.Command.Ref.call,
      Command.Declarations.teleport, Req.none, BitVec.or_assoc] using
      (Oria.Command.emit <| Command.Declarations.teleport.call <|
        .cons (Oria.Command.encode target) <| .cons (Oria.Command.encode position) .nil)
  | some rotation =>
    simpa [Eff.failure, Grade.seq, Grade.failure, grade, Target.requirements, Vec3.requirements, RotationAction.requirements,
      Oria.Command.Call.grade, Oria.Command.Call.requirements, Oria.Command.Ref.call,
      Command.Declarations.teleportOriented, Req.none, BitVec.or_assoc] using
      (Oria.Command.emit <| Command.Declarations.teleportOriented.call <|
        .cons (Oria.Command.encode target) <| .cons (Oria.Command.encode position) <|
        .cons (Oria.Command.encode rotation) .nil)

/-- Entity-to-entity teleportation only reads the two selectors' context requirements. -/
@[expose] public def entityGrade (target destination : Target) : Grade :=
  ⟨target.requirements ||| destination.requirements,
    Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩

/-- Copy one entity's position, rotation, and dimension to the selected targets.
Returns the teleported count. An absent or plural destination fails. -/
public def entity (target destination : Target) :
    Prog (entityGrade target destination) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, entityGrade, Target.requirements, Oria.Command.Call.grade,
    Oria.Command.Call.requirements, Oria.Command.Ref.call,
    Command.Declarations.teleportEntity, Req.none] using
    (Oria.Command.emit <| Command.Declarations.teleportEntity.call <|
      .cons (Oria.Command.encode target) <| .cons (Oria.Command.encode destination) .nil)

end Oria.Std.Teleport
