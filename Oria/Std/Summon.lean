module

public import Oria.Std.Command.Arg.Nbt
import Oria.Std.Command.Declarations

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Summoning entities

`here` uses the execution position. `at` takes world or local coordinates and optional entity
NBT. Omitting NBT requests native mob spawn initialization; supplying a compound, including
an empty one, loads those fields without that initialization. The entity type comes from the
native registry. These commands return 1 on success, including when NBT contains passengers.
-/

namespace Oria.Std.Summon

open Oria.Std.Command.Arg

/-- Combine the dimension, position, and optional NBT-fragment requirements. Spawning may
change the world and scores and consume randomness. -/
@[expose] public def grade (position : Option Vec3 := none) (data : Option Compound := none) : Grade :=
  ⟨Req.dimension ||| (position.map Vec3.requirements).getD Req.position |||
      (data.map Compound.requirements).getD Req.none,
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.failure⟩

/-- Summon a registered entity at the current position with native spawn initialization.
Return 1 on success. Invalid spawn bounds, disallowed peaceful-mode spawning, or entity
creation failure produce failure. The host resource ID must name a summonable entity type. -/
public def here (entity : ResourceId) : Prog grade Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, Oria.Command.Call.grade, Oria.Command.Call.requirements,
    Oria.Command.Ref.call, Command.Declarations.summonHere, Req.none, BitVec.or_assoc] using
    (Oria.Command.emit <| Command.Declarations.summonHere.call <|
      .cons (Oria.Command.encode entity) .nil)

/-- Summon at an explicit position, optionally loading entity NBT. Return 1 on success;
creation failures, invalid bounds, and duplicate UUIDs produce failure. Omitting NBT performs
native mob initialization; supplying an empty compound retains the explicit-NBT behavior.
Coordinates and compound fields may contain dynamic holes. A runtime compound snapshot
uses Minecraft's native macro serialization. Static syntax is parsed when the function loads.

```lean
open Oria Oria.Std
example := Summon.at "minecraft:marker"
  (.world (.absolute (.decimal 0.5)) (.absolute (.static 64)) (.absolute (.decimal 0.5)))
  (some (.value (nbt% {Tags: ["temporary"]})))
```
-/
public def «at» (entity : ResourceId) (position : Vec3) (data : Option Compound := none) :
    Prog (grade (some position) data) Int32 :=
  match data with
  | none => by
      simpa [Eff.failure, Grade.seq, Grade.failure, grade, Vec3.requirements, Oria.Command.Call.grade, Oria.Command.Call.requirements,
        Oria.Command.Ref.call, Command.Declarations.summonAt, Req.none, BitVec.or_assoc] using
        (Oria.Command.emit <| Command.Declarations.summonAt.call <|
          .cons (Oria.Command.encode entity) <| .cons (Oria.Command.encode position) .nil)
  | some data => by
      simpa [Eff.failure, Grade.seq, Grade.failure, grade, Vec3.requirements, Compound.requirements, Oria.Command.Call.grade,
        Oria.Command.Call.requirements, Oria.Command.Ref.call, Command.Declarations.summonData,
        Req.none, BitVec.or_assoc] using
        (Oria.Command.emit <| Command.Declarations.summonData.call <|
          .cons (Oria.Command.encode entity) <| .cons (Oria.Command.encode position) <|
            .cons (Oria.Command.encode data) .nil)

end Oria.Std.Summon
