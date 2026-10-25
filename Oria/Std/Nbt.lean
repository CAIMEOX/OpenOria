module

public import Oria.Std.Data
public import Oria.Language.TypedNbt
import all Oria.Language.TypedNbt

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Typed native documents

Derive `Nbt.Repr` for a host record to obtain its native representation, codec round-trip
law, and typed field paths. `Nbt.Ref A` owns mutable native contents in the invocation
arena. Lists and scalar fields can be operated on without materializing each element.
Writes retain native data-modification failure: equal assignments and clearing an empty
list fail. Missing compound fields can be created; invalid array indices fail.
`store` publishes a copy to world data. `snapshot` copies a typed selection to an immutable
`Nbt.Data` value. Persisting that snapshot and assigning it to a root retains its contents
across invocations. Arena references remain invocation-local.

`Nbt.Global A` declares a pack-relative storage subtree with a host initial value. Register it
with `Datapack.global`; `Datapack.Spec.settings.ns` supplies its namespace.
The same read, set, length, clear, copy, and snapshot operations
accept arena references and globals through `ToLocation`; copies can cross those address
spaces. Global contents survive entry cleanup and matching-schema reloads. Their fields
also support `let n ← state.count` and `state.count := n + 1` in object do blocks.
These operations retain `memoryRead`/`memoryWrite` effects regardless of storage lifetime.
See `Oria.Examples.GlobalNbt` for a complete declaration and datapack.
-/

namespace Oria.Nbt

open Oria.Std.Command.Arg

private def suffix (p : Path Scalar (Value .compound)) : Command.Fragment EncodedVal :=
  let f := (Command.encode p).fragment
  { f with segments := (match p.head with | .key _ => [.token "."] | _ => []) ++ f.segments }

/-- Measure a selected immutable snapshot without allocating another snapshot. Numbers
return their floor, collections their length, compounds their field count, and strings
their UTF-16 length. Missing or multiple selections fail. -/
public def measure {t : Option Tag} {r : Region} (v : Val (Data t) r)
    (p : Option (Path Scalar (Value .compound)) := none) : Prog .failure Int32 :=
  measureValue v (p.map suffix |>.getD .empty) false

/-- Convert one numeric selection to I32 using native scale-1 semantics. Fractions are
floored. This is a numeric conversion, not an exact tag check. Missing, nonnumeric,
or multiple selections fail. The snapshot remains unchanged and no object is allocated. -/
public def numberAt {t : Option Tag} {r : Region} (v : Val (Data t) r)
    (p : Path Scalar (Value .compound)) : Prog .failure Int32 :=
  measureValue v (suffix p) true

/-- Copy an owned typed selection into external NBT. Equal contents use native Failure.
The destination retains native path semantics; this does not create an alias to the arena.

```lean
open Oria
example (xs : Val (Nbt.Ref (Array Int32))) :=
  Nbt.store xs Nbt.Access.root (.storage "demo:result") (.key "values")
```
-/
public def store {l a b : Type} [r : Repr a] [Repr b] [ToLocation l a r]
    (root : l) (p : Access (Val Int32) a b) (target : DataTarget)
    (destination : Path Scalar (Value .compound)) :
    Prog ⟨target.requirements,
      Eff.memoryRead ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩ Unit := by
  simpa only [Oria.Std.Command.Arg.Nbt.Path.scalar_encode_fragment_requirements,
    DataTarget.encode_fragment_requirements, Req.none, BitVec.or_zero] using
    exportTo (ToLocation.toLocation root) p (Oria.Command.encode target).fragment (Oria.Command.encode destination).fragment

end Oria.Nbt
