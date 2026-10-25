module

public import Oria.Std.Command.Arg.Data
public import Oria.Language.Nbt
import all Oria.Language.Nbt
import Oria.Std.Command.Declarations

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Game NBT and immutable snapshots

`get` and `getScaled` return I32 measurements. `readOne` and `readAll` copy complete selected
NBT values into the invocation arena as `Nbt.Data`. Snapshots can cross function boundaries,
be stored in ADTs, or be explicitly persisted. `write` copies a snapshot back into game data.

Targets may be storage, a single entity, or a block. Use application-owned resource names
for user data. The compiler namespace's `runtime` and `persistent` storages hold language
runtime state. Each path segment applies to all current matches: `tasks[{owner:"Ada"}].n`
selects the n field of every matching task. `tasks` selects one list value; `tasks[]` selects
its elements.

Minecraft parses static paths when loading functions. Paths with dynamic indices are parsed
at macro invocation. See the [standard library guide](##Oria.Std) for error handling,
context requirements, and static versus dynamic values.
-/

namespace Oria.Std.Data

open Oria.Std.Command.Arg

/-- Effect bound for game NBT operations, combining target and extra argument requirements.
Declarations conservatively include world, scoreboard-reading, and random effects;
an individual operation may use only a subset. -/
@[expose] public def grade (target : DataTarget) (extraReq : ReqRow := Req.none) : Grade :=
  ⟨target.requirements ||| extraReq, Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩

/--
Read a native I32 measurement. Omitting the path reads the target's root compound and
returns 1 on success. A supplied path must select exactly one value: numbers are rounded
down, collections return their length, compounds their field count, and strings their
UTF-16 length. Zero or multiple matches fail. An empty list is one valid match and returns 0.
Use readOne to read the complete value.

```lean
open Oria Oria.Std Oria.Std.Command.Arg
example := Data.get (.storage "demo:state") (some (.key "points"))
```
-/
public def get (target : DataTarget) (path : Option (Nbt.Path Scalar (Nbt.Value .compound)) := none) :
    Prog (grade target) Int32 :=
  match path with
  | none => by
      simpa [Eff.failure, Grade.seq, Grade.failure, grade, DataTarget.requirements, Oria.Command.Call.grade,
        Oria.Command.Call.requirements, Oria.Command.Ref.call,
        Command.Declarations.dataGet, Req.none] using
        (Oria.Command.emit <| Command.Declarations.dataGet.call <|
          .cons (Oria.Command.encode target) .nil)
  | some path => by
      simpa [Eff.failure, Grade.seq, Grade.failure, grade, DataTarget.requirements, Oria.Command.Call.grade,
        Oria.Command.Call.requirements, Oria.Command.Ref.call,
        Command.Declarations.dataGetPath, Req.none] using
        (Oria.Command.emit <| Command.Declarations.dataGetPath.call <|
          .cons (Oria.Command.encode target) <| .cons (Oria.Command.encode path) .nil)

/-- Read a unique numeric tag, multiply by the construction-time scale, and round down to
the native I32 result. Non-numeric values, zero matches, and multiple matches fail.
The scale is encoded as a Double argument and must be finite. -/
public def getScaled (target : DataTarget) (path : Nbt.Path Scalar (Nbt.Value .compound)) (scale : Float) :
    Prog (grade target) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, DataTarget.requirements, Oria.Command.Call.grade,
    Oria.Command.Call.requirements, Oria.Command.Ref.call,
    Command.Declarations.dataGetScaled, Req.none] using
    (Oria.Command.emit <| Command.Declarations.dataGetScaled.call <|
      .cons (Oria.Command.encode target) <| .cons (Oria.Command.encode path) <|
        .cons (Oria.Command.encode scale) .nil)

/-- Merge a host compound into the target's root compound, returning 1 on success.
Fails if the target cannot be modified or the merge leaves it unchanged. The compound
is supplied at construction time; use modify or write for dynamic values. -/
public def merge (target : DataTarget) (value : Nbt.Value .compound) :
    Prog (grade target) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, DataTarget.requirements, Oria.Command.Call.grade,
    Oria.Command.Call.requirements, Oria.Command.Ref.call,
    Command.Declarations.dataMerge, Req.none] using
    (Oria.Command.emit <| Command.Declarations.dataMerge.call <|
      .cons (Oria.Command.encode target) <|
        .cons (Oria.Command.encode (⟨.compound, value⟩ : Nbt.Any)) .nil)

/-- Remove the selected nodes and return the removal count. Fails if no nodes are removed
or the target cannot be modified. -/
public def remove (target : DataTarget) (path : Nbt.Path Scalar (Nbt.Value .compound)) :
    Prog (grade target) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, DataTarget.requirements, Oria.Command.Call.grade,
    Oria.Command.Call.requirements, Oria.Command.Ref.call,
    Command.Declarations.dataRemove, Req.none] using
    (Oria.Command.emit <| Command.Declarations.dataRemove.call <|
      .cons (Oria.Command.encode target) <| .cons (Oria.Command.encode path) .nil)

/--
Perform a native NBT modification using a value, existing NBT, string slice, or number
provider as the source. Returns the number of changed target nodes on success. An empty
source selection, an unchanged target, or an unsupported target operation causes failure.
An integer compute source uses Minecraft's defaulting provider evaluation: arithmetic
errors produce an IntTag zero, after which the usual changed-target rule applies.
`Compute.run` instead exposes provider arithmetic errors as Failure.

For multiple matches from {name}`Oria.Std.Command.Arg.DataSource.from`, set uses the last
value. List insertion operations copy all source matches in selection order.
Use readOne when uniqueness must be checked.

```lean
open Oria Oria.Std Oria.Std.Command.Arg
example (n : Val Int32) := Data.modify (.storage "demo:state") (.key "points")
  .set (.value (.hole .i32 n))
```
-/
public def modify (target : DataTarget) (path : Nbt.Path Scalar (Nbt.Value .compound)) (op : DataOp) (source : DataSource) :
    Prog (grade target source.requirements) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, DataTarget.requirements, DataSource.requirements, Oria.Command.Call.grade,
    Oria.Command.Call.requirements, Oria.Command.Ref.call,
    Command.Declarations.dataModify, Req.none] using
    (Oria.Command.emit <| Command.Declarations.dataModify.call <|
      .cons (Oria.Command.encode target) <| .cons (Oria.Command.encode path) <|
      .cons (Oria.Command.encode op) <| .cons (Oria.Command.encode source) .nil)

/-- Copy exactly one complete NBT value into an immutable snapshot. Zero or multiple
matches fail. A whole list counts as one value; omitting the path copies the root compound.
Snapshots preserve native tags and can cross function and ADT boundaries. To retain one
across invocations, explicitly persist it and write it to a persistent root. -/
public def readOne (target : DataTarget)
    (path : Option (Nbt.Path Scalar (Nbt.Value .compound)) := none) :
    Prog (grade target) Nbt.Data := by
  let program := Nbt.readExternal .one (Oria.Command.encode target).fragment
      (path.map fun path => (Oria.Command.encode path).fragment)
  cases path <;> simpa [Eff.failure, Grade.seq, Grade.failure, Nbt.externalGrade, grade, IR.Nbt.ReadMode.tag, Req.none] using program

/--
Copy all matches into a native NBT list in selection order. No matches yields a successful
empty list; target-access, macro-parsing, and copy errors still fail. Each matched value
retains its nested structure, so selecting one list produces an outer list containing it.

```lean
open Oria Oria.Std Oria.Std.Command.Arg
example :=
  let path := (Nbt.Path.key "tasks").matching (nbt% {owner: "Ada"})
  Data.readAll (.storage "demo:state") (some (path.field "n"))
```
-/
public def readAll (target : DataTarget)
    (path : Option (Nbt.Path Scalar (Nbt.Value .compound)) := none) :
    Prog (grade target) (Nbt.Data (some .list)) := by
  let program := Nbt.readExternal .all (Oria.Command.encode target).fragment
      (path.map fun path => (Oria.Command.encode path).fragment)
  cases path <;> simpa [Eff.failure, Grade.seq, Grade.failure, Nbt.externalGrade, grade, IR.Nbt.ReadMode.tag, Req.none] using program

/-- Copy an ephemeral or persistent NBT snapshot to a game path, preserving its tags,
values, and contents. Returns the number of changed targets on success; unchanged contents
follow native modification-failure semantics. Uses native copying without macro stringification. -/
public def write {t : Option Nbt.Tag} {r : Region} (target : DataTarget)
    (path : Nbt.Path Scalar (Nbt.Value .compound)) (value : Val (Nbt.Data t) r) :
    Prog (grade target) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, Nbt.externalGrade, grade, Req.none] using
    Nbt.writeExternal (Oria.Command.encode target).fragment (Oria.Command.encode path).fragment value

end Oria.Std.Data

namespace Oria.Nbt

open Oria.Std.Command.Arg

private def suffix (path : Path Scalar (Value .compound)) : Command.Fragment EncodedVal :=
  let fragment := (Command.encode path).fragment
  { fragment with segments := (match path.head with | .key _ => [.token "."] | _ => []) ++ fragment.segments }

/-- Copy a unique match from an ephemeral or persistent NBT value. Zero or multiple
matches fail; omitting the path copies the whole value. The snapshot belongs to the
current invocation arena, and the source remains unchanged. -/
public def readOne {t : Option Tag} {r : Region} (value : Val (Data t) r)
    (path : Option (Path Scalar (Value .compound)) := none) : Prog .failure Data := by
  let program := readValue .one value (path.map suffix)
  cases path <;> simpa [Eff.failure, Grade.seq, Grade.failure, suffix, IR.Nbt.ReadMode.tag, Req.none, Eff.none, Grade.pure] using program

/-- Collect selected nodes from an immutable NBT value into a new list. No matches yields
a successful empty list. Omitting the path makes the whole source value one list element.
The snapshot belongs to the current invocation arena. -/
public def readAll {t : Option Tag} {r : Region} (value : Val (Data t) r)
    (path : Option (Path Scalar (Value .compound)) := none) :
    Prog .failure (Data (some .list)) := by
  let program := readValue .all value (path.map suffix)
  cases path <;> simpa [Eff.failure, Grade.seq, Grade.failure, suffix, IR.Nbt.ReadMode.tag, Req.none, Eff.none, Grade.pure] using program

end Oria.Nbt
