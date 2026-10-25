# NBT values, paths, and transport

`Oria.Nbt` provides host NBT data, typed conversion, construction syntax, and SNBT output.
Import it with `import Oria.Nbt`.
`Nbt.Value t` is host data; `Val (Nbt.Data t)` describes an immutable Minecraft runtime value.
The compiler's memory construction and NumberProvider formatting reuse this module.

## Host construction

```lean
import Oria.Nbt
open Oria

def document (n : Int32) (text : String) : Nbt.Value .compound :=
  nbt% {
    text: $(text), count: $(n), enabled: true,
    offsets: [L; 1, 3], extra: [1, "two", {nested: false}]
  }
```

`nbt%` expands to ordinary Lean constructors, so the resulting host value supports
constructor matching. Numbers and strings use Lean's parsers.
Field names can be identifiers or quoted strings. This syntax constructs Lean source values;
it is not an external SNBT-file parser.

| Syntax | Host payload | Tag |
| --- | --- | --- |
| `127b`, `true`, `false` | Int8 | byte |
| `32767s` | Int16 | short |
| `42`, `42i` | Int32 | int |
| `42L` | Int64 | long |
| `1.25f` | Float32 | float |
| `1.25`, `1.25d` | Float | double |
| `"hello"` | String | string |
| `[B; 1, 2b]` | Array Int8 | byte array |
| `[I; 1, 2]` | Array Int32 | int array |
| `[L; 1, 2L]` | Array Int64 | long array |

Integer literals are range-checked and float literals must be finite.
Unsuffixed array integers use the array's element width; explicit suffixes cannot exceed it.
For example, `[B; 128]` and `[I; 1L]` produce diagnostics.

Ordinary lists can mix tags. This follows the SNBT interface introduced in
[Minecraft 1.21.5](https://www.minecraft.net/en-us/article/minecraft-java-edition-1-21-5).
Minecraft handles the corresponding binary-list wrappers.

## Host interpolation

`$(e)` uses the open `Nbt.ToNbt` class.
Instances cover fixed-width numbers, Bool, String, NBT, List, and Array.
Ordinary collections encode as lists; integer-array constructors preserve array tags.

```lean
def frame (n : Nat) : Nbt.Value .compound :=
  nbt% {locals: $(Array.replicate n (0 : Int32)), saved: []}

def longs (x : Int64) : Nbt.Value .longArray :=
  nbt% [L; $(x), 3]
```

An interpolated integer-array element must have the array's element type.
Unbounded Nat/Int inputs need an explicit width conversion.
Interpolation preserves Lean binding hygiene and executes at the host construction stage.
`Val Int32` has no host ToNbt instance; runtime conversion uses `Nbt.ofI32`.

NumberProvider descriptions can be encoded to NBT and embedded in larger host documents.
`Nbt.Any` is a dependent pair of tag and value, allowing the same interface to carry
scalars, references, and compound descriptions.

## Typed codecs

```lean
structure PlayerInfo where
  name : String
  points : Int32
  active : Bool
  deriving Nbt.ToNbt, Nbt.FromNbt

def save (player : PlayerInfo) : Nbt.Any :=
  Nbt.ToNbt.toNbt player

def load (raw : Nbt.Any) : Except Nbt.DecodeError PlayerInfo :=
  Nbt.FromNbt.fromNbt raw
```

`save ⟨"Alex", 12, true⟩` produces `{name:"Alex",points:12,active:1b}`.
Derived values can be interpolated into `nbt%`.

| Source type | Encoding |
| --- | --- |
| Structure | Named compound fields; inherited fields are flattened |
| Payload-free enum | Short constructor-name string |
| Payload ADT | One-key compound from short constructor name to payload list |
| List / Array | NBT list |
| Option | `{none:[]}` or `{some:[value]}` |
| Unit | Empty compound |

For a payload datatype State, idle and playing 1 2 encode as `{idle:[]}` and
`{playing:[1,2]}`. Nested Option retains each constructor layer.
An `Nbt.Value .intArray` field preserves its tag; `Array Int32` encodes a list.

Decoding checks tags and payload lengths. Bool accepts only byte 0 or 1.
Record field order is arbitrary, extra fields are ignored, and missing fields fail.
Lean field defaults do not supply missing input fields.
Repeated compound keys use the last value.
ADT decoding requires one constructor key and the correct payload count.

`DecodeError` carries a field/index path and a reason. Its Std.Format printer produces,
for example, `$."players"[2]."points": expected int, got long`.
Record decoding builds a standard HashMap once and uses Except composition.

Deriving supports nonrecursive, unindexed types whose fields do not depend on earlier fields,
including empty types and inherited structures. Type parameters use their corresponding codec
instances. Proof-carrying or validation-dependent data needs a custom instance.
NBT deriving and Oria.Object deriving serve different host/object interfaces.

## Codec laws

`Oria.Nbt.Lemmas` proves round-trip laws for base types and compositional laws for containers:

```lean
example (xs : List Int32) :
    Nbt.FromNbt.fromNbt (Nbt.ToNbt.toNbt xs) = Except.ok xs :=
  Nbt.from_to_list Nbt.from_to_int32 xs
```

Container laws assume the element law.
Derived-type examples are in [Nbt.Laws](../Oria/Proofs/Nbt/Laws.lean).
Cross-module proofs can use `deriving @[expose] Nbt.ToNbt, @[expose] Nbt.FromNbt`.

These laws describe NBT trees. They do not claim preservation of input field ordering,
extra fields, repeated keys, or arbitrary text formatting.
Constructor short names must be unique within a derived encoding.

## Typed native documents

Use `deriving Nbt.Repr` when a Lean data definition should also describe a mutable native
document. It generates the host codecs, a finite schema, a kernel-checked codec round-trip
proof, and typed field selections under the type's `Nbt` namespace. Import `Oria` for the
runtime operations and its deriving handler.

```lean
structure Work where
  input : Array Int32
  output : Array Int32
  deriving Nbt.Repr

@[mcfunction]
def edit := show Prog _ Unit from do
  let work ← Nbt.alloc (Work.mk #[3, 1, 2] #[])
  let x ← work.input[0]
  Nbt.append work Work.Nbt.output (.i32 (x + 1))
  Nbt.clear work Work.Nbt.input
  Nbt.store work Work.Nbt.output (.storage "example:result") (.key "values")
```

`Nbt.Ref A` is a mutable, invocation-local handle. Ordinary function calls can pass and
alias it; updates are visible through those aliases. Its data lives in one native arena
object. A cooperative task retains that arena across ticks and releases it on completion,
failure, or cancellation. `persist` rejects mutable native references, including references
nested in object types.

`Nbt.Access i A B` selects a value of type B inside A. Generated field paths compose with
`p.then q`; `.at i` selects an Array element. At runtime the index carrier is `Val Int32`.
Paths are singular and retain their root type. An out-of-range index fails, including native
negative indices outside the list's range. Writes require the selected location to exist.

Arrow bindings and assignments also accept `let x ← work.input[i]` and
`work.input[i] := x + 1`. Reads produce I32, while writes accept host values of the selected
type and object I32 expressions. Other native operations use the explicit typed paths.
The [elaboration guide](elaboration.md#typed-native-access-and-assignment) specifies the
dispatch rules, index conversions, and failure behavior.

| Operation | Contract |
| --- | --- |
| `alloc hostValue` | Materialize one typed document |
| `readI32 ref path` | Read an Int32 field directly into a scalar location |
| `length ref path` | Measure an Array without copying it |
| `snapshot ref path` | Copy one selection into an immutable runtime NBT value |
| `set ref path source` | Replace one value of the selected type |
| `append ref path source` | Append one element of the Array's element type |
| `clear ref path` | Empty an Array while preserving its location |
| `copy dst p src q` | Copy equal-typed selections, preserving native contents |
| `appendFrom dst p src q` | Copy one selected element into an Array |
| `store ref path target destination` | Publish a native copy to external data |

Write sources are `.literal hostValue` and `.i32 runtimeValue`. Native copies handle whole
records, variants, strings, and wide numeric fields without routing their contents through
scoreboard arithmetic. Set, copy, clear, and publication retain native `data modify`
results: unchanged contents fail. Missing compound keys can be created; invalid list
indices fail. Use `.ignore` where continuing after an unchanged write is intended.
Reads carry `memoryRead`; writes carry `memoryWrite`;
external publication also carries the standard Data world effect bound.

The compiler retains typed field/index paths through Cont and Machine. Within a lexical
continuation, a successful read or write can supply a later scalar read and establish
selection existence for later reads. Aliasing writes and list resizing invalidate the
affected facts. Different function parameters may refer to the same document. Calls and
join bodies delimit the current analysis; they preserve the ordinary read/write semantics.
See [owned-document memory optimization](optimization.md#owned-document-memory-facts).

I32 write sources follow their physical location. Constants use `set value`, stack words
use `set from`, and registers use `set compute default integer` with a fixed score provider.
The initialized register is read directly; its value need not pass through a temporary NBT
field. The source is read before the operation's success flag is published.

Standalone `Compute.run` and native data-compute sources have distinct evaluation rules
in the pinned server. Standalone integer compute reports division and overflow errors as
Failure. A data-compute integer source substitutes zero for those arithmetic errors, then
performs the modification and reports whether it changed the target. These operations
remain explicit in source. Register-backed typed writes use only an initialized score leaf.

Repr deriving supports nonrecursive records, flattened inherited fields, enums, payload
variants, and type parameters with Repr instances. Array, List, Option, primitive numbers,
String, Bool, Unit, and `Nbt.Value tag` have built-in instances. Runtime element operations use Array as the
host description of a native mutable list. Recursive, indexed, and dependent definitions
require a further representation design. Binding schemas to source types and constructing
field-path evidence are confined to the trusted deriving implementation.

Host codec proofs concern NBT trees, not validation of arbitrary game data at runtime.
`Nbt.Data` below remains the immutable representation for foreign snapshots. `Nbt.measure`
and `Nbt.numberAt` inspect those snapshots without making per-selection copies; `numberAt`
explicitly performs Minecraft's scale-1 numeric conversion. It is not an exact IntTag check.
The [merge-sort example](merge-sort.md) snapshots external input, converts its numeric
elements into typed buffers, and uses typed operations throughout the sorting loops.

## Global native documents

`Nbt.Global A` describes an owned subtree in command storage, using the same `Nbt.Repr A`
as an arena document. Its storage name and path are construction-time data; `Spec.settings.ns`
supplies the namespace during target lowering. Its contents are mutable runtime NBT.
The [checked example](../Oria/Examples/GlobalNbt.lean) includes a complete pack:

```lean
structure State where
  count : Int32
  values : Array Int32
  label : String
  deriving Nbt.Repr

def state : Nbt.Global State :=
  Nbt.Global.init "state" (.key "buffer")
    ⟨0, #[10, 20], "initial"⟩

@[mcfunction]
def increment := show Prog _ Unit from do
  let n ← state.count
  state.count := n + 1
  state.label := "updated"

@[datapack]
def game : Datapack.Spec := Datapack.build {ns := "global_demo"} do
  Datapack.global state
  Datapack.entry "increment" increment.ref
```

Declare the initial value in the host language. The root path is a nonempty sequence of
compound fields; keys reuse the NBT path encoder and validation. Runtime array indices
belong to the selected access, such as `state.values[i]`. Storage names use the canonical
`Datapack.ResourcePath` type, so `"state"` denotes `global_demo:state` in this pack. Changing
only the Spec's namespace relocates the global accesses in the same source functions,
including task bodies. The compiler's `runtime` and `persistent` storages are reserved.

Registration checks that every used global has the declared address and schema. Two
registered roots in one storage must have disjoint paths: independent initialization of
a parent and its child would give conflicting ownership. Select nested fields through
typed access paths under their registered root.

The operations `readI32`, `length`, `set`, `append`, `clear`, `copy`, `appendFrom`, `snapshot`,
and `store` accept both globals and arena references. The receiver determines its content
type through `ToLocation`. Whole-document paths infer that type from the receiver:

```lean
let tmp ← Nbt.alloc (State.mk 0 #[] "scratch")
Nbt.copy tmp Nbt.Access.root state Nbt.Access.root
tmp.values[0] := 42
Nbt.copy state Nbt.Access.root tmp Nbt.Access.root
```

Copying native contents into storage needs no `persist`. A snapshot is an immutable arena
value and can be persisted separately. Globals hold native trees rather than Oria heap
edges; they are outside the managed collector. Removing a declaration or collecting the
Oria heap does not delete its storage subtree. The global handle itself is host data;
object function parameters continue to use the existing value ABI.

First load initializes the declared subtrees and publishes their canonical schema manifest
after initialization succeeds. It replaces initial contents inside those owned subtrees;
data outside them is preserved. Reloading a matching manifest retains current values and
checks that the roots still exist. The manifest includes storage, path, and native schema,
and excludes initializer values and registration order. A mismatch or missing initialized
root leaves readiness unset, blocks public entries, and preserves the existing data for
inspection. Migration and reset are explicit deployment operations.

All writers to an owned subtree must preserve its declared schema. Raw Data operations and
other datapacks can bypass typed operations; arbitrary foreign paths therefore retain the
explicit, fallible Data interface. Registration is an ownership contract, not a validator
for arbitrary existing game data. Compiler metadata under `<namespace>:persistent globals`
belongs to the runtime.

Cont identifies globals by pack-relative storage and complete structural path. Prefix overlap invalidates
facts about descendants; calls, external commands, and task checkpoints end cached memory
facts. A task can observe changes made by another entry while it is parked. Fixed addresses
need no arena-pointer decode; dynamic indices use the existing macro transport. The scalar
global artifact has neither arena allocation nor macro calls.

## Runtime snapshots

`Nbt.Data` has an optional known-tag index. `none` denotes unclassified native NBT;
`some .string` and other tags record known representations.
An unknown tag remains a closed object type with a fixed pointer layout.

| Operation | Behavior |
| --- | --- |
| `Nbt.literal value` | Materialize host NBT, retaining its tag |
| `Nbt.ofI32 value` | Materialize an object I32 as native IntTag |
| `Nbt.forget value` | Forget tag knowledge without changing pointer or region |
| `Nbt.toI32 value` | Native numeric read at scale 1, rounded down; nonnumeric values fail |
| `Data.readOne target path` | Copy exactly one game-NBT match |
| `Data.readAll target path` | Collect all game-NBT matches into a list |
| `Nbt.readOne value path`, `Nbt.readAll value path` | Select from an immutable runtime snapshot |
| `Data.write target path value` | Copy a complete snapshot into game NBT |
| `Nbt.native value` | Produce a command fragment using native macro serialization |

Snapshots can cross functions, be stored in ADTs, and be explicitly persisted.
Native copy preserves Long, Float, Double, strings, and arrays.
Numeric computation requires an explicit `Nbt.toI32` conversion.

```lean
open Oria Oria.Std Oria.Std.Command.Arg

def store : DataTarget := .storage "demo:data"

@[mcfunction]
def selectedNumber (i : Val Int32) : Prog (Data.grade store) Int32 := do
  let path := ((Nbt.Path.key "tasks").matching (nbt% {owner: "Ada"})).field "n"
  let values ← Data.readAll store (some path)
  let value ← Nbt.readOne values (some ⟨.index (.dynamic i), []⟩)
  Nbt.toI32 value
```

Reads bind normal snapshots and propagate failure through ordinary do notation. `Data.write` retains native modification results;
writing unchanged content can fail.

A runtime leaf is `{tag:0,payload:[],value:<NBT>}`.
Object parameters, fields, locals, and stack slots carry its pointer.
Promotion copies the native value and adds descriptor d = 1 and management metadata.
GC treats native contents as opaque data, including integer values.
All tag-knowledge variants share the same leaf-copy interpretation.
Outer return releases snapshot-read and macro temporary storage.

NBT memory operations have typed operand telescopes.
`abstractFragment_restore` proves restoration after operand abstraction.
Machine retains explicit NBT operations; DP121 implements native copy, match cardinality,
and numeric conversion, freezing inputs before publishing reused output locations.

## Host SNBT output

`Value.format` and `pretty width` produce readable Std.Format layouts.
`Value.renderSnbt` checks float finiteness and emits one-line SNBT for command files.
NaN and infinities can be represented as host values but cannot be rendered as SNBT.

Strings reuse Lean.Json escaping. Dollar signs use `\u0024` so literal macro-like text
remains string content.
Float formatting converts the exact binary value to a JsonNumber representation and retains
negative zero. The resulting decimal can be longer than a human-oriented Float.toString.
This host formatter is distinct from Minecraft's native macro formatter.

## Paths and match cardinality

`Nbt.Path i p` contains field names, indices of type i, list selection, and filters of type p.
Its default indices are Int and its default filter type is Empty.
`.key` starts a path; `.field`, `.at`, and `.all` extend it.
`map` maps indices and has interface identity/composition laws.

Std paths use `Nbt.Path Scalar (Nbt.Value .compound)`.
Indices can be host constants or dynamic I32 expressions; compound filters are host values.
`.matching (nbt% {owner: "Ada"})` selects matching list compounds.
Target storage identities are carried separately.

For `{tasks:[{owner:"Ada",n:1},{owner:"Bob",n:2},{owner:"Ada",n:3}]}`:

```text
tasks                 → one list value
tasks[]               → three compound values
tasks[].n             → integer values 1, 2, 3
tasks[{owner:"Ada"}].n → integer values 1, 3
```

Each path segment acts on all currently selected nodes.
Missing fields contribute no results. Selection itself does not construct an NBT list.
See [Mojang's path description](https://www.minecraft.net/de-de/article/minecraft-snapshot-18w43a).

| Reader | Cardinality |
| --- | --- |
| readOne | Exactly one match succeeds; zero or multiple matches fail |
| readAll | Collect matches in selection order; no matches on a valid target/path succeed with an empty list |

Target-access, parsing, and copy errors remain failures.
Each read starts fresh result storage and cannot expose a previous result after failure.
`readAll("tasks")` collects one whole task list into an outer list;
`readAll("tasks[]")` collects its elements.

Native data-get requires a unique match and returns a number or size.
Set-from chooses the final source match, so readOne separately checks uniqueness.
Append-from copies source matches to a cleared list; native no-match failure is normalized
only for the reader's empty-selection case.
Unchanged native modifications can also fail.
These contracts are checked against the
[pinned server](../minecraft-26.3.lock.json).

## Native macro transport

`Nbt.native` uses Minecraft's function-macro formatter.
Strings become raw text without quotes; numeric tags lose their suffix;
Float/Double use the native decimal format with at most 15 fractional digits.
Compounds, lists, and arrays use SNBT.

Use native fragments where that serialization is the intended command argument.
Use `Data.write` for a tag- and value-preserving copy.
A string hole is not automatically a quoted SNBT string.
Host compound construction, mixed-field fragments, and complete runtime compounds share
the command codec pipeline.

Std path constructors currently provide static keys and compound filters with dynamic
integer indices. Runtime snapshots are immutable; game data updates use Data operations.

## Persistent snapshots

`Nbt.snapshot document path` copies one
typed selection into a fresh immutable `Val Nbt.Data`. Selection failure follows the
computation's failure exit. Native copying preserves the tags and contents of strings,
arrays, compounds, and numeric values.

```lean
let document ← Nbt.alloc (#[3, 7] : Array Int32)
let snapshot ← Nbt.snapshot document Nbt.Access.root
Nbt.set document (Nbt.Access.root.at (0 : Val Int32)) (.i32 99)
let durable ← Persistent.persist snapshot
saved := durable
```

Here `saved` is a registered `Persistent.Root Nbt.Data`. The published value is `[3,7]`.
Mutating the owned document changes neither the snapshot nor the persistent copy.
The explicit `snapshot` → `persist` → root-assignment sequence separates native copying,
arena promotion, and reachability. Mutable `Nbt.Ref` values remain ineligible for promotion,
including references nested in ordinary ADTs.
The snapshot's native contents form a GC leaf: their numeric fields are data, even when
they happen to equal an Oria address.

## Acceptance

`Oria.Proofs.Nbt` checks construction syntax, binding, interpolation, codecs, serialization,
and diagnostics. Final target output and native suites exercise compiler memory use.

The [NBT artifact fixture](../tests/NbtArtifact.lean) is parsed by Minecraft and checks
integer widths, arrays, mixed lists, escaping, negative zero, and extreme finite doubles.
Runtime-NBT suites cover selection, empty results, failure propagation, repeated literal
materialization, function/ADT transport, native copying, macro arguments, persistence, and
GC-root recovery with register and all-stack configurations.
The typed-NBT fixture also mutates a document after snapshotting, ends the invocation,
collects, and reads the preserved snapshot through a root.
See [integration acceptance](../integration/datapack/README.md).
