# Elaboration rules

Oria elaborates Lean source into typed Tree programs. A type tells the elaborator whether
a term is host data, an object expression, or an object computation. Syntax determines
which information is available when that type is checked.

The [checked examples](../Oria/Examples/Elaboration.lean) accompany this guide.
Start source files with `module`, import `Oria`, and use `meta import Oria` for attributed
definitions. [Lean integration](lean4.md) describes the trusted compiler interface.

## Values, expressions, and computations

| Type of a term | Meaning | Evaluation |
| --- | --- | --- |
| `Nat`, `String`, a Lean record, a host function | Host value | While constructing the program |
| `Val A r` | Pure object expression with source type A and region r | In the generated program |
| `Prog g A r` | Object computation returning a normal `Val A r` | When sequenced into the generated program |
| `Persistent.Root A` | Named persistent-cell description | Reads and writes are object computations |
| `Nbt.Access i A B` | Typed native path from A to B | The description is assembled in Lean; its indices may contain object expressions |

`g` records context requirements and effects. `.pure` is an empty grade. `r` records the
region guarantee of the normal result. The default region `.any` admits invocation-local
values; `.persistent` guarantees a persistently storable graph.

A pure grade describes effects. A constructor or a named pure function call still has
type `Prog`, so binding its result uses `←`.

## Selecting object `do`

An expected type `Prog g A r` selects Oria's `do` elaborator. Other expected computation
types use Lean's ordinary facilities. A body ascription can supply the result type while
letting the elaborator compute the grade:

```lean
@[mcfunction]
def readPoints := show Prog _ Int32 from do
  let n ← Scoreboard.get .self "points"
  return n + 1
```

Lean checks a declaration's header before its body. Put an inferred grade hole in this
body ascription. A fully written header checks the body's computed grade. `Prog.weaken`
explicitly changes it to a proved upper bound.

The following binding and control-flow rules apply inside an object `do`. Object
operators, field projection, and expected-type-directed constructors can also occur in
ordinary Lean expressions while building a program.

## Bindings

### Identifier bindings

| Form | RHS classification | Result |
| --- | --- | --- |
| `let x := e` | Host value | Lean let-binding |
| `let x := e` | `Val A r` | One shared object binding, with the same region |
| `let p := action` | `Prog g A r` | Name a program description |
| `let x ← action` | `Prog g A r` | Execute the computation; bind its normal value |
| `let _ ← action` | `Prog g A r` | Execute and discard its normal value; propagate Failure |
| `let x ← root` | `Persistent.Root A` | `Root.get root`, returning a persistent value |
| `let x ← doc.field[i]` | I32 selection in `Val (Nbt.Ref A)` | Typed native read, with `memoryRead` and Failure |

The RHS of an unannotated binding synthesizes its type. The elaborator resolves available
synthetic typeclass arguments; unresolved type parameters and coercions retain Lean's
constraint-solving behavior. An explicit binder annotation supplies information for
checking. Uses later in the block do not choose the datatype of an unresolved leading-dot
constructor.

```lean
let offset : Nat := 10
let x := n + offset
let action := Scoreboard.get .self "points"
let a ← action
let b ← action
return x + a + b
```

Here n is a `Val Int32`. The let for x introduces one object value. The action description
is executed twice. Naming it does not read a score or cache a command result.

`let x := 10` follows Lean's numeric default and gives x the host type Nat. Write
`let x : Val Int32 := 10` to bind an object constant. A literal in `return 10` is checked
against the block's result carrier. Converting a computed host value uses an explicit
operation such as `I32.lit`; the arithmetic instances also accept host Nat operands.

Object division is a computation, with scoreboard floor rounding and Failure on zero:

```lean
let q ← x / y
return q + 1
```

The RHS of an arrow binding completes typeclass synthesis before Oria checks for a `Prog`.
This also supports other typeclass operators whose result is an object computation.

For an object expression, the expansion is:

```lean
do let x := e; rest
-- expands to
Prog.bind (Prog.pure e) (fun x => rest)
```

Equivalently, for `e : Val A r` and a continuation of type `Prog g B q`:

\[
\frac{\Gamma\vdash e:\mathrm{Val}\ A\ r\qquad
      \Gamma,x:\mathrm{Val}\ A\ r\vdash k:\mathrm{Prog}\ g\ B\ q}
     {\Gamma\vdash\mathbf{do}\ \mathbf{let}\ x:=e;\ k:
      \mathrm{Prog}\ g\ B\ q}.
\]

Tree retains the shared binding. ANF gives its result a local atom. Later optimization
may propagate constants or choose a physical representation. The binding itself does
not prescribe a register, spill slot, or heap allocation.

Host functions and collections of expression descriptions retain their Lean types.
For example, `let f (x : Val Int32) := x + 1` defines a host generator. A host tuple
containing two expressions is host data; bind an individual `Val` to share its object
evaluation. Outside an object `do`, a Lean let naming a `Val` shares its description.

### Pattern bindings

Object patterns use the same source-typed pattern compiler as `match`:

```lean
let .mk (.mk wins losses) rounds := state
let .some n := optional | return 0
let .some n ← action | return 0
```

The first form requires an exhaustive pattern. A fallback form selects its fallback when
the pattern does not match. In the arrow form, failure of `action` occurs before matching
its normal value and follows the surrounding failure continuation. Catch that failure
with `try`/`catch`, `.getD`, `.orElse`, or another explicit recovery combinator.

Host patterns use Lean matching. Ordinary local bindings are immutable. Assignment is
available for persistent roots and typed native selections. `let mut` and configured
let forms, such as `let +generalize`, are outside object `do`.

## Statements, results, and exits

| Form | Behavior |
| --- | --- |
| `return v` | Return a `Val` to the nearest enclosing object `do` |
| `return .ctor args` | Construct an object, then return its value |
| Final `action` in a value-returning block | Supply the computation's normal result |
| Intermediate `action` | Execute it and discard the normal result; propagate Failure |
| Final `action` in a Unit block | Execute it and finish with Unit; propagate Failure |
| `action.discard` | Discard the normal result and preserve Failure |
| `action.ignore` | Handle Failure and discard the normal result |
| `try body catch _ => handler` | Run the handler on body's failure exit |

Use `return Val.unit` for an explicit object Unit value. Integer literals can be checked
as `Val Int32`; `Bool.lit` and `Val.unit` explicitly construct the corresponding pure
expressions. `return` takes a normal value, while an action is sequenced with `←` or used
as the final computation.

```lean
let n ← Scoreboard.get .self "points"
if n < 0 then return 0
Scoreboard.set .self "points" (n + 1)
return n
```

Early return exits the nearest object block. A nested object `do` creates its own return
destination. Statement `if` and `match` share their following continuation. Recovery
retains effects that occurred before failure; it does not restore earlier world or root
state. See [failure semantics](failure.md).

## Conditions and matching

| Discriminant | Interpretation |
| --- | --- |
| Lean `Bool` or `Prop` condition | Host choice while constructing the program |
| `Val Bool` condition | Object branch |
| Host match discriminants | Lean pattern matching |
| Object match discriminants | Source-typed pattern matrix, followed by decision-tree lowering |

An object match's discriminants must all be object values. Supported patterns include
constructors, nested constructors, I32 literals, wildcards, and variable binders. Object
matching uses first-match order and checks exhaustiveness. Named discriminants, dependent
motives, and generalizing object matches are outside this interface.
Conditions use plain `if condition`; dependent `if h : condition` and `if let` require
an explicit match or a host helper.

Branch grades are joined. Host alternatives are also checked with their joined grade,
even though only the selected alternative constructs runtime code. Error messages show
the names of requirements and effects when a declared grade differs.

## Records and constructors

`deriving Oria.Object` supplies typed builders and projection metadata. Expected `Prog`
types and object-action positions select these builders:

```lean
let p ← Point.mk x y
let q : Val Point ← .mk x y
return .mk x y
```

A qualified constructor identifies its datatype. Leading-dot syntax obtains the datatype
from an expected type or binder annotation. Constructor arguments are existing `Val`
expressions. Construction returns `Prog .pure A` with region `.any`.

Projection `s.field` preserves s's region. Record construction and update return fresh
ordinary objects. Named nested fields share their reconstruction path:

```lean
return {state with
  counters.wins := state.counters.wins + 1
  counters.losses := state.counters.losses + 2
  rounds := state.rounds + 1}
```

The source is bound once, `counters` is reconstructed once, and then the outer record is
constructed. Omitted fields retain their values. Overlapping assignments such as
`counters := c` and `counters.wins := n` are rejected. Each intermediate path must name a
derived record field. Inherited object records retain their parent object, addressed as
`toParent.field`. Bind nested constructor computations before using them as field values.
A reconstructed persistent record requires explicit `persist` before publication.

## Typed native access and assignment

For `doc : Val (Nbt.Ref Buffer)` or a registered `doc : Nbt.Global Buffer`, the following
forms expand to `Nbt.readI32` and `Nbt.set`:

```lean
let x ← doc.values[row][column]
doc.values[row][column] := x + 1
doc.label := "updated"
```

The deriving metadata resolves each field. Array steps preserve the element type. Indices
accept `Val Int32`, integer literals, and host Nat/Int/Int32 values through the ordinary
wrapping Int32 conversions. Negative indices retain Minecraft's indexing convention. Missing or
out-of-range reads use Failure. Writes follow native `data modify`: an unchanged value
fails, missing compound keys may be created, and invalid list indices fail.

Reading with this shorthand produces I32. Native strings, compound data, and arrays remain
available through explicit `Nbt.snapshot`, `Nbt.copy`, `Nbt.appendFrom`, and related typed
operations. Assignment takes a host value of the selected type, or an object I32 for an
I32 selection. It does not turn native strings into object arithmetic values. To continue
regardless of a native write's result, use the existing failure combinator:

```lean
Prog.ignore do doc.label := "updated"
```

The shorthand is recognized on an arrow binding's RHS and an assignment's LHS. Use
`Nbt.readI32 doc path` when naming or passing a read computation as a host value. Existing
`Buffer.Nbt.field` paths support composition with `.then` and `.at`, including operations
such as `Nbt.length` and `Nbt.snapshot`.

A native global's relative storage name and field path are retained in memory IR.
Target lowering qualifies them with the datapack's namespace.
Its content type comes from `Nbt.Repr`; globals and arena references share `Nbt.Location`
and the same typed access construction. See [global native documents](nbt.md#global-native-documents).
For `points : Nbt.Global Int32`, `let n ← points` reads the root value and
`points := n + 1` replaces it. A record global can likewise receive a host record value.

A root assignment `saved := value` invokes `Root.set` and requires
`value : Val A .persistent`. Typed NBT assignment mutates the selected arena document or global subtree.
Both assignments return Unit. Pure object-record updates produce a new value instead of
mutating their input. See [NBT](nbt.md) and [persistent memory](persistent-memory.md).

Assignments can occur in statement `if` and `match` branches and host-iteration bodies.
The following continuation runs after the selected branch completes normally. An unselected
branch performs no access; a failed write uses the surrounding failure continuation.
Before elaboration, Oria asks Lean to analyze early returns and loop exits using a
control-only view in which assignments have one normal exit. The original syntax is then
elaborated with its typed path, write source, effects, and Failure. Host `do` expressions
retain Lean's ordinary binding and mutation behavior.

## Local recursion and iteration

```lean
let rec go (i acc : Val Int32) : Prog .pure Int32 := do
  if i <= 0 then return acc
  go (i - 1) (acc + i)
go n 0
```

When all parameters are `Val` carriers and the result is a `Prog`, `let rec` expands to
`Prog.fix`. Write the complete parameter types, result type, and grade. The function body
can capture surrounding values and call itself with its local name. Recursive occurrences
become symbolic first-order calls. This form accepts one recursive declaration per binding.

Other recursive signatures use Lean's recursion machinery and termination checking.
A Nat-parameter generator returning `Prog` is therefore a host recursive function.
Runtime recursion may diverge; its grade describes effects. Attributes and termination
hints belong to the host-recursion form.

`for` iterates a finite host List, Array, or range during construction. `break` and
`continue` act within that loop; `return` exits the containing object block. Runtime loops
use recursive object calls. `Task.checkpoint` and `Task.yield` are explicit suspension
operations. See [recursion](recursion.md) and [tasks](tasks.md).

## Deriving and declaration attributes

| Declaration | Generated interface | Conditions and role |
| --- | --- | --- |
| `deriving Oria.Object` | `Object` instance, constructor builders, projection metadata | Public ordinary-Type datatypes; regular recursion and Type parameters |
| `@[value_type]` with `Oria.Object` | Inline-product representation request | The layout preparation pass checks representability |
| `deriving Nbt.ToNbt` | Host encoder | Source fields use their host encoders |
| `deriving Nbt.FromNbt` | Host decoder with structured errors | Source fields use their host decoders |
| `deriving Nbt.Repr` | Both codecs, schema, round-trip proof, typed field paths | Nonrecursive, unindexed native descriptions |
| `@[mcfunction]` | Quoted Tree plus `.ref` and typed `.call` | Closed object signatures; implicit region parameters are permitted |
| `@[root]` | Named root and initializer registration | Closed persistent result; restricted initializer effects |
| `@[datapack]` | Collected, compiled artifact | Registered entries, hooks, roots, and tasks determine the reachable program |

`Oria.Object` rejects indexed families, proof/runtime-dependent fields, universe
polymorphism, private constructors, and empty inductives. Recursive type arguments must
remain regular. Supported nested recursion includes persistent Ref fields. The object
catalogue and representation preparation retain their own closure/layout checks.

For an object record `Point`, the generated metadata has three jobs:

1. The `Object` instance associates the source type with its object schema.
2. Constructor metadata redirects `Point.mk` to a typed program builder in an object
   computation position. With host arguments and a host expected type, `Point.mk` remains
   the ordinary Lean constructor.
3. Projection and constructor-field metadata support `p.x`, record notation, and object
   patterns while retaining the source field types and region constraints.

The derived interface describes construction and elimination of object values. A host
`Point` and a `Val Point` belong to different stages; deriving supplies the interfaces
for each stage rather than an implicit conversion between arbitrary values.

NBT deriving operates on host types. Records become named fields, enums become strings,
and payload constructors use the documented constructor/payload encoding. `Nbt.Repr`
generates `A.Nbt.field` selections for records, including flattened inherited fields.
Its round-trip proof concerns values encoded by that codec. Validation of arbitrary game
data remains a separate operation. An NBT description containing strings or arrays can
be used as `Val (Nbt.Ref A)` without making A an ordinary object datatype.

For example, the checked `Buffer` definition derives `Nbt.Repr`. `Buffer.mk` constructs
host data for `Nbt.alloc`; `Buffer.Nbt.values` supplies an access path for the resulting
native handle. `Counters` instead derives `Oria.Object`: `let c ← Counters.mk 1 2`
constructs an object record, and `c.wins` denotes an object projection. Both declarations
use Lean structure syntax, with different instances and metadata selecting their roles.

Calling a Lean builder such as `f x` constructs code in the host. `f.call x`, generated by
`@[mcfunction]`, preserves an object function call with the source signature. Local object
recursion supplies its own symbolic self-call and uses the local function name directly.
An attributed function has explicit `Val` parameters, optionally preceded by implicit
region parameters. Its object source types, result type, and grade must be closed with
respect to value parameters. The attribute registers a checked function description;
datapack elaboration follows its `.call` dependencies to collect the reachable definitions.
Datapack public entries accept zero object arguments and return Unit.

## Verification and implementation

The frontend reuses Lean's parser, hygienic syntax, structure metadata, typeclass synthesis,
and do elaboration continuations. Lean supplies parsed field paths; the object adapter
groups them by direct fields, retaining parent objects addressed through `toParent.field`.
These operations construct the existing typed builders. Tree, Cont, Machine, and DP121
retain their responsibilities.

[Elaboration proofs](../Oria/Proofs/Elaboration.lean) check definitional expansions and
diagnostics. The final-artifact test compares pure-let and explicit-bind datapacks.
Native acceptance runs nested updates, host/object recursion, typed reads/writes, and
failure recovery with register and all-spill configurations. Merge sort exercises the
same access and recursion forms across cooperative checkpoints.

Lean documents [term elaboration](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Elaborators/)
and [do extensions](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Extending--do--Notation/).
These facilities provide local contexts, expected types, continuation information, and
source metadata used by Oria's elaborators.
