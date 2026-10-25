# Object values and invocation memory

`Object A code` relates a checked Lean source type to an object type.
`@[mcfunction]` and object deriving preserve the full source type in generated calls and
constructors. Host type arguments determine closed runtime schemas.

## Type identity and schemas

`TypeId` stores the Lean declaration name and complete object-type arguments.
For example, `Chain Int32` and `Chain Bool` have different identities.
Collection instantiates registered field templates and visits each concrete identity once.
Regular recursion produces a finite schema graph.

```lean
public inductive Chain (A : Type) where
  | nil
  | cons (head : A) (tail : Chain A)
  deriving Oria.Object
```

Object deriving supports ordinary type parameters, direct and mutual regular recursion,
and recursion through persistent Ref. Recursive references retain their original arguments.
Declarations must be public, nonempty, and in the supported fixed universe.
Non-regular recursion, general nested inductives, indexed families, dependent runtime
fields, and proof fields are outside the deriving subset.

Object data consists of Unit, Bool, I32, runtime NBT, Option, Ref, and registered ADTs.
Persistence additionally checks the closed physical layouts and per-object slot limit.

## Capturing completion

Commands return normal values through `Prog g Int32`. A failed computation leaves through
its failure exit. `attempt` captures that exit as ordinary Option data:

```lean
@[mcfunction]
def readPlus : Prog (Std.Scoreboard.readGrade .self) Int32 := do
  let x ← Std.Scoreboard.get .self "points"
  return x + 1

@[mcfunction]
def readOption : Prog (Std.Scoreboard.readGrade .self).handled (Option Int32) :=
  Prog.attempt readPlus.call
```

The Option can cross calls, occupy ADT fields, or be explicitly persisted. Capturing failure
retains preceding world effects. See [failure and recovery](failure.md).

## Physical layouts

| Value | Representation |
| --- | --- |
| Unit | Zero words |
| Bool, I32, payload-free enum | One scalar word |
| Value type | Concatenated scalar fields |
| Ordinary payload ADT, ordinary Option, Ref | One pointer word |
| Runtime NBT | One pointer to a native-NBT leaf |

All constructors of an ordinary payload ADT use boxed representation, including empty constructors.
`@[value_type]` selects an inline, pointer-free, single-constructor product.
Arguments, normal return values, and joins use the same frozen width table.
A potentially failing function prefixes its return words with a success flag. This flag is
calling-convention metadata and occupies no object field or persistent-root slot.
See [value types and layout correctness](value-types.md).

An ephemeral object is represented in storage as:

```snbt
{tag:1,payload:[41,-2]}
```

The header tag is separate from payload slots. Fields follow declaration order; Unit
contributes no slot; inline fields contribute all their words. User tags are constructor position plus one.
Option uses tags 0 and 1. Pattern dispatch reads the tag, then projects fields in the
selected branch.

Each allocation carries `HeapLayout n` with one word-kind entry per payload slot.
For pointer bits \(p_i\), its scan shape is:

\[
d=2^n+\sum_{i=0}^{n-1}p_i2^i.
\]

The sentinel bit records the slot count. Tags are outside this bitmap.
The two-slot scalar/pointer layout above has \(d=6\).
Ephemeral objects omit runtime GC metadata; persistent slots retain d and management fields.
Runtime NBT uses an opaque native value and the zero-slot descriptor \(d=1\).
See [persistent memory](persistent-memory.md) and [NBT](nbt.md).

## Arena and call lifetime

An outer entry creates an ephemeral arena. Internal functions share it.
Allocation writes a complete draft, appends it to the arena, and publishes the pointer.
Arena object i has address \(-(i+1)\); persistent slot i has address \(i+1\).

Generic reads select the arena by pointer sign after the layout has classified the word
as a pointer. Negative I32 scalars are not pointer candidates.
NBT addressing converts an object pointer to a list index and uses a typed macro hole;
field offsets remain static.

Outer return releases the arena, drafts, stack, and macro temporary state.
Internal return releases only its necessary activation frame.
Public entries return Unit, so object pointers cannot escape through their public result.
Named persistent roots retain values across invocations.
Each load/tick callback owns its own invocation arena.

## Optimization and validation

Cont simplification substitutes copies and reduces branches on known constructors using
their original payload atoms. Commands and calls retain their execution order.
Machine lowering chooses scalar and boxed operations and failure branches; demand removes unused result
components and pure allocations/projections where supported.

Scope, operand count, layout width, and call arity are indexed.
Layout tests, reference interpretation, final-output assertions, and native acceptance
check the corresponding protocols. Complete semantic preservation has not been proved.
See [compiler architecture](design.md) and [integration acceptance](../integration/datapack/README.md).
