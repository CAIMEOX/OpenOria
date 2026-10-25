# NBT merge sort

[MergeSort](../Oria/Examples/MergeSort.lean) sorts a runtime list of signed I32 values
using two typed native buffers. It compiles through the ordinary Tree, Cont, Machine,
and DP121 pipeline and uses cooperative checkpoints for long inputs.

## Run the example

```bash
lake exe oria-merge-sort output/merge-sort
```

Install the exported directory as a datapack, reload it, and submit an input:

```mcfunction
data modify storage merge_sort:state input set value [3,-2,3,0,1]
function merge_sort:sort
```

The task starts on the next game tick. Read its completion state and output:

```mcfunction
scoreboard players get #task.status merge_sort.oria
data get storage merge_sort:state output
```

Status 2 means completion; this input produces `[-2,0,1,3,3]`. Status 3 means an
unhandled command failure, and status 5 means cancellation. A busy submission fails
without replacing the active job. `function merge_sort:sort/cancel` cancels the task.
See [cooperative tasks](tasks.md) for the complete protocol.

The input contract is a native NBT list whose elements are I32 tags. Empty and singleton
lists are valid. Numeric reads use scale 1; they return I32 values directly and do not
materialize element snapshots. The program is not a general validator for arbitrary NBT.

## Storage and algorithm

The application owns `merge_sort:state`, with public fields `input` and `output`.
The working type is an ordinary Lean record:

```lean
structure Buffers where
  values : Array (Array Int32)
  deriving Nbt.Repr
```

Its generated field path `Buffers.Nbt.values` selects the outer list. The source form
`let x ← s.values[b][i]` reads an I32 element. Explicit paths compose one `.at b` for the
buffer with another `.at i` for the element. Function arguments carry
`Val (Nbt.Ref Buffers)` plus scalar range indices. Field names are resolved while building
the program; runtime macros contain only the dynamic indices and arena address.

The program snapshots input once, then converts each numeric element into the first typed
buffer. Conversion has checkpoints and does not allocate element snapshots. Input remains
unchanged. For run widths 1, 2, 4, and so on, it merges adjacent half-open ranges from one
buffer into the other, then swaps their integer buffer identities. `Nbt.store` copies the
final buffer to output.

Each range is represented by `lo`, `mid`, and `hi`; constructing a range does not copy
a sublist. The merge keeps the current heads `x` and `y` in ordinary register/stack
locations. Advancing one side reads only its next element. An exhausted side leaves the
remaining range to `drain`, which copies individual native tags directly. Equal heads
choose the left side first, preserving stable merge order.

`limit` computes endpoints against the remaining length. The same operation clips the
next run width, keeping valid I32 index additions in range. Fully annotated local `let rec`
functions provide the loops through `Prog.fix`; checkpoints let the runtime park and
restore their scalar state.

The sorting loops use `Nbt.readI32`, `Nbt.append`, `Nbt.appendFrom`, and `Nbt.clear`.
Clearing an empty buffer completes normally. Publication also succeeds when output already
contains the same result, so repeated sorted inputs require no special handling.

The arena contains two objects: the input snapshot and the typed buffer record. Their native
payload size is O(n). Scalar reads go directly into register/stack locations. Source-level
merge work is O(n log n); macro parsing and native NBT operations have their own costs.
The demo has not established a speedup over another sorting representation.

## Lifetime and effects

Completion, failure, and cancellation release the entire task arena and native scratch
fields. A failure before publication preserves the previous output. The input snapshot
isolates subsequent sorting from changes to the public input field. Working buffers belong
to the runtime and are not exposed in the application's storage.

The grade combines memory reads/writes, the standard Data world effect bound, failure,
and suspension, with no executor requirement. Lowering exposes the native operation cost
to the task budget analysis. These bounds concern command quota, not elapsed tick time.

The normal pack uses 128 registers and a 2048-command slice budget. The stack variant
uses six registers, placing ordinary words on the stack:

```bash
lake exe oria-merge-sort output/merge-sort-stack --stack
```

It exports `merge_sort_stack:sort` and shares the same application storage identity.
Install one variant for normal use.

## Acceptance

`scripts/rps-test --merge-sort` loads both variants on the pinned server and compares
complete output lists with Java's integer sort. Cases cover empty/singleton inputs,
duplicates, negative values, I32 extrema, repeated sorted inputs, reversed input, and
deterministic random input with a non-power-of-two length. It checks input preservation,
fuel-driven parking, scratch cleanup, numeric-read failure, cancellation, and resubmission.
The suite checks the two-object arena bound and command-quota exhaustion during the run.
It also exercises typed update/copy/clear operations, repeated equal writes, cross-function
aliasing, and failed out-of-bounds writes through a separate exported fixture.

The source is included in `OriaTests`; `scripts/check-docs` checks its declaration contracts.
Scope, call arity, and location certificates come from the compiler's existing interfaces.
End-to-end sorting correctness has not been proved.
