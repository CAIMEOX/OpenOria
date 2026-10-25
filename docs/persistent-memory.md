# Persistent memory

Oria has an invocation arena for temporary objects and a persistent arena for values retained
between invocations. Named roots establish persistent reachability.
Writes replace roots or explicitly mutate persistent Ref cells.

[Native globals](nbt.md#global-native-documents) have a separate representation:
`Nbt.Global A` names a storage subtree containing native NBT, with typed reads and mutation.
Its contents survive calls without promotion or managed GC. `Persistent.Root A` retains
ordinary object values and their managed graph; `Nbt.snapshot` can copy native data into
an immutable value for that interface.

## Roots and regions

Declare a root with an initial persistent value and register its stable storage identity:

```lean
module

import Oria
import Oria.Datapack
meta import Oria
meta import Oria.Datapack

open Oria Oria.Persistent

@[root]
def points : Root Int32 := Root.init (persist 0)

@[mcfunction]
def increment : Prog stateGrade Unit := do
  let old ← points
  let next ← persist (old + 1)
  points := next

@[datapack]
def game : Datapack.Spec :=
  Datapack.build {ns := "memory"} do
    Datapack.root "memory:points" points
    Datapack.entry "increment" increment.ref
    Datapack.collector "gc"
```

A root has a declared type and initializer; distinct roots of the same type have distinct
identities. Every registered root is initialized. Root replacement retains the previous
object if another root, Ref, or current local value still refers to it.

`Val A .persistent` guarantees a persistently storable reachable graph.
Ordinary `Val A` can reference either arena.
Forgetting a persistent region guarantee is a zero-cost coercion.
Explicit `persist` promotes a value; it does not update a root.

```lean
persist  : Val A → Prog allocGrade A .persistent
Root.get : Root A → Prog readGrade A .persistent
Root.set : Root A → Val A .persistent → Prog writeGrade Unit

Ref.new : Val A .persistent → Prog allocGrade (Ref A) .persistent
Ref.get : Val (Ref A) r → Prog readGrade A .persistent
Ref.set : Val (Ref A) r → Val A .persistent → Prog writeGrade Unit
```

These signatures omit Object evidence. Persistent effects compose in ordinary Prog.
Ref retains cell identity; promoted structures containing a Ref retain the same cell.
Writes require persistent contents, including when the handle's region has been forgotten.

Region-polymorphic functions can preserve an input region in their result.
The region parameter is erased from the object ABI, yielding one object function body.
New ordinary ADT construction belongs to the invocation arena and can reference persistent
fields. Such a mixed graph must be promoted before writing it into persistent storage.

## Execution stages

For persistent state \(P\), an invocation uses fresh arena \(E\) and data stack \(S\):

\[
\mathsf{Idle}(P)
\longrightarrow\mathsf{Run}(P,\varnothing,\varnothing)
\longrightarrow\mathsf{Idle}(P').
\]

Persistent slots remain valid throughout Run.
Replacing a root or Ref therefore leaves existing local references usable.
Outer return releases E and S.

[Cooperative tasks](tasks.md) retain their own E and S while parked between ticks.
Ordinary entries have separate invocation storage and may run while a task is parked.
Persistent references held by task locals remain valid because the exported collector
rejects calls while a task is queued, parked, or running.

One execution phase is shared by all public entry points: idle, ordinary entry, task
slice, collection, or initialization. A public entry checks idle before changing registers,
panic state, or workspace contents. Nested native callbacks receive failure at that boundary.
Completion and recoverable failure release the phase after workspace cleanup. A task
releases it when parking, completing, failing, or being cancelled. Load/tick hooks have
individual entry wrappers, so one hook's failure does not skip subsequent hooks.

A separately exported collector implements:

\[
\mathsf{Idle}(P)
\xrightarrow{\mathsf{gc}}\mathsf{Collect}(P)
\longrightarrow\mathsf{Idle}(P').
\]

`Datapack.collector` exports maintenance, not an ordinary object-call reference.
The user invokes it after an ordinary entry returns. A, GC, and B may run sequentially
within one tick. Allocation and ordinary return do not trigger collection.

Only registered pointer-root components form the GC root set.
Registers, the invocation arena, and the data stack have no live source references at
that boundary. Residual numeric contents of registers are not persistent handles.
The VM objective, generated function identities, and runtime/persistent storage paths
belong to the compiler. Native callbacks and user commands must preserve those resources.

Normal execution is synchronous. It provides neither a 50 ms bound nor rollback after a
fatal failure. `#panic` and `return fail` are debugging observations; execution and storage
after a fatal failure are outside the defined language behavior.

## Object and slot layouts

Invocation object i uses address \(-(i+1)\), persistent slot i address \(i+1\).
Layout word kinds determine which values are pointers before their signs are interpreted.

Ordinary objects store `{tag,payload}`.
An occupied persistent slot also stores descriptor, epoch mark, and a management link:

```snbt
{d:6,mark:0,next:1,tag:2,payload:[73,4]}
```

Occupied slots have d > 0. A free slot stores `{d:0,next:...}`.
The same `next` field links the used or free list. Sweep replaces slot contents while
preserving list indices.

For n payload slots and pointer bits \(b_i\):

\[
d=2^n+\sum_{i=0}^{n-1}b_i2^i,
\qquad n\le30.
\]

The sentinel encodes n; low bits follow physical slot order.
Header fields do not count as payload slots.
GC dispatches by d, while source pattern matching dispatches by tag.
Different types and constructors with the same d share a scanner.

Ref has management tag 0 and contains its element's physical words, including expanded
value-type fields. Its 30-slot limit is checked after expansion.
A Ref Unit has no payload slots.
Native NBT leaves retain their `value` field and use d = 1; their nested native numbers
are data, not Oria pointers.

## Promotion

Persistent requests have closed, first-order, regular types with at most 30 slots in every
reachable heap payload. Inline values themselves may be wider.
Initializer failure prevents publication of that root's value and leaves readiness unset.
Command results may first be explicitly materialized as Option.

Preparation builds a finite copy graph shared by runtime generation and Machine.
Scalar nodes copy their words; Ref nodes retain their addresses; boxed nodes choose field
actions from their source constructor tag.
Ephemeral objects have no descriptor, so this closed type graph supplies the interpretation.

A promotion memo maps source addresses to persistent addresses and layout evidence:

\[
M:\mathsf{Addr}_E\rightharpoonup
(\mathsf{Addr}_P,\mathsf{PlanId}).
\]

The source address is the key. Incompatible interpretations of the same source address
produce panic. Different tag knowledge for one native-NBT leaf shares its copy identity.

Promotion proceeds as follows:

1. Return scalars and existing persistent addresses directly.
2. Return a previously recorded destination when the source address is memoized.
3. Reserve a destination slot, write a zero-payload skeleton, and register it in M.
4. Save source and destination state in a work frame. Copy payloads and recursively replace
   ephemeral pointer fields, retaining existing Ref addresses.
5. Publish the completed slot, release the work frame, and return its persistent address.

Memo registration precedes child traversal, preserving sharing.
The operation completes synchronously within one tick. Task checkpoints occur outside
promotion; recursive copying needs a finite region bound to be used in a cooperative task.
Root publication is a separate user operation.

The memo is a compound keyed by decimal source address. Structured dynamic-key paths encode
the lookup. Work frames keep nested copying from overwriting parent state.

## Allocation and collection

Allocation removes the free-list head when available; otherwise it appends a slot.
The slot joins the used list, gets the current epoch mark, and retains a positive I32 address.

GC chooses epoch `1 - epoch` and starts a work stack from pointer roots:

1. Read the occupied slot and validate its descriptor.
2. Skip an address already marked with the new epoch.
3. Mark it, then append its pointer fields using the descriptor's scanner.

Mark-before-scan handles cycles and shared subgraphs.
A scanner reads one object scratch copy and accesses fields at static offsets.
Sweep follows the used list, retains newly marked slots, and moves other slots to the free
list. The epoch is committed after successful sweep; a marking failure prevents sweep.

For U occupied slots, L reachable objects, B reachable edges, R roots, and D scan shapes,
sweep costs O(U), graph marking O(R + L + B), and current linear descriptor dispatch adds
O(LD). Native NBT copying, path resolution, and macro costs require separate measurement.

## Initialization and storage identity

First load creates the allocator and runs registered initializers.
ABI 2 stores each root as a list of physical words. Scalar roots use one-element lists;
zero-width roots use empty lists. Initializers publish every result component before their
call frames are released. GC enumerates only the root components classified as pointers.
Initializers cannot read/update existing roots or execute native commands, including
through transitive dependencies. They can allocate new Ref cells for the initial graph.

Existing storage is checked against the ABI version and canonical root/schema JSON.
The description includes stable root keys, closed root types, field/constructor order, and
representation hints and resolved physical word kinds. Transient copy indices, register
budgets, and initializer bodies are excluded. ABI 1 storage requires explicit replacement
or an external migration before loading this format.
A matching schema preserves values. A mismatch leaves ready at zero, rejects ordinary
entries, and preserves the existing storage for inspection.

## Compilation and acceptance

[Runtime.GC](../Oria/Runtime/GC.lean) generates ordinary Prog marking, scanning, and sweeping
from prepared scanners and root identities. Its definitions enter collection before closure
checking and follow Cont, Machine, demand, allocation, and DP121 lowering.

Scanners are shared by descriptor. Tree and Cont retain one remainder continuation after
each conditional field append. Machine control-flow and condition optimization reduce their
generated blocks and temporary values.
[RuntimeGC](../Oria/Proofs/RuntimeGC.lean) checks linear generation for 0 through 30 pointer
slots and that the collector does not allocate managed objects.

DP121 implements the allocator, copy frames, memo, initialization, and maintenance wrapper.
The maintenance wrapper checks readiness and quiescence, clears panic, invokes collection, and cleans
its data stack. Ordinary invocation storage is not a GC root at this boundary. A registered
task must complete or be cancelled before this maintenance entry can run.

The [heap model](../Oria/Runtime/HeapModel.lean) states decoded cells as native/scalar
contents plus the edges selected by their descriptors. Kernel-checked theorems establish:

- fresh memo reservation preserves destination uniqueness;
- a completed promotion's address map preserves values, aliasing, and finite graph paths;
- publishing a live root and writing live persistent edges into a Ref preserve closure;
- the marker's initial worklist, scanned-cell step, and already-marked step preserve
  root/edge coverage; an empty worklist establishes mark closure;
- a root-containing, edge-closed mark set lets sweep retain every reachable cell at its
  original address, together with heap closure and root validity.

Promotion theorems require the completed-copy relation. Collection theorems require the
mark-closure invariant. Refinement of the emitted allocator, copying loop, and marker to
these contracts remains a separate proof obligation; the theorems do not certify every
generated Minecraft command. The [phase model](../Oria/Runtime/Phase.lean) also proves
that entry requires idle and collection requires task quiescence.

`tests/golden/persistent/` fixes representative target functions.
`scripts/gametest` checks sharing, mixed ephemeral/persistent references, Ref cycles,
old local references, sequential collection, slot reuse, repeated load preservation, and
schema mismatch rejection. Its native callback fixture attempts nested entry, collection,
and initialization while an outer entry retains an arena object.
See [PersistentRuntime](../Oria/Proofs/Fixtures/PersistentRuntime.lean).

Background: [Tofte and Talpin](https://doi.org/10.1006/inco.1996.2613) on regions and effects,
and [The Garbage Collection Handbook](https://gchandbook.org/contents.html) on tracing collection.
