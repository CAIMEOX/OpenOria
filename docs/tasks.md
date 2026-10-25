# Cooperative tasks

Tasks execute one logical computation across game ticks. `Task.checkpoint` permits parking
when the current slice lacks fuel. `Task.yield` always continues on the next game tick.
Both operations contribute `Eff.suspend`; Failure recovery preserves that effect.

```lean
module

import Oria
import Oria.Datapack
meta import Oria
meta import Oria.Datapack

open Oria Oria.Datapack

@[mcfunction]
def work : Prog Grade.suspension Unit := do
  Task.yield
  return Val.unit

@[datapack]
def game : Spec := build { ns := "demo", sliceBudget := 20000 } do
  task "work" work.ref
```

`function demo:work` submits the task and returns submission success. A busy task slot causes
native failure without replacing the current job. `function demo:work/cancel` cancels that
entry's active job and releases its workspace. Each datapack has one task slot. Its logical
result is Unit; the computation can publish results to scores or named persistent roots.
Several public paths can name the same task definition and share its launcher and cancellation ownership.

## Execution and context

A task starts on the next game tick under the server's command context. Its requirement row
must be supplied by `Req.server`. `Execute.forEach` requires a synchronous body; it cannot
contain suspension. The current cost model diagnoses Execute traversal as an unknown bound.

Resumable function entries, explicit checkpoints, and continuations after resumable calls
are safe boundaries. Ordinary operations complete before crossing a boundary. Calls without
actual suspension retain the synchronous calling convention. Resumable calls store their
return continuation and caller values in an explicit frame, including recursive calls.
Normal returns and recoverable failures follow the original continuation and handler.

The task workspace uses `<namespace>.task:runtime`. It contains an invocation arena and an
explicit stack. That arena belongs to the entire logical task and stays resident while parked.
The compiler owns this generated namespace and its private function identities.
Ordinary entries use `<namespace>:runtime`. Register words live across parking and the arena
allocation cursor are saved before scheduling and restored before continuation. Existing spill
words and caller frames remain in place. A suspended computation never repeats earlier effects.

Ordinary entries, task slices, collectors, and initialization share the `#phase` execution
protocol. A running slice excludes reentrant public calls. A parked task releases that
execution phase, allowing ordinary entries to run with their separate arena. Its task slot
remains live, so collection still waits for completion or cancellation. Cancellation checks
the shared phase before releasing the retained task workspace.

Persistent objects retain the datapack's ordinary persistent storage identity. Collection
entries fail while a task is active, preserving objects referenced only by the suspended task.
Completion, unhandled Failure, and cancellation release the task workspace. Pack initialization
resets the slot and workspace. This protocol covers continuation within the running server.

Other game logic can change shared state between slices. A local snapshot read before a
checkpoint remains that snapshot after resuming; it is not a new read. Keep a read/modify/write
operation in a synchronous helper when it must finish within one tick.

## Fuel and cost bounds

The compiler calculates a bound for each yield-free region after physical operation emission.
The model counts function entries, execute wrappers, stores, macro bodies, and native commands.
Sequential costs add; returning conditional paths take the maximum. Calls to the next budget
gate end the region. A cycle without such a boundary or an unmodelled native operation produces
`unboundedTaskRegion`.

Native declarations carry an optional `Command.Ref.cost`, copied to their catalog declaration.
This is the library's semantic upper bound on the native command, excluding compiler-generated
wrappers. Standard bounds cover scoreboard get/set/operation and add/remove, and native
Data get, scaled get, merge, remove, and modify operations.
Compiler-owned NBT fragments carry their own bound. External commands default to unknown.
The cost contract assumes these declared bounds hold for the pinned server semantics.
Bounds concern the command quota, not wall-clock tick time.

Let Q be the smaller of `sliceBudget` and the server's
`minecraft:max_command_sequence_length`, B the bootstrap bound, and R the maximum parking bound.
The callback begins with `fuel = Q - B - R`. A region of bound U runs only when `fuel >= U` and
precharges U. Otherwise the runtime saves state, schedules its single private callback with
`1t replace`, and returns. The compiler and callback check that `Q >= B + R + max U`; insufficient
quota completes with the budget-error status instead of repeatedly parking the same region.
Submission and error cleanup have small startup costs that the server quota must also admit.
The task fuel covers its scheduled callback; it does not reserve commands in an external caller.

The invariant is `actualRemaining >= fuel + R`. `TaskBudget` proves the arithmetic reservation
steps. The physical cost model is checked against Minecraft 26.3 by native acceptance tests;
semantic preservation of the complete coroutine lowering is not yet proved.

## Generated runtime and verification

An ordinary entry whose closed call graph has no suspension generates the synchronous program.
It adds no task state, wakeup, budget gates, or task workspace. Explicit background registration
retains asynchronous submission even for a body that fits in one region.

The VM objective exposes diagnostic scores `#task.phase` (0 idle, 1 queued, 2 running),
`#task.status` (0 reset, 1 active, 2 completed, 3 failed, 4 insufficient budget, 5 cancelled),
`#task.slices`, and `#task.parks`. These scores belong to the compiler's reserved runtime.
`#phase` records exclusive execution: 0 idle, 1 ordinary entry, 2 task slice, 3 collection,
and 4 initialization.

`scripts/rps-test --tasks` runs both the default register budget and all-spill variant under a
512-command server quota. It checks non-tail recursion, tail backedges, multiword returns,
saved caller values, arena references,
ordinary-entry interference, exact effect counts, Failure recovery, busy submission, collection
exclusion, atomic background entries, and a server quota that cannot admit a region.
It also checks cancellation, ownership of the cancellation path, and submission after cancellation.

[NBT merge sort](merge-sort.md) exercises typed native operations over two arena lists;
`scripts/rps-test --merge-sort` verifies full sorted outputs and task lifecycle.

References: [Rust's coroutine transformation](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir_transform/coroutine/index.html)
and [Cooperative Task Management Without Manual Stack Management](https://www.usenix.org/conference/2002-usenix-annual-technical-conference/cooperative-task-management-without-manual-stack).
