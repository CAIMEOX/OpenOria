# Building a datapack

`Datapack.Spec` selects public entries, tasks, load/tick callbacks, persistent roots, global
native documents, and collector paths. `@[datapack]` collects their named dependencies and
publishes a finite `.artifact`.

## Source example

```lean
module

import Oria
import Oria.Datapack
meta import Oria
meta import Oria.Datapack

open Oria Oria.Std Oria.Datapack

private def destination : Std.Command.Arg.Vec3 :=
  .world (.absolute 0) (.absolute 80) (.absolute 0)

@[mcfunction]
def home : Prog (Teleport.grade .self destination).handled Unit :=
  (Teleport.to .self destination).ignore

@[datapack]
def demo : Datapack.Spec :=
  Datapack.build {ns := "demo", description := "Oria teleport demo"} do
    entry "home" home.ref

public def main : IO Unit :=
  demo.artifact.writeTo ("output/demo" : System.FilePath)
```

The complete executable is [Teleport](../examples/Teleport.lean).
Imported definitions use Lean's ordinary name resolution.
Internal `.call` dependencies are collected automatically.
Several public paths can share one compiled function body.

A registration helper is an ordinary host function returning `Datapack.Builder Unit`.
Its Lean conditionals and loops decide which entries to include during construction.
Game control flow belongs to the registered functions' Prog bodies.

## Entry contract

A public entry has source signature:

\[
\mathsf{EntrySig}(g)=\langle[],\mathsf{Unit},g\rangle.
\]

Its source argument list must be empty, including when a potential argument would occupy
zero physical words. To expose a computation producing another type, define a named Unit
wrapper and register its `.ref`.
Internal functions retain typed parameters and return values.

The referenced definition must be registered with `@[mcfunction]`.
Lean checks the reference's signature; environment collection checks its declaration identity.

A public entry inherits the Minecraft caller's context. The caller must provide the grade's
requirements. For example, the teleport entry requires an executing entity.
Normal Unit completion returns native success with result zero; commands inside the
function follow lexical failure propagation and recovery. Public entries translate uncaught
failure to native failure after cleanup. Load/tick callbacks isolate failures at each registration.

The wrapper initializes its invocation arena and data stack, calls the compiled function,
and releases temporary state after completion.
Programs with managed persistent roots or global native documents additionally check storage
readiness.
An active invocation must respect reserved compiler storage and avoid reentering a public
wrapper that would reset that storage.

## Configuration

[Settings](../Oria/Datapack/Spec.lean) includes:

| Field | Meaning |
| --- | --- |
| `ns` | Validated resource namespace |
| `description` | Datapack description |
| `version` | Current target `.dp121` |
| `commands` | Optional explicit command declarations; defaults to Std.Manifest |
| `objective` | Optional compiler scoreboard objective |
| `registerBudget` | Total allocation budget, default 128, minimum 6 |
| `sliceBudget` | Cooperative task command quota per callback, default 20000 |

The budget includes four scratch and two return registers. Budget 6 places ordinary values
on the stack; 256 provides a larger allocation pool.
Dedicated heap/runtime registers are separate.
See [register allocation](register-allocation.md).

The builder is Lean's `StateM Spec`. `build` is pure.
Compilation diagnoses duplicate public paths/root identities, unresolved references,
unsupported representations, and missing command declarations.

## Callbacks

`onLoad setup.ref` and `onTick step.ref` register zero-argument Unit functions.
Their context requirements must be contained in `Req.server`, which supplies position,
rotation, dimension, and anchor, but no executor.

Code using `.self` can run inside `Execute.forEach [.as .allPlayers]`, which supplies the
executor for its body. See [Execute](execute.md).
Effects may be nonempty.

A phase dispatcher preserves registration order and repeated registrations.
Dependency collection deduplicates bodies, not callback invocations.
Load first runs compiler initialization, then user callbacks.
Tick calls its callbacks in order. Every callback owns its invocation arena.
Ordering relative to other datapacks follows Minecraft's tag execution.

## Tasks

`task "work" work.ref` registers a zero-argument Unit computation under server context.
Calling the public function submits it for the next game tick. The datapack has one active
task slot; a busy submission returns native failure. `function <namespace>:work/cancel`
releases that entry's active task and its workspace.

`Task.checkpoint` permits budget-driven parking; `Task.yield` always schedules the
continuation for the next game tick. Their effect is `Eff.suspend`. An ordinary entry or
callback cannot reach a suspension point. Task registers, frames, and invocation objects
remain valid across slices, while ordinary entries use separate invocation storage.
Collection entries reject calls while a task is active.

The compiler bounds physical command regions and reserves callback and parking costs.
Unknown native costs and cycles lacking safe boundaries produce diagnostics.
See [cooperative tasks](tasks.md) for the cost model, supported commands, and completion states.

## Persistent roots and collectors

```lean
Datapack.root "demo:points" points
Datapack.collector "gc"
```

A root has a stable storage identity and a declared initializer.
Initialization preserves an existing matching persistent schema.
A collector is a separate maintenance entry to invoke after ordinary programs return.
See [persistent memory](persistent-memory.md).

## Global native documents

`Datapack.global state` registers a value declared with `Nbt.Global.init storage path initial`.
The storage name is relative: `"state"` becomes `<ns>:state`, including inside task functions.
The same globals and source functions can be compiled under another Spec namespace.
`runtime` and `persistent` are reserved for compiler state.
Registered roots within one storage must have disjoint compound-field paths.
Compilation checks every reachable typed global access against these declarations.

First load initializes the owned subtrees before user callbacks. Subsequent loads preserve their
contents when the registered paths and native schemas match the saved manifest. Initializer
values and registration order may change without resetting data. A changed schema or a missing
initialized root blocks entries and leaves existing data in place.

Global native documents use the same typed field/index operations as `Nbt.Ref`, and are stored
independently of the managed persistent heap. See [native globals](nbt.md#global-native-documents)
for ownership, copying, and reload behavior, and the checked
[GlobalNbt example](../Oria/Examples/GlobalNbt.lean) for a complete declaration and registration.

## Resources and files

Public paths use `PublicFunctionPath` and reserve `__oria` for generated functions.
Internal function IDs are compiler-assigned; they are not a Minecraft access-control boundary.

The output includes public functions, internal blocks, macro helpers, `pack.mcmeta`, and
load/tick tags when registered. The DP121 metadata has min/max format `[121, 0]`.
Resource path segments preserve dots and cannot escape the artifact directory.

Target call-closure evidence is required before file assembly.
`Artifact` uses Lean.Json for metadata and System.FilePath for paths.
`Artifact.writeTo` requires an absent or empty destination directory.

Lake's datapack facets export imported checked declarations during an ordinary build and
manage their generated-file inventory. A native main provides explicit output to another
directory. See [Lake datapack builds](lake-datapacks.md).

## Acceptance

`scripts/quality` checks registration contracts, diagnostics, resource mapping, final
datapack contents, native file output, and downstream Lake builds.
`scripts/gametest` checks callback initialization/order, shared public aliases, typed calls,
dynamic teleport, normal Unit results, and invocation cleanup.
`scripts/rps-test` also exercises actual resource reload and player tick callbacks.

These suites use the [pinned server](../minecraft-26.3.lock.json).
Their scenario coverage and execution requirements are described in the
[integration guide](../integration/datapack/README.md).
