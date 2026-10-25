# Compiler architecture

Oria constructs typed, first-order object programs in Lean and compiles them to Minecraft
datapacks. Lean modules, namespaces, and Lake packages organize the source. Named object
calls retain function boundaries in the generated program.

The supported toolchain is recorded in [lean-toolchain](../lean-toolchain), and the server
in [minecraft-26.3.lock.json](../minecraft-26.3.lock.json). The current target is
[DP121](../Oria/Datapack/Version.lean), with datapack format `(121, 0)`.
See [module structure](structure.md) for import entry points.

## Construction and elaboration

`Val A r` describes a pure object expression. `Prog g A r` describes ordered computations
with grade `g` and result region `r`. The default region is `.any`; `.persistent`
records that the reachable value graph satisfies persistent-storage constraints.
`Object A code` relates a Lean source type to its logical object type.

`@[mcfunction]` checks the complete source signature and publishes `.signature`, `.ref`,
and `.call`. An ordinary Lean call constructs the callee's body at construction time.
A saturated `f.call` emits a named object call. Runtime object functions have closed
argument and result types; host type parameters are resolved during construction.

Object I32 expressions support wrapping `+ - *`, comparisons, and Boolean operations.
Division is a `Prog .failure Int32` computation: `let q ← x / y` uses scoreboard floor
division and propagates failure for a zero divisor. The `MIN / -1` result wraps to `MIN`.
`&&` and `||` generate short-circuit branches. Lean's `=` remains a proposition.
The [source-program guide](source-programs.md) covers host computation, inference,
immutable records, finite host iteration, and lexical control flow.

## Effects, context, and command results

A `Grade` contains a context requirement row and an effect row. Sequential and branch
composition take unions. Execute scopes apply ordered context transformations: supplied
context discharges requirements at the point where it becomes available.
`Prog.weaken` explicitly enlarges a declared bound with a `Grade.Below` proof.
See [Execute](execute.md) for the composition rules.

Ordinary `do` uses Lean's `elabDoWith` extension. Binding receives an action's normal
object value; an unhandled failure propagates through the computation. The failure effect
belongs to the grade and is independent of the normal result type.

`try ... catch _ => ...` recovers within a lexical scope. `action.ignore` suppresses failure
and discards the normal value. `Prog.attempt action` captures completion as ordinary
`Option A` data. See [failure and recovery](failure.md) for the typing and lowering rules.

Object `do` supports early return, statement branches, pattern bindings, and finite host
`for` loops with break/continue. Runtime recursion uses `Prog.fix`.
Runtime reassignment and general dependent object matching are outside the source subset.
See [object construction](object-construction.md), [integer patterns](integer-patterns.md),
and [recursion](recursion.md).

## Whole-program compilation

`@[datapack]` compiles a `Datapack.Spec` and publishes a finite `.artifact`.
The [datapack builder](datapack-builder.md) registers zero-argument Unit entries and tasks,
ordered load/tick callbacks, persistent roots, and maintenance collectors.

[Meta.Datapack.compile](../Oria/Meta/Datapack.lean) assembles the stages:

1. Check registrations and resolve root initializers.
2. Collect reachable named definitions and instantiated object schemas.
3. Prepare the shared representation table and persistent-copy metadata.
4. Generate the ordinary Prog GC library when a collector is registered.
5. Check dependency closure, lower Tree to Cont, simplify scalars, and propagate owned-document memory facts.
6. Lower to Machine, simplify control flow, and eliminate dead code using whole-program demand.
7. Recompute demand, allocate locations, and lower Machine to DP121. Task registrations use
   actual suspension summaries to select resumable calls and explicit continuation frames;
   physical command-region bounds determine budget guards.
8. Share identical private definitions, linearize uniquely referenced tail successors,
   fold identical resulting bodies, check target call closure, and assemble the artifact.

Public paths and callback order belong to the specification; internal references belong
to the collected program. Repeated registrations preserve invocation order while sharing
a compiled function body.

## Program representations

```text
Val / Prog → Tree → Cont → Machine → DP121 → Artifact
```

| Representation | Contract |
| --- | --- |
| [Tree](../Oria/IR/Tree/Syntax.lean) | Source-shaped pure expressions, ordered computations, scoped recursion, Execute bodies, and typed pattern matrices. Locals have nominal identities. |
| [Cont](../Oria/IR/Cont/Syntax.lean) | Atomic operands, primitive bindings, single-constructor dispatch, normal/failure invocation successors, lexical joins, and jumps. Types and local/join scopes are indexed. |
| [Machine](../Oria/IR/Machine/Syntax.lean) | Word-level instructions, typed block edges, finite function references, and argument/result arities. |
| [DP121](../Oria/IR/DP121/Syntax.lean) | Structured scoreboard, storage, function, Execute, return, and macro commands. |
| [Artifact](../Oria/Datapack/Artifact.lean) | Output files, metadata, and callback tags, with checked paths and explicit filesystem output. |

Representation tables, closure evidence, demand masks, and allocation plans are metadata
attached to these stages. [Continuations and pattern compilation](continuations.md)
defines the source-to-Cont rules and demand equations.
See [optimization and sharing](optimization.md) for the pass contracts and encoding seam.

## Representation and allocation

Unit occupies zero words. I32, Bool, and payload-free enums occupy one word.
Ordinary payload ADTs, Option, Ref, and runtime NBT values use one pointer word.
Value types expand into scalar products; closed layouts are resolved in dependency order.
Parameters, normal returns, and joins use the same value-width rules.
A function whose grade includes failure adds a leading success word to its return ABI.

The representation table is built from closed schemas and shared with persistent-runtime
generation. Constructor tags, field widths, and pointer-slot classifications are determined
there. Machine lowering emits allocation and projection operations using that table.
See [object values](object-values.md), [value types](value-types.md), and [persistent memory](persistent-memory.md).

Demand propagates across block parameters, calls, and returns. Liveness freezes the
instruction inputs, outputs, live-across values, and call targets. Block-local linear scan
assigns demanded words to reusable registers or stack slots. Call-graph SCCs determine
callee-first preferences; final clobber summaries determine caller saves.
See [register allocation](register-allocation.md) and
[interprocedural allocation](interprocedural-allocation.md).

## Commands and NBT transport

The standard catalog is assembled by [Std.Manifest](../Oria/Std/Manifest.lean).
Command declarations describe signatures and templates; public Std functions accept typed
arguments. The open `ArgCodec` class combines static fragments and typed holes.

Static arguments remain in the command text. Dynamic I32 values use numeric macro fields;
runtime NBT values can use Minecraft's native macro serialization. Mixed compounds and
lists retain static fields while encoding their dynamic parts. Only required holes are
written to the argument compound. [CommandPlan](../Oria/IR/DP121/CommandPlan.lean)
aligns the macro schema with the source operands.

Teleport supports structured selectors, world/relative/local coordinates, host decimals,
angles/facing, and entity destinations. Scoreboard includes objective lifecycle, scores,
operations, presentation, and trigger integration. NumberProvider expressions retain
constructor-derived context summaries; named provider references carry conservative
requirements. Command-family contracts are collected in the
[standard-library guide](standard-commands.md).

[Oria.Nbt](../Oria/Nbt.lean) provides host NBT, SNBT output, typed codecs, construction syntax,
and paths. Runtime `Nbt.Data` values are immutable arena-backed snapshots that can cross
function and ADT boundaries and be explicitly persisted. Native copying preserves tags and
values; entering I32 computation is an explicit operation. See [NBT](nbt.md).

## Execution and validation contracts

An ordinary public invocation owns an ephemeral arena and its data stack. Internal functions
share the arena. Both normal completion and recoverable failure release invocation storage.
Persistent roots and Ref updates require explicit persistent values.
A separately exported collector runs after an ordinary invocation has returned.

A cooperative task owns a workspace across multiple ticks. Parking stores live register
words and the arena cursor; stack slots remain resident. The scheduler resumes the recorded
continuation on the next tick. Collection is excluded throughout that logical invocation.
Ordinary programs without reachable suspension retain the synchronous execution path.
See [cooperative tasks](tasks.md).

`Program.compile` returns `Compiler.CompiledProgram`. Its `.closed` field carries
program-organization contracts; `.certificate` proves each retained body was produced
by the stated compiler function. This is provenance evidence.
Scope and arity constraints are enforced by dependent indices, and parallel transfers
carry a semantic certificate for arbitrary input stores.

Cont and DP121 have reference interpreters. Current behavior is checked by theorem examples,
diagnostics, final-output snapshots, downstream Lake builds, and
[Minecraft integration tests](../integration/datapack/README.md).
End-to-end semantic preservation and the soundness of the complete liveness/caller-save
pipeline have not been proved.

```bash
./scripts/quality
./scripts/gametest
./scripts/rps-test
./scripts/rps-test --language
./scripts/rps-test --admin
./scripts/rps-test --tasks
```

These checks cover specified fixtures and execution modes. They do not establish exhaustive
command-overload coverage, client rendering, or large-program performance bounds.
