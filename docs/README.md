# Oria documentation

Oria constructs typed object programs in Lean and exports Minecraft DP121 datapacks.
The guides below describe the public interfaces and current execution contracts.
The [generated reference](../docbuild/README.md) provides searchable declaration documentation.

## Start here

- [Source programs](source-programs.md): host/object computation, inference, records, and do control flow.
- [Elaboration rules](elaboration.md): host/object dispatch, bindings, results, native paths, recursion, and deriving.
- [Failure and recovery](failure.md): computation exits, effects, lexical recovery, and Option capture.
- [Datapack builder](datapack-builder.md): entries, callbacks, roots, and output configuration.
- [Lake builds](lake-datapacks.md): use Oria as a dependency and export packs with `lake build`.
- [Standard library](standard-commands.md): command results, context, arguments, and command-family guides.
- [Rock-paper-scissors](rock-paper-scissors.md): a complete per-player game.
- [Round ledger](language-acceptance.md): records, persistent state, failure recovery, and control flow.
- [NBT merge sort](merge-sort.md): typed native buffers and cooperative runtime sorting.

## Values and execution

- [Object construction](object-construction.md) and [integer patterns](integer-patterns.md).
- [Object representations](object-values.md) and [runtime recursion](recursion.md).
- [Value types](value-types.md): inline products, physical layout, and correctness theorems.
- [Cooperative tasks](tasks.md): checkpoints, tick-to-tick continuations, fuel, and task workspace.
- [Persistent memory](persistent-memory.md): named roots, explicit promotion, Ref, and manual GC.
- [NBT](nbt.md): derived native documents, typed paths, runtime snapshots, and native macro transport.
- [Global native documents](nbt.md#global-native-documents): typed storage variables and reload semantics.
- [Execute](execute.md): selectors, ordered context changes, conditions, and result receivers.

## Compilation reference

- [Compiler architecture](design.md) and [module structure](structure.md).
- [Continuations, patterns, and demand](continuations.md).
- [Scalar and memory optimization](optimization.md).
- [Register allocation and calls](register-allocation.md).
- [Interprocedural allocation](interprocedural-allocation.md).
- [Lean integration](lean4.md).

## Validation and documentation

- [Integration acceptance](../integration/datapack/README.md): server and downstream Lake suites.
- [Reference-site build](../docbuild/README.md): authoring, preview, and publication.

Use `scripts/quality` for theorem/behavior checks, documentation, and final-output validation.
Run the native suites separately as described in the integration guide.
