# Module structure

Oria separates source construction, Lean elaboration, IR contracts, compilation algorithms,
command libraries, and artifact output. The public DSL names `Val`, `Prog`, and `Object`
remain in the `Oria` namespace.

## Import entry points

| Import | Purpose |
| --- | --- |
| `Oria` | Object construction, syntax extensions, and the standard library. |
| `Oria.Language` | Values, computations, failure recovery, regions, roots, Ref, and source-type correspondence. |
| `Oria.Meta` | Elaboration, declaration attributes, and object deriving. |
| `Oria.IR` | Stage contracts, representation metadata, and IR observations. |
| `Oria.Compiler` | Linking, lowering, analysis, and optimization. |
| `Oria.Datapack` | Typed entry registration, artifact compilation, and file output. |
| `Oria.Nbt` | Host NBT, paths, SNBT formatting, and codec deriving. |
| `Oria.NumberProvider` | Host numeric-expression DSL and DP121 encoding. |

Source modules normally use `import Oria` and `meta import Oria`.
Datapack declarations additionally import `Oria.Datapack` in both phases.
The [Lake guide](lake-datapacks.md) describes downstream package builds.

## Directories

| Directory | Responsibility |
| --- | --- |
| `Language` | Public construction interfaces and source/object type correspondence. |
| `Meta` | Lean syntax elaboration, attributes, deriving, environment registries, and collection. |
| `IR/Common` | Logical types, schemas, signatures, references, scopes, and primitive operations. |
| `IR/Tree`, `IR/Cont` | Source-shaped and continuation representations. |
| `IR/Representation` | Word widths, constructor layouts, pointer-slot kinds, and persistent-copy graphs. |
| `IR/Machine`, `IR/DP121` | Word-level CFG and structured target contracts. |
| `IR/Program`, `IR/Catalog` | Collected members, dependency closure, and catalog contracts. |
| `Compiler` | Algorithms producing or transforming stage products. |
| `Command` | Command signatures, templates, open codecs, selectors, and Execute context transformations. |
| `Std` | User-facing commands and shared argument types. |
| `Nbt`, `NumberProvider` | Host data and numeric descriptions with their encoders. |
| `Runtime` | Memory identities and the Prog-generated mark-sweep collector. |
| `Datapack` | Resources, typed registration, artifact assembly, and output. |
| `Effect`, `Data` | Grade algebra, indexed containers, and validated literals. |
| `Proofs`, `tests`, `integration` | Theorems, behavior/diagnostic checks, final-output assertions, and native acceptance. |

## Dependency direction

Meta reads Lean's environment and produces a finite collected program.
The pure compiler consumes that program. IR modules define the contracts consumed by
algorithms, together with their queries, semantics, and formatting.

Tree-to-Cont lowering performs ANF conversion and delegates pattern matrices to
`Compiler/Lower/Pattern`. Cont simplification uses typed substitution and known-constructor
facts. A subsequent Cont memory pass forwards native scalar reads and annotates established
selection checks using structured paths and conservative alias information. Machine lowering
preserves those descriptors, consumes the prepared representation table, and emits word-level
operations and CFG edges.

Machine control-flow optimization threads jumps, merges uniquely owned successors, removes
unreachable blocks, and turns eligible self-tail calls into entry backedges.
Bits analysis and condition selection expose direct target predicates.
Demand and liveness produce the facts consumed by register allocation and target encoding.

DP121 lowering is divided by target responsibility: arithmetic, calls, parallel transfers,
stack access, command transport, Execute, heap access, NBT copying, and persistent runtime.
The Task module reuses operation emission and allocation metadata to generate resumable
frames, live-register snapshots, and wakeup dispatch. Its cost model consumes structured
physical commands, so macro helpers and stack transfers contribute to region bounds.
The same allocation metadata governs parameter moves, returns, and caller saves.
`Datapack.Artifact` consumes target call-closure evidence and assembles files.

`Runtime.GC` receives prepared descriptor scanners and root identities. It constructs
ordinary Prog definitions that join collection before closure checking and follow the
same compilation stages as user definitions.
The prepared representation table is shared by this generator and Machine lowering.

Std assembles the default command catalog through `Std.Manifest`.
Command authors reuse `Std.Command.Arg` and the open `ArgCodec` interface.
`Std.Compute.Number` connects NumberProvider to Compute.
Host NBT formatting and runtime-memory construction reuse `Oria.Nbt`.

## Validation

```bash
./scripts/quality
```

The gate builds the library and theorem/behavior modules, validates public documentation,
checks final artifact output, exercises a downstream Lake package, and audits internal
imports and module visibility. Server suites and their scope are described in the
[integration guide](../integration/datapack/README.md).
