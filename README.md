# Oria

Oria is a Lean 4 embedded language that compiles typed programs into Minecraft Java
datapacks. Lean constructs the program; Minecraft executes it. The target is
[Minecraft 26.3, datapack format 121](minecraft-26.3.lock.json).

## Quick start

Copy [lean-toolchain](lean-toolchain) into a new project, then create `lakefile.toml`:

```toml
name = "my-pack"
defaultTargets = ["Game"]

[[require]]
name = "oria"
git = "https://github.com/CAIMEOX/OpenOria.git"
rev = "main"

[[lean_lib]]
name = "Game"
defaultFacets = ["datapack"]
```

Create `Game.lean`:

```lean
module

import Oria
import Oria.Datapack
meta import Oria
meta import Oria.Datapack

namespace Game

open Oria Oria.Std Oria.Datapack

@[mcfunction]
def announce : Prog (Tellraw.grade .all).handled Unit :=
  (Tellraw.text .all "Hello from Oria!").ignore

@[datapack]
def game : Spec := build {ns := "hello"} do
  onLoad announce.ref
  entry "hello" announce.ref

end Game
```

Build the datapack:

```bash
lake update
lake build
```

Copy `.lake/build/datapacks/Game/Game.game/` into the world's `datapacks/` directory.
Reload the world, then run `/function hello:hello`.

`@[mcfunction]` defines an object function. `@[datapack]` collects its reachable
dependencies and produces the pack. Named calls use `f.call`; ordinary Lean calls
expand code during construction. `Val A` describes a runtime value, and `Prog g A`
describes a computation; `g` records its effects and required command context. Here, `ignore`
allows an empty player selection to complete normally.

The [Lake guide](docs/lake-datapacks.md) covers dependency configuration, module selection,
and incremental exports. The [datapack builder](docs/datapack-builder.md) covers entries,
load/tick callbacks, resources, and persistent roots.

## User documentation

Start with the [documentation index](docs/README.md) or browse the
[standard library guide](docs/standard-commands.md).

- [Source programs](docs/source-programs.md) and [elaboration rules](docs/elaboration.md):
  host/runtime computation, inference, records, patterns, and control flow.
- [Failure and recovery](docs/failure.md) and [Execute](docs/execute.md):
  command composition, effects, and execution-context requirements.
- [NBT](docs/nbt.md), [persistent memory](docs/persistent-memory.md), and
  [value types](docs/value-types.md): typed documents, paths, storage, and object layout.
- [Cooperative tasks](docs/tasks.md): computations that park and resume across ticks.

Runnable examples include [rock-paper-scissors](docs/rock-paper-scissors.md),
[RoundLedger](docs/language-acceptance.md), and [NBT merge sort](docs/merge-sort.md).
[StandardLibrary.lean](Oria/Examples/StandardLibrary.lean) contains checked command examples.
See [reference-site instructions](docbuild/README.md) to build the searchable API documentation.

## Compiler and semantics

```text
Val / Prog → Tree → Cont → Machine → DP121 → Artifact
```

- [Architecture](docs/design.md) and [module structure](docs/structure.md):
  compilation stages, representation contracts, and implementation responsibilities.
- [Continuations and pattern compilation](docs/continuations.md):
  ANF lowering, decision trees, joins, and demand analysis.
- [Optimization](docs/optimization.md) and [register allocation](docs/register-allocation.md):
  scalar/memory facts, physical locations, call frames, and code sharing.
- [Lean integration](docs/lean4.md): typed construction, quotation, and trusted interfaces.

## Validation

From an Oria checkout, run `./scripts/quality` for proofs, diagnostics, final-output checks,
documentation examples, and downstream Lake builds. The
[integration guide](integration/datapack/README.md) describes native Minecraft suites,
their prerequisites, and coverage boundaries.
