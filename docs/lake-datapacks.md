# Building datapacks with Lake

Oria registers a `datapack` facet for modules, libraries, and packages. Lake builds the
selected Lean modules, then exports the artifacts already checked by `@[datapack]`.
Source imports determine the compilation dependencies. The exporter reads each module's
own declarations, including private declarations.

## A downstream project

Use the Lean version in Oria's `lean-toolchain`. A project can depend on Oria with an
ordinary TOML configuration:

```toml
name = "my-game"
defaultTargets = ["Game"]

[[require]]
name = "oria"
git = "https://github.com/CAIMEOX/OpenOria.git"
rev = "main"

[[lean_lib]]
name = "Game"
defaultFacets = ["datapack"]
```

Place the program in `Game/Pack.lean`:

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
  (Tellraw.text .all "Welcome!").ignore

@[datapack]
def game : Spec := build { ns := "my_game" } do
  onLoad announce.ref
```

Import it from `Game.lean`:

```lean
module
import Game.Pack
```

Run:

```bash
lake update
lake build
```

The installable datapack directory is
`.lake/build/datapacks/Game.Pack/Game.game/`. Copy that directory into a world's
`datapacks/` directory. Resource names inside it come from `Spec.settings.ns` and the
registered public entries; the output folder name identifies the Lean declaration.
Multiple declarations in one module receive separate output directories.

## Selecting a build

| Command | Selection |
| --- | --- |
| `lake build +Game.Pack:datapack` | Declarations in one module. |
| `lake build Game:datapack` | Declarations in the library's selected modules. |
| `lake build :datapack` | Declarations in the root package's Lean libraries. |
| `lake build` | The package's default targets and each library's default facets. |

The module and library forms also work with a library's ordinary default facets. Add
`defaultFacets = ["datapack"]` to make datapack export part of a bare `lake build`.
Each package owns its output under its configured build directory, including when Oria
is a Git or local-path dependency. Declarations in imported modules are exported by those
modules' own facets.

## Incremental output

Lake traces the module's Lean artifacts and the Oria exporter. Repeating an unchanged
build preserves generated file timestamps. Changes to imported code rebuild the affected
module and its datapacks. A missing generated file also causes export to run again.

Each module's output directory contains a `manifest.json` inventory. Updating a pack
replaces its generated files and removes previous files that are absent from the new
artifact. Removing a declaration removes its generated files. Files outside this inventory
are preserved. The installable pack is the declaration's subdirectory, while the inventory
and Lake trace remain in the module's output directory.

`Artifact.writeTo` remains the explicit IO interface for exporting to a new or empty
destination. Lake's facet manages incremental output separately.

## Acceptance

`scripts/lake-test` builds an independent consumer package through the public Lake commands.
It checks initial export, private declarations, cached builds, imported-definition changes,
missing-file recovery, renamed entries, and declaration removal. These filesystem and
build-system behaviors complement the compiler's typed certificates.

The implementation uses [Lake's custom facet facilities](https://github.com/leanprover/lean4/blob/v4.31.0-rc2/src/lake/README.md#defining-new-facets)
and the same executable-backed module-facet pattern as
[doc-gen4](https://github.com/leanprover/doc-gen4/blob/v4.31.0-rc2/lakefile.lean).
