# Building the documentation

Standard library guides, declaration contracts, and examples live in Lean source files.
[doc-gen4](https://github.com/leanprover/doc-gen4/blob/v4.31.0-rc2/README.md)
generates searchable HTML from them. The documentation project reads the current Oria
working tree through a path dependency and shares its `.lake/packages` directory.
This directory's Lake configuration and manifest manage the generator's dependencies.

## Build and preview

Run from the Oria repository root:

```bash
./scripts/docs
python3 -m http.server 8031 --bind 127.0.0.1 --directory docbuild/.lake/build/doc
```

Open <http://127.0.0.1:8031/OriaDocs.html>. The standard library guide is at
<http://127.0.0.1:8031/Oria/Std.html>. Search requires serving the pages over HTTP.
The script sets `DISABLE_EQUATIONS=1` to hide implementation equations while retaining
types, documentation, and source links.

Lake incrementally updates module information, then doc-gen4's `fromDb` command renders
the HTML. This release's `:docs` facet can reuse an old HTML marker after module information
changes. Explicit rendering ensures that import and documentation changes reach the pages.

The first build downloads the generator and its dependencies. When upgrading Lean, update
this directory's `lean-toolchain` and the doc-gen4 version in `lakefile.toml`, then run:

```bash
lake -d docbuild update
```

Also update the documentation manifest when Oria's dependencies change. Generated HTML lives
in `docbuild/.lake/build/doc/`, which Git ignores. Publish the contents of that directory.
Source links point to the Git commit recorded at build time; commit and push the corresponding
source before publishing.

## GitHub Pages

The [Docs workflow](../.github/workflows/docs.yml) builds the pinned documentation project
on pushes and pull requests to `main`. Main-branch runs publish the generated site to
<https://caimeox.github.io/OpenOria/>. The guide starts at
<https://caimeox.github.io/OpenOria/OriaDocs.html>.
To rebuild manually, select **Actions > Docs > Run workflow** on `main`.

Repository setup requires **Settings > Pages > Build and deployment > Source: GitHub Actions**.
Deployment uses the built-in `GITHUB_TOKEN` and an OIDC identity. No personal token or
repository secret is needed. The `github-pages` environment controls deployment approvals
if maintainers add protection rules. Pull-request runs build and upload artifacts; only
`main` can deploy.

CI caches compiled library dependencies and the root package's Lean artifacts. It rebuilds
the documentation database and HTML from the current import graph on every run, so removed
modules leave the search index and navigation.

## Source layout

- [Oria.Std](../Oria/Std.lean): usage guide, results, context, and argument stages.
- [Oria.Std modules](../Oria/Std): contracts for commands, argument codecs, and constructors.
- [Oria.Examples.StandardLibrary](../Oria/Examples/StandardLibrary.lean): composed examples
  using `@[mcfunction]`, which constructs and checks Tree during compilation.
- [OriaDocs](OriaDocs.lean): site entry point and cross-module navigation.
- [docs](../docs): compiler design, memory protocols, and implementation notes.

## Authoring and checking

Write public documentation in English. Command contracts describe argument meanings,
initialization requirements, native success conditions, integer results, context requirements,
effect bounds, and static/dynamic argument handling. NBT reads also document match cardinality,
missing values, copying, and numeric conversion. Explain type-level constraints in the
context of their use.

Module guides use Markdown `/-! ... -/`; declaration docstrings use Verso `/-- ... -/`.
Std modules set:

```lean
set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true
```

Use `{name}` to reference an existing Lean declaration and `{lit}` for Minecraft text.
Lean checks examples inside `lean` fences. Put examples with named object functions and
inter-function calls in `Oria.Examples.StandardLibrary`. Module Markdown uses
`[label](##Fully.Qualified.Name)` for cross-references. The current doc-gen4 reads Markdown
module guides and converts Verso declaration docstrings to HTML.

```bash
./scripts/check-docs
./scripts/quality
```

`check-docs` uses Lean's built-in `linter.missingDocs` and rechecks every Std source file and
the composed examples with warnings treated as errors. It checks missing documentation,
Verso references, and example types. Server acceptance tests check actual Minecraft results
and command effects. The full quality gate includes this documentation check.
