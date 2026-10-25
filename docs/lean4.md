# Lean integration

Lean is Oria's host language. It supplies source syntax, namespaces, type checking,
metaprogramming, and package builds. Oria's object language describes computations
executed by Minecraft.

## Host and object computation

`Val A` describes an object expression, and `Prog g A` describes ordered object computation.
An ordinary Lean value such as `Nat`, `String`, or `Float` can participate in host computation
while constructing those expressions. A `Val` is not an observed runtime Lean value.

Ordinary calls construct and combine program fragments. The generated saturated `f.call`
creates an object call to a named `@[mcfunction]` definition.
`Prog.fix` describes runtime recursion by constructing a finite recursive Tree.
See [source programs](source-programs.md) and [runtime recursion](recursion.md).

The expected type selects Oria's ordinary-do elaborator.
Host Bool/Prop conditionals and host matches execute during construction.
`Val Bool` conditionals and matches over object values generate runtime control flow.
`=` remains Lean propositional equality; object scalar comparisons use `==` and the
relational operators.

## Checked domain literals

Expected domain types accept validated string literals:

```lean
def points : Command.Objective := "points"
def loot : ResourceId := "demo:loot"
def path : Datapack.PublicFunctionPath := "game/start"
```

The same mechanism applies to record fields and arguments, including
`Scoreboard.get .self "points"` and `{ns := "demo"}`.
A literal without an expected domain type retains Lean's String interpretation.
Annotate lists or branches when they need domain-valued elements.

[Data.StringLiteral](../Oria/Data/StringLiteral.lean) uses a scoped Lean environment extension.
Domain modules register their existing smart constructor:

```lean
attribute [string_literal ResourceId.ofString] ResourceId
```

The constructor takes a String followed by default proof arguments.
Type aliases are matched by definitional equality; ambiguous rules report a diagnostic.
Computed String inputs use `parse` or a constructor supplied with existing validity evidence.

Selectors use semantic constructors such as `.self` and structured filters.
Raw selector text uses an explicit parsing interface.
`Inline` explicitly denotes command text.

## Source types and regions

`Object A code` relates a source type to a logical object type.
Deriving records parameterized constructor fields and publishes typed construction interfaces.
Collection instantiates closed schemas from concrete type arguments.
See [object construction](object-construction.md) and [object values](object-values.md).

`Val A r` and `Prog g A r` keep region relations in Lean types.
Reification constructs one function body; generated calls retain the source region relation.
Region markers are erased from the object ABI.
An initializer registered with `@[root]` uses the same declaration machinery.

The representations of values, computations, captured definitions, return destinations,
and typed native paths use [sealed carriers](../Oria/Data/Sealed.lean). The carrier's
opaque implementation supplies total wrapping/unwrapping operations with a kernel-checked
round-trip equation. Its key retains source and region identity. Ordinary structure
elimination therefore yields an abstract payload whose identity must be preserved.
`Object` instances also retain an abstract source-to-code witness.

Trusted elaborators use a small private kernel ABI for generated constructors, projections,
and calls. On the pinned Lean version, those opaque ABI declarations are exported under
their private names with a declaration-local `backward.privateInPublic` setting. Ordinary
name resolution in `module` source files keeps them private. Explicit `import all`, direct use of compiler-private
names, and custom environment mutation belong to the trusted extension boundary.
This arrangement accommodates Lean's current compilation-type restriction on hidden
type aliases while retaining the public `Val` and `Prog` interfaces.

## Metaprogramming facilities

Oria uses Lean's standard representations for generated code:

| Representation | Facility |
| --- | --- |
| Surface declaration syntax | Syntax quotation and `Lean.Quote` |
| A computed host value embedded in core syntax | `Lean.ToExpr` |
| Typed combinations of core expressions | Qq's `Q(...)` and `q(...)` |
| A local continuation embedded in do syntax | Lean's `doElabToSyntax` interfaces |

[Meta.Quote](../Oria/Meta/Quote.lean) provides standard instances for object types and type IDs.
Declaration generation uses hygienic syntax quotation, typed expressions, and the private
compiler ABI for sealed values.
Generated declarations are checked by Lean.

Qq assists typed construction of `Lean.Expr`; its quoted expressions are not independent
kernel typing certificates. Unknown expressions need type inspection before typed quotation.
Oria identifies computation type heads with structural core-expression matching and
normalization at the relevant elaboration boundary.

Local `exprToSyntax` values belong to their elaboration context.
Templates that cross declaration elaboration use independent syntax quotation.
The [Lean quotation reference](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Defining-New-Syntax/)
and [Qq](https://github.com/leanprover-community/quote4/tree/v4.31.0-rc2) describe these facilities.

## Interface and validation boundaries

`Val`, `Prog`, and the reification carrier are abstract user interfaces.
Compiler modules access their representations through audited internal imports.
Lean module privacy controls ordinary name access; trusted compiler and metaprogramming
code belongs to the implementation boundary.

Scope and arity indices constrain object IR construction.
Lean diagnostic tests use `#guard_msgs`; semantic interface laws use propositions and theorems.
[Compiler architecture](design.md) distinguishes these contracts from whole-pipeline
semantic preservation.
