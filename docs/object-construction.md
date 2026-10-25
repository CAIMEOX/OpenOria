# Type-directed object construction

An object computation can use its source datatype's constructor names:

```lean
public inductive Box where
  | mk (value : Int32)
  deriving Oria.Object

def boxed (n : Val Int32) : Prog .pure Box := Box.mk n
def boxed' (n : Val Int32) : Prog .pure Box := .mk n
```

The expected `Prog .pure Box` selects object construction. The field is checked as
`Val Int32`. When the expected type is the host type `Box`, `Box.mk` retains its ordinary
Lean meaning. Construction is a computation represented by `Tree.Prim.construct`.
Its logical grade is pure; the backend chooses its physical representation and allocation.

## Checking and synthesis

A qualified constructor supplies its datatype in an Oria action position:

```lean
def example (n : Val Int32) : Prog .pure Box := do
  let b ← Box.mk n
  return b
```

A leading-dot constructor uses an expected datatype. A binding annotation can supply it:

```lean
def example (n : Val Int32) : Prog .pure Box := do
  let b : Val Box ← .mk n
  return b
```

Without that annotation, `let b ← .mk n` requires more information. Subsequent uses of `b`
do not select a constructor family. This follows the checking/synthesis distinction in
[Dunfield and Krishnaswami, *Bidirectional Typing*](https://arxiv.org/abs/1908.05839):
an unannotated binding synthesizes its RHS type; an annotated constructor can be checked
against the supplied value type.

An arrow binding receives the normal value of its RHS. Its annotation fixes the source
datatype used to resolve constructors. A failing RHS leaves through the computation's failure
exit; `Prog.attempt` explicitly converts completion into Option data.

## Returning a constructed value

`return .mk n` constructs the object and then returns it:

```lean
def example (n : Val Int32) : Prog .pure Box := do
  return .mk n
```

Tail constructors in ordinary object computations can be written directly as `.mk n`.
Constructor fields take existing `Val` expressions. Bind a nested construction before
passing its result as another constructor field or a function argument. Construction
produces the ordinary region guarantee; obtaining a persistent object requires `persist`.
Existing persistent values can be passed into ordinary object fields through the established
region-forgetting coercion.

## Implementation and verification

Structures also support field projection and immutable record notation. A projection
retains its source region, while a reconstructed record has the ordinary region guarantee.
See [source programs](source-programs.md#records-and-regions) for construction, update,
and the Tree/Cont projection contract.

Object derivation records each canonical source constructor and its generated typed builder
in the existing object registry. `Oria.Meta.Elab.Constructor` selects that builder and delegates
name resolution, application arguments, implicit parameters, and parentheses to Lean facilities.
Leading-dot lookup is restricted to the expected datatype's constructors. Option uses its
registered builders. Host functions and host-typed bindings retain Lean's meaning. Within
object `do`, a `Val`-typed `let x := e` creates a shared object binding; see the
[elaboration rules](elaboration.md#identifier-bindings).

Lean's leading-dot notation uses the outer expected type's namespace. Oria's source type is
an argument of `Prog`, so its elaborator supplies the source-constructor lookup and preserves
the existing typed construction interface. The representation and lowering passes consume
the same Tree operations.

`Oria.Proofs.Constructors` proves definitional equality with the explicit builders using `rfl`,
checks imported metadata and Tree equality, and exercises diagnostics for missing type
information, invalid fields, incomplete applications, and region mismatches. The
rock-paper-scissors example uses the shorthand in its pattern branches and runs through
the native server acceptance suite.
