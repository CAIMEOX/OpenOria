# Value types and layout correctness

`@[value_type]` represents a closed, single-constructor object by its scalar fields.
For fixed-size arithmetic, a three-limb value occupies three words. Its construction,
projection, and immutable update require no arena allocation.

```lean
@[value_type]
public structure Triple where
  x : Int32
  y : Int32
  z : Int32
  deriving Oria.Object

@[mcfunction]
def increment (v : Val Triple) : Prog .pure Triple := do
  return {v with x := v.x + 1}
```

The attribute precedes deriving. The usual `Val A`, object constructors, record syntax,
field projection, and matching remain available. Runtime signatures have closed types.
A parameterized declaration is checked separately at each reachable closed instance.

## Eligibility and representation

An eligible declaration has exactly one constructor. Its fields are Unit, Bool, I32,
payload-free enums, or other eligible value types. Unit contributes zero words; a nested
product contributes all its words. A pointer-containing field is rejected, including
ordinary Option, Ref, runtime NBT, and ordinary boxed ADTs.
An inline dependency cycle is rejected because its layout would be infinite.

The frozen representation table assigns a form to each closed nominal type:

\[
F(A)\in\{\mathsf{Enum},\mathsf{Boxed},\mathsf{Product}(n)\}.
\]

For a value constructor with fields \(A_1,\ldots,A_k\), we define

\[
w(A)=\sum_{i=1}^{k}w(A_i),\qquad
o_i=\sum_{j<i}w(A_j).
\]

Field i occupies the half-open range \([o_i,o_i+w(A_i))\). A zero-field value has width
zero; a one-word wrapper preserves its field word. The logical constructor has no stored
tag. Matching its single constructor transfers control directly to the selected body.

The solver uses Lean's dependency-first SCC implementation. Ordinary boxed fields stop
inline expansion. The resulting table supplies widths and pointer classifications to
Machine lowering, persistent preparation, and target emission.

## Calls, registers, and memory

Tree and Cont retain logical object types. Cont-to-Machine lowering expands values at
construction, projection, calls, returns, and joins. Machine demand and liveness operate
on individual words; unused fields can disappear across function boundaries.
Register allocation places the demanded words in registers or fixed frame slots.

A value has no runtime address or identity. Copying its words preserves value semantics.
Spilling stores words in the current activation's NBT stack slots. A callee returns all
demanded words before its frame is popped. The first two demanded return words use result
registers; remaining words use the callee's result area.

A boxed parent embeds a value field directly in its payload. Its descriptor expands by
the same number of scalar slots. A Ref embeds its element representation in its mutable
payload; `Ref.get` produces a snapshot of those words, so a later `Ref.set` cannot change
an earlier local value.

`persist` is an identity on scalar-only representations. A boxed parent still promotes
its pointer fields. The 30-slot limit applies to each physical persistent heap payload,
after expansion. An inline 31-word value may be a root, but a boxed constructor or Ref
containing those 31 words exceeds the limit.

Persistent ABI 2 stores every root as a word list, including `[x]` and `[]`. Initialization
publishes all return words before releasing the initializer's call frame. Root scanning
uses `(root identity, word offset)` entries derived from pointer classifications.
Scalar numbers are never interpreted as pointers by value or sign alone.
The stored schema includes representation hints and resolved layouts; register budgets
and allocation locations do not affect that schema.

## Verified layout interface

[Representation.Packing](../Oria/IR/Representation/Packing.lean) defines the pack and
unpack operations used by Machine lowering. Its kernel-checked `layout_correct` theorem
states, for every frozen table, field list, word type, field vectors x, and word vector v:

\[
\mathsf{unpack}(\mathsf{pack}(x))=x
\quad\land\quad
\mathsf{pack}(\mathsf{unpack}(v))=v.
\]

The theorem covers zero-width fields, nested expansion, and arbitrary word values.
`project_pack` establishes that projection recovers the original field vector.
`descriptor_correct` establishes that each field's slice of the payload descriptor equals
that field's own word-kind vector. The implementation shares the frozen widths across
value transport and descriptor construction.

These are layout-interface theorems. A complete compiler theorem would use a relation
\(\mathcal R_T\) between logical values/heaps and physical word vectors/heaps under table T:

\[
\mathcal R_T(s,m)\land s\longrightarrow s'
\quad\Longrightarrow\quad
\exists m'.\;m\longrightarrow^{*}m'\land\mathcal R_T(s',m').
\]

Such a theorem requires a well-formed closed-table premise and step semantics for calls,
allocation, projection, root replacement, and Ref mutation. The layout lemmas discharge
field transport and descriptor slicing. Additional obligations include correctness of
the SCC layout solver, demand/liveness, frame transfers, promotion, and GC reachability.
Those full preservation results have not been proved. In particular, a round-trip theorem
alone cannot justify an arbitrary layout table or a register allocator.

## Acceptance and costs

[ValueTypes](../Oria/Proofs/Fixtures/ValueTypes.lean) compiles source programs through the
complete pipeline with register budgets 128 and 6. Native GameTest checks nested products,
recursive multiword calls, sparse return demand, failure exits and Option transport, root initialization/replacement, Ref
snapshot semantics, boxed parents, collection, reload, and invocation cleanup.
The arithmetic-only final artifact is checked for absence of arena append operations.
Layout checks cover cycles, pointer fields, and the expanded persistent-payload limit.

Word expansion removes object allocation and dynamic pointer lookup for eligible values.
It can increase register pressure, argument copies, and spill traffic. The attribute
specifies representation; whether it improves a particular workload requires measurement.
Big-integer carries, limb bounds, and overflow remain arithmetic correctness obligations.

## References

The component-wise calling convention follows the approach used by
[OxCaml unboxed products](https://oxcaml.org/documentation/unboxed-types/intro/) and
[GHC unboxed tuples](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/primitives.html#unboxed-tuples).
Addressable stack objects require a separate escape discipline, as illustrated by
[OxCaml regions](https://oxcaml.org/documentation/stack-allocation/reference/).
Oria's stack slots contain copied words and do not introduce an addressable object region.
