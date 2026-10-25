# Integer literal patterns

Object matches accept integer constants, variables, and wildcards for `Val Int32`:

```lean
@[mcfunction]
def classify (n : Val Int32) : Prog .pure Int32 := do
  match n with
  | -1 => return 10
  | 0 => return 20
  | n => return n
```

Constants can occur inside ADTs and alongside other discriminants:

```lean
@[mcfunction]
def choose (x : Val (Option Int32)) (y : Val Int32) : Prog .pure Int32 := do
  match x, y with
  | .some 0, _ => return 10
  | .some n, 0 => return n
  | .some (-1), _ => return 20
  | _, y => return y
```

Rows retain source order. The first matching row supplies the result. Wildcard and variable
rows cover the remaining integer domain; an uncovered residual path is a compile error.
Rows that cannot be selected are reported as redundant. The I32 domain is not enumerated
during coverage analysis.

## Literal values

Integer patterns use Lean's `Int32` values, including its modulo-2^32 conversion of numerals.
The signed range is -2147483648 through 2147483647. Both endpoints and negative constants
are supported. For example, `4294967295` and `-1` denote the same I32 value, so two otherwise
identical rows using those constants are redundant. This agrees with object integer literals
and equality comparisons. Use signed-range notation when writing a pattern for clarity.

Lean elaborates and normalizes each pattern. For an I32 constant, the frontend reads the
normalized value through `Int32.toUInt32`, `UInt32.toNat`, and Lean's literal-value inspection.
Lean's internal integer constructor tree does not enter the object IR.

## Representation and lowering

The typed source-pattern constructor is:

```lean
Pattern.i32 : Int32 → Pattern .i32 []
```

An integer pattern introduces no bindings. Catalog closure and dependency inspection treat
it as a scalar leaf; Tree formatting prints its signed value.

Tree → Cont uses constant specialization in the existing pattern matrix compiler. Integer
constants act as nullary alternatives, following
[Le Fessant and Maranget's treatment of constant patterns](https://pauillac.inria.fr/~maranget/papers/opat/pat002.html).
The general decision-tree scheme is described in
[Maranget, *Compiling Pattern Matching to Good Decision Trees*](https://www.cs.tufts.edu/~nr/cs257/archive/luc-maranget/jun08.pdf).
For the next tested constant k:

1. The equal edge retains rows beginning with k, a wildcard, or a variable and removes that
   column. A variable receives the original discriminant.
2. The unequal edge removes rows beginning with k and continues with the residual matrix.
3. Both edges preserve row order and contribute their selected source-row identities to
   redundancy checking.

The generated Cont uses an existing `binary .eq` operation followed by `branch`. Typed
renamings lift the remaining discriminants and row arguments beneath the comparison result.
Each source RHS is already a join and remains shared. Cont, Machine, register allocation,
and DP121 retain their existing instruction sets and representations.

## Verification

`Oria.Proofs.IntegerPattern` compiles source definitions and evaluates the resulting Cont
with the existing reference semantics. It covers signed endpoints, negative values, variable
fallbacks, multi-column priority, nested Option payloads, missing coverage, and redundant rows.
These checks run in `scripts/quality`.

`scripts/rps-test` exercises the game and a separate cross-function nested-literal
case on the pinned Minecraft server. The acceptance pack uses register budget 6, covering
stack arguments, payload reads, comparisons, and invocation cleanup.
