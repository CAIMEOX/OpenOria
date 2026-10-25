# Runtime recursion

A local `let rec` in object `do` constructs a first-order recursive function when all its
parameters are Val carriers and its result is Prog. Write its parameter types, result,
and grade. These remain fixed within the recursive definition.

```lean
@[mcfunction]
def sum (n : Val Int32) : Prog .pure Int32 := do
  let rec go (i acc : Val Int32) : Prog .pure Int32 := do
    if i <= 0 then return acc
    go (i - 1) (acc + i)
  go n 0
```

Each runtime recursive binding declares one function. Host signatures use Lean recursion
and its termination checker, including Nat-parameter generators that return Prog.
See [elaboration rules](elaboration.md#local-recursion-and-iteration).

`Prog.fix` is the underlying builder. Its conceptual interface is
`Prog.fix (body : F → F) : F`, where F is a Prog result or a telescope of Val arguments
ending in Prog. It also supports host generator code using a complete expected arrow type.

## Construction and scope

The builder creates a recursive binding and quotes the body once.
The supplied `recur` function constructs symbolic calls, producing a finite Tree.
Ordinary Lean recursion instead runs while constructing the program.

[Lower.Scope](../Oria/Compiler/Lower/Scope.lean) lifts recursive definitions to named
first-order helpers and passes lexical captures as explicit arguments.
Nested fix and Execute bodies share this mechanism. Demand removes unused captures.
Recursive references are closed under the same finite program catalog as other calls.

Multiple state parameters enter the Machine argument telescope directly.
A recursive call is a computation and cannot become a runtime higher-order value.

## Effects and regions

`program.weaken (h := upper) proof` explicitly enlarges its grade under a `Grade.Below` proof,
preserving its result region. Closed grades can use the default proof argument.
Tree retains the evidence and ANF erases it, with no target instruction.

Region-polymorphic source signatures can preserve the region of an existing value.
Region markers do not enter the object ABI. See [persistent memory](persistent-memory.md).

## Execution

Ordinary recursion uses the data-call protocol: spill slots and required caller registers
are preserved in activation frames, while internal calls share the entry's arena.

Machine optimization turns a self call immediately returning the complete unchanged
result tuple into an entry backedge. The edge uses parallel argument transfer and keeps
the current activation frame. Cross-function tail calls use the ordinary call protocol.

Recursion may diverge. A pure grade describes effects, not termination.
Unused-result calls retain their execution position. Minecraft execution limits still apply.

Cooperative tasks can place `Task.checkpoint` in a recursive body and register the outer
Unit computation with `Datapack.task`. Safe boundaries break executing cycles for cost
analysis. Optimized self-tail backedges retain their frame; other resumable calls store an
explicit return continuation. See [cooperative tasks](tasks.md).

## Acceptance

[RecursionRuntime](../Oria/Proofs/Fixtures/RecursionRuntime.lean) contains sum, Fibonacci,
lexical captures, nested recursive helpers, and effectful self-tail recursion.
`scripts/gametest` executes them with register and all-stack configurations, checks numeric
results, and checks arena/stack cleanup.
[Recursion](../Oria/Proofs/Recursion.lean) checks helper sharing, non-tail calls, spill demand,
and self-tail backedges.

The source/object distinction corresponds to the separation of function calls and joins
in [Lean LCNF](https://github.com/leanprover/lean4/tree/v4.31.0-rc2/src/Lean/Compiler/LCNF).
