# Interprocedural register allocation

Register allocation runs on Machine's word-level control-flow graph during DP121 lowering.
The block-local interval allocator is shared by every function. Calling relationships
determine the order in which its register preferences are chosen.

## Callee-first allocation

Demand propagation runs first. Liveness records every call point, including the body
function of an Execute scope. The allocator reads those records to construct a call graph;
it reuses the existing intervals when assigning locations.

The graph is decomposed with
[Lean's strongly connected component utility](https://github.com/leanprover/lean4/blob/v4.31.0-rc2/src/Lean/Util/SCC.lean).
Its callee-first component order places an acyclic chain `A -> B -> C -> D` in allocation
order `D, C, B, A`. A caller therefore receives its callees' completed parameter locations
and transitive register-use summaries. This follows the register-mask propagation used by
[LLVM's IPRA](https://llvm.org/doxygen/RegUsageInfoPropagate_8cpp_source.html).

Let `H(f)` be the conservative set of ordinary registers used by a function's allocated
blocks, `A(f)` its demanded entry-parameter registers, and `W(f)` its transitive summary:

\[
W(f)=H(f)\cup\bigcup_{f\to g}\left(A(g)\cup W(g)\right).
\]

For a live interval `v`, the preference cost of a free register `r` counts the calls that
would require preserving `v`:

\[
\operatorname{cost}(v,r)=
\sum_{c:\,v\in\operatorname{LiveAcross}(c)}
\mathbf{1}\!\left[r\in A(\operatorname{callee}(c))\cup W(\operatorname{callee}(c))\right].
\]

The interval allocator chooses a free register with the lowest cost. It still reuses
expired locations and spills when the register pool is exhausted. The configured budget
includes six fixed scratch/return registers, so a budget of 128 provides 122 ordinary
value registers.

## Recursive components and final saves

Every member of a recursive component reaches the other members. Its preference summary
unites the component's seed locations and the completed summaries of outgoing callees.
All members are allocated against this frozen view. The completed component is then
summarized for its callers.

After allocation, the existing global fixed-point calculation independently recomputes
the final summaries from the actual locations. At call point `c` targeting `g`, the saved
registers are:

\[
\operatorname{Saved}(c)=
\operatorname{RegLoc}(\operatorname{LiveAcross}(c))
\cap\left(A(g)\cup W(g)\right).
\]

This final calculation governs preservation. Preference summaries govern allocation
quality. Caller values already in stack locations remain in their own frames. A call
creates a data frame when its spill, saved-register, or overflow-result area is needed.
The existing calling convention and typed location certificates are shared by acyclic
and recursive programs.

## Examples and acceptance

[Function call examples](../Oria/Examples/Calls.lean) retain values across explicit named
calls. Their construction-time `carry` helper generates the repeated arithmetic body;
each annotated definition and `.call` still creates its own first-order function boundary.

| Example | Shape | Result at input 4 |
| --- | --- | --- |
| `chain3` | Four functions; three retained values at different depths. | 32 |
| `chain7` | Eight functions with a retained value at every caller. | 82 |
| `tree` | Two branches sharing callees; earlier results survive later calls. | 149 |
| `sum24` | Twenty-four demanded arguments. | 300 for arguments 1 through 24. |
| `locals` | Sixteen values survive a 24-argument call and the tree. | 9061 |
| `choose` | Runtime alternatives with a retained value. | 43; input -4 returns 39. |

At the ordinary budget these examples allocate register-only data calls.
Limiting the ordinary pool to two registers exercises caller saves,
local spills, and stack parameters; setting it to zero exercises the all-stack convention.

`Oria.Proofs.CallAllocation` checks those allocation contracts.
`IndexedVector.set` uses Lean's `Vector.set`; its interface theorems establish that the
updated position returns the supplied value and every other position retains its value.

`scripts/gametest` executes every example with budgets 128, 8, and 6, checks each numeric
result, and checks invocation stack/arena cleanup. Existing recursive sum, Fibonacci,
nested recursion, and self-tail-call cases run in the same suite.

The strategy minimizes preservation through callee-aware preferences. Register pressure,
recursive interference, and conservative summaries can still require storage. The
[calling convention](register-allocation.md) specifies the resulting frame operations.

## Parallel transfer validation

Wide calls exercise the symbolic store used by the parallel-move checker. Its execution
fold captures every source value before constructing the next store closure. A standard
`ULift` wrapper gives the fold a data-valued accumulator, and an explicit non-inlining
boundary preserves that evaluation order during compilation.

`execute_eq_fold` proves equality with the functional-store execution rule. The existing
mapping and untouched-location proofs use that equality, so each generated transfer
sequence retains its certificate for arbitrary input stores. `Oria.Proofs.Transfers`
checks a 64-move schedule in addition to swap and cycle schedules.
