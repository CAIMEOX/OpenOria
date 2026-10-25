# Register allocation and the call stack

Location allocation runs on Machine's word-level CFG. Demand, liveness, and allocation
results are analysis metadata consumed by DP121 lowering.

## Budget

```lean
Datapack.build { ns := "demo", registerBudget := 128 } do
  entry "run" run.ref
```

A budget \(B\ge6\) reserves four scratch registers and two result registers, leaving
\(B-6\) ordinary value registers. Budget 6 uses stack locations for all ordinary values.
The default is 128; larger budgets are allowed. Minecraft imposes no hardware limit at 128.

Ordinary registers use `#rN`, scratch registers `#s0` through `#s3`, and results
`#ret0` and `#ret1`. Dedicated heap/runtime state is outside this pool.

## Demand and liveness

[Demand](../Oria/Compiler/Analysis/Demand.lean) propagates component demand across blocks
and calls using the shared operand rules in
[Analysis.Machine](../Oria/Compiler/Analysis/Machine.lean).
For target-parameter demand \(D\) and edge arguments \(\bar a\):

\[
\mathsf{EdgeUse}(D,\bar a)=\bigcup_{j\in D}\mathsf{FV}(a_j).
\]

This substitution maps target positions to the source scope.
For an instruction producing \(m\) fresh words:

\[
\begin{aligned}
D_i&=\mathsf{take}_m(L_{\mathrm{after}}),\\
C_i&=\mathsf{drop}_m(L_{\mathrm{after}}),\\
L_{\mathrm{before}}&=C_i\cup\mathsf{Uses}(op_i,D_i).
\end{aligned}
\]

\(C_i\) records the old values live across the instruction.
After demand reaches its fixed point,
[Liveness](../Oria/Compiler/Analysis/Liveness.lean) freezes inputs, outputs, across masks,
and the callee at each position.

The stable block-local number is \(n-1-i\) for scoped variable \(i\).
Input reads and result definitions occur at events \(2i+1\) and \(2i+2\).
Half-open intervals end after the final read, allowing an output to reuse an input's
location when that input dies.

## Allocation

Machine blocks access their own parameters and earlier results; edges transport cross-block
values. [LinearScan](../Oria/Compiler/RegAlloc/LinearScan.lean) allocates each block separately,
reuses expired registers, and spills the interval ending farthest away when necessary.
Spilled intervals receive reusable stack slots. Function-local space is the maximum
needed by any block. The algorithm follows
[Poletto and Sarkar](https://web.cs.ucla.edu/~palsberg/course/cs132/linearscan.pdf).

Immediate literals retain their direct form. Dead components have no location.
Call-graph SCCs determine callee-first preferences. Recursive components use a frozen
summary while final clobbers are recomputed from completed placements.
See [interprocedural allocation](interprocedural-allocation.md).

Within this preference pass, CFG edges favor matching register homes for transported words,
and arithmetic results favor the left operand's home. Hints are collected once per function
from the frozen placement. Avoiding caller-save conflicts has priority over these copy costs.
The interval checker validates every resulting assignment; final clobber and save sets are
computed from the selected homes. A hint does not assert that a register is free.

[Check](../Oria/Compiler/RegAlloc/Check.lean) verifies that every live interval has a home
and overlapping intervals do not share one. Its soundness theorem produces the placement
proposition. Fin indices bound registers and slots.
This certificate assumes the supplied intervals are sound.

## Calls and frames

A callee's demanded entry-parameter homes determine its internal parameter ABI.
Overflow arguments use its local stack slots.
The first two demanded return components use result registers; wider Machine results use
frame result slots. Callers import only the components they need.

For call \(c\) to \(g\), with transitive ordinary-register use \(W_g\):

\[
\mathsf{Saved}(c)=
\mathsf{RegLoc}(C_c)\cap
\bigl(\mathsf{ArgRegs}(g)\cup W_g\bigr).
\]

Parameter preparation is included because it can overwrite caller values.
Caller values already on the stack need no additional register save.

A data frame has the shape:

```text
{locals: [...], saved: [...], result: [...]}
```

The call sequence is:

1. Create a callee frame when needed and save caller registers.
2. Write stack parameters, then schedule parallel register-parameter moves.
3. Invoke the callee.
4. Restore caller registers, import results, and pop the frame.

A running callee uses `stack[-1].locals[i]`. During framed handoff, caller locals use
`stack[-2].locals[i]`; a frameless call keeps the current frame.
These offsets are static and require no addressing macro.
Blocks and macro helpers within one activation do not create separate language frames.

Minecraft function/return supplies control return. The NBT stack stores data.
Entries, callbacks, and root initializers use the same data-call convention.

Resumable task calls store an explicit return continuation in the caller frame and place
results in the task workspace. Parking copies only live register homes; existing spills
remain in their frame. Resume restores those words before entering the continuation.
Register placement and liveness use the same Machine analyses as synchronous calls.
See [cooperative tasks](tasks.md) for the tick-to-tick protocol.

## Parallel transfers and location reuse

[Transfer](../Oria/Compiler/Lower/DP121/Transfer.lean) breaks move cycles with one temporary
location and symbolically validates the schedule for arbitrary input stores.
Its algorithm follows
[Rideau, Serpette, and Leroy](https://xavierleroy.org/publi/parallel-move.pdf).

Register moves use scoreboard operations; register/stack moves use store/get; stack copies
use NBT set-from. Arithmetic reads any operand that an output will overwrite before publishing
the result. Division uses the allocated quotient register directly when available and retains
a register divisor in place. If initializing the quotient would overwrite its divisor, the
divisor is copied first. Success is published after the native division reads its operands;
stack results use scratch registers. Signed floor rounding and zero failure are native.

Commands freeze dynamic inputs in the macro compound before result publication.
Native selection helpers share these prepared fields across their internal commands.
Helpers that read ordinary input homes until return capture into reserved scratch
registers, then move the demanded channels to their allocated result locations.
Heap construction writes an isolated draft; projection freezes the source address before
writing reused result locations.

## Arena lifetime and acceptance

Internal calls share an invocation arena. An outer normal return releases the arena and
stack; object returns remain valid within the invocation. Persistent GC runs through a
separate maintenance entry after that return and scans named roots.
See [persistent memory](persistent-memory.md).

A task's arena and data stack belong to its entire logical invocation, including parked
intervals. Ordinary entries use a separate arena and stack. The collector rejects calls
while the task slot is active, preserving persistent objects held only by task locals.

Each entry's allocation and scratch requirements include its transitive callees and Execute
bodies. An entry initializes an arena or stack only when this summary requires it. Execute's
capture frame and an ordinary callee's spill frame are selected independently; dynamic
Execute arguments address the current frame when there is no capture frame.

Calling a public wrapper from an active invocation can reset that invocation's storage.
Command libraries must respect the compiler's reserved objective, storage, and function
identities.

Interface proofs cover numbering, placement validation, register-role separation, and
parallel moves. The validation strategy is related to
[translation validation for register allocation](https://xavierleroy.org/publi/validation-regalloc.pdf).
Full liveness soundness and Machine-to-DP121 frame simulation have not been proved.

`scripts/quality` checks the contracts and final emitted files.
`scripts/gametest` exercises overflow arguments, caller saves, long/shared-callee chains,
24-argument calls, retained locals, recursion, failure behavior, persistent memory, and
invocation cleanup. Budgets 128, 8, and 6 provide ordinary, two-register, and all-stack
acceptance configurations. These are behavior tests, not performance measurements.
