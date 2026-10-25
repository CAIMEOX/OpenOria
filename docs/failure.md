# Failure and recovery

A computation `Prog g A r` has a normal result of type `A`. Its grade records observable
effects and execution-context requirements. The `failure` effect means that execution may
leave without producing a normal value. It says nothing about termination or world rollback.

## Source interface

```lean
@[mcfunction]
def next := show Prog _ Int32 from do
  let n ← Scoreboard.get .self "points"
  Scoreboard.set .self "points" (n + 1)
  return n + 1

@[mcfunction]
def readOrZero := show Prog _ Int32 from do
  try
    Scoreboard.get .self "points"
  catch _ =>
    return 0

@[mcfunction]
def initialize := show Prog _ Unit from do
  (Scoreboard.Objectives.add "points" .dummy).ignore
```

An arrow binding receives the normal result. A bare statement discards that value and
propagates failure. `return v` returns normally from the nearest object `do` block.

Recovery is lexical. The catch arm handles failure while executing its protected body.
Failure in the catch arm, or in code following the complete try expression, propagates to
the next enclosing handler. Each action is executed once. World changes made before failure
remain observable; recovery does not restore scores, entities, storage, or persistent roots.

The public combinators are ordinary program constructors:

| Form | Normal result | Failure behavior |
| --- | --- | --- |
| `Prog.fail` | No normal value | Leave through the failure exit |
| `p.map f` | Transform the normal value | Propagate |
| `p.discard` | Unit | Propagate |
| `p.ignore` | Unit | Suppress |
| `p.getD v` | Value or fallback `v` | Recover |
| `p.orElse q` | Value from `p` or `q` | Run `q` on failure; propagate its failure |
| `p.isSuccess` | Bool | Capture completion |
| `Prog.attempt p` | Option A | Capture completion as object data |

A successful integer zero remains a normal value. For a command, the native success bit
selects normal or failed completion; its integer result never determines success. `attempt` constructs an ordinary Option, which can be matched, returned,
stored in an ADT, and explicitly persisted. It can therefore allocate an object.
`getD`, `isSuccess`, `ignore`, and lexical recovery require no such materialization.

## Effect rules

Write a grade as \(g=(\rho,\epsilon)\), where \(\rho\) is a requirement row and \(\epsilon\)
is an effect row. Let \(F\) denote the failure label and \(H(g)=(\rho,\epsilon\setminus\{F\})\).
Sequential and branch composition use componentwise union, written \(g\sqcup h\).

\[
\frac{\Gamma\vdash p:A\;!\;g\qquad
      \Gamma,x:A\vdash q:B\;!\;h}
     {\Gamma\vdash\mathsf{bind}\ p\ x.q:B\;!\;(g\sqcup h)}
\]

\[
\frac{}{\Gamma\vdash\mathsf{fail}:A\;!\;(\varnothing,\{F\})}
\qquad
\frac{\Gamma\vdash p:A\;!\;g\qquad\Gamma\vdash q:A\;!\;h}
     {\Gamma\vdash\mathsf{catch}\ p\ q:A\;!\;(H(g)\sqcup h)}.
\]

Both possible paths contribute their context requirements. Handling failure removes only
that effect; reads, writes, and other effects remain. An explicit `Prog.weaken` can retain a
larger declared bound. Kernel-checked grade laws establish that handling is idempotent,
distributes over composition, and removes the failure bit.

## Control-flow lowering

Tree contains `fail` and `catching body handler`. Function signatures retain the normal
result type and the grade.

ANF lowering carries two destinations: normal completion and failure. A catch introduces a
join for the handler, capturing its lexical environment. The protected body uses that join
as its failure destination. The handler uses the outer failure destination. The continuation
after the catch is compiled outside the protected scope.

Cont represents a potentially failing primitive as:

\[
\mathsf{invoke}\ o\
  \{\mathsf{normal}(x)\Rightarrow C;\ 
    \mathsf{failure}\Rightarrow D\}.
\]

The primitive executes once. Only the normal successor binds its result. A terminal
`fail` leaves the current definition; ordinary joins represent local recovery.

Machine chooses the physical return convention. For normal value width \(w(A)\):

\[
w_{\mathrm{return}}(g,A)=
\begin{cases}
1+w(A),&F\in\epsilon_g,\\
w(A),&F\notin\epsilon_g.
\end{cases}
\]

A potentially failing function returns \((1,\llbracket v\rrbracket)\) on normal completion
and \((0,\bar 0)\) on failure. Failure payload slots are padding and cannot be read as values.
An infallible function returns only its normal words. Object layouts and persistent-root
payloads contain value words, independently of this function ABI.

Native command operations expose success and integer-result words. Demand analysis decides
which stores to emit. Direct `ignore` can execute a command without capturing either word;
a propagating statement needs success, and binding an observed integer also needs result.
Ignoring a named call retains the callee's internal failure control flow.

## Invocation boundaries

A public Unit entry completes with native success and result zero. An unhandled failure
returns native failure after releasing invocation stack, arena, and temporary storage.
Each load/tick callback has its own boundary, so failure in one callback does not suppress
later registrations.

`Execute.forEach` accepts a Unit- or Int32-returning body. Normal Unit completion supplies
native result zero; normal Int32 completion supplies that integer. Body failure stops that
branch, while Minecraft continues other selected contexts. The outer scope masks body
failure. Native store-success/store-result steps observe each branch's completion.

A persistent initializer publishes its normal value only after normal completion. Failed
initialization releases temporary memory and leaves initialization incomplete, so ordinary
entries remain gated. Runtime corruption and panic are fatal conditions, outside recoverable
Failure semantics.

## Validation

[FailureRuntime](../Oria/Proofs/Fixtures/FailureRuntime.lean) is compiled to final datapacks
and exercised on the pinned server with register budgets 128 and 6. Assertions cover
successful zero, short-circuiting, fallback, Option capture, cross-function propagation,
nested recovery, callback isolation, initializer publication, and cleanup after a failing
public entry. Execute, persistent-memory, and command-family fixtures exercise the same
protocol in their own contexts.

Scope and arity are indexed. The grade algebra is proved in
[Effect.Grade](../Oria/Effect/Grade.lean); [Failure](../Oria/Proofs/Failure.lean) proves
that invocation selects the appropriate successor and passes it the post-operation state.
These guarantees do not constitute an end-to-end semantic-preservation proof of the
complete compiler.
