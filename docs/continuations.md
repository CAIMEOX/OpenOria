# Continuations, patterns, and demand

Tree retains source pattern matrices. Tree-to-Cont lowering performs ANF conversion,
resolves nominal locals to indexed scope positions, and compiles each matrix into
constructor or integer tests. Joins make shared continuations explicit.

## Patterns and bindings

A pattern records its subject type and the ordered types of its bindings:

\[
p:\mathsf{Pattern}\ A\ \Delta,
\qquad
\bar p:\mathsf{Patterns}\ \bar A\ \Delta.
\]

The rules are:

\[
\begin{gathered}
\frac{}{\_:\mathsf{Pattern}\ A\ []}
\qquad
\frac{}{x:\mathsf{Pattern}\ A\ [A]}
\\[1em]
\frac{n:\mathsf{I32}}{n:\mathsf{Pattern}\ \mathsf{I32}\ []}
\\[1em]
\frac{c:\bar B\to A \quad \bar p:\mathsf{Patterns}\ \bar B\ \Delta}
     {c(\bar p):\mathsf{Pattern}\ A\ \Delta}.
\end{gathered}
\]

Pattern vectors concatenate binding types in source order. Lean resolves constructor names
and elaborates RHS environments. Reification creates locals for those bindings and records
each RHS once. Coverage and redundancy are checked during pattern lowering.

## Cont syntax

Let \(\Gamma\) be the local-value context and \(J\) the context of join parameter telescopes.
`Comp Γ R J` has result type \(R\). Its syntax is:

\[
\begin{aligned}
a &::= x\mid()\mid b\mid n,\\
C &::= \mathsf{return}\ a\\
  &\mid \mathsf{let}\ x=o\ \mathsf{in}\ C\\
  &\mid \mathsf{invoke}\ o\ \{x\Rightarrow C;\ \mathsf{failure}\Rightarrow D\}\\
  &\mid \mathsf{fail}\\
  &\mid \mathsf{if}\ a\ \mathsf{then}\ C\ \mathsf{else}\ C\\
  &\mid \mathsf{switch}\ a\ \{c_i(\bar x_i)\Rightarrow C_i;\ d\}\\
  &\mid \mathsf{join}\ j(\bar x)=C_j\ \mathsf{in}\ C\\
  &\mid \mathsf{jump}\ j(\bar a),\\
d &::= \epsilon\mid\_\Rightarrow C.
\end{aligned}
\]

Operations include arithmetic, construction, calls, commands, Execute, and memory.
A switch tests one constructor layer and introduces that constructor's fields only
in the selected successor.

Join bodies receive their values through their own parameter telescope and can refer to
outer joins. Lowering passes pattern bindings followed by the lexical environment;
demand analysis later removes unused components.

\[
\frac{j:\Delta\in J \quad \Gamma\vdash\bar a:\Delta}
     {\Gamma;J\vdash\mathsf{jump}\ j(\bar a):R}
\]

`Scope.Var` and `Args` enforce these scope and telescope constraints.
The `join_arguments` theorem in [Match](../Oria/Proofs/Match.lean) states the corresponding
argument-delivery law in the Cont interpreter. Tree computations carry exact grades;
Cont operations and function signatures retain the declared bounds.

## Pattern compilation

[Lower.Pattern](../Oria/Compiler/Lower/Pattern.lean) uses Maranget's specialization/default
scheme with a leftmost-column heuristic. An irrefutable first row jumps to its RHS.
Constructor specialization expands payload patterns; default retains wildcard and variable
rows. Both operations preserve source order.
See [Compiling Pattern Matching to Good Decision Trees](https://www.cs.tufts.edu/~nr/cs257/archive/luc-maranget/jun08.pdf).

Each RHS becomes a join before compiling tests. Default successors and non-tail
continuations are shared. The explicit join organization follows
[Compiling without Continuations](https://simon.peytonjones.org/compiling-without-continuations/).

For example:

```text
Rock, _ => 10
_, Rock => 20
_, _ => 30
```

The first subject reaching Rock selects the first RHS. Remaining values share the second
subject's test. [Match](../Oria/Proofs/Match.lean) evaluates all enum combinations and checks
row priority, nested payloads, binder order, and non-tail continuation behavior.

Integer alternatives use equality followed by a residual matrix on the unequal edge.
The [integer-pattern guide](integer-patterns.md) describes numeral and coverage semantics.

The recursive compilation measure counts remaining refutable patterns and columns.
The implementation uses a private `partial` definition. Type indices constrain its generated
bindings and jumps; selected RHS identities support redundancy checking.

## Physical components

Machine lowering expands Cont values using the shared representation table.
For a 32-bit word \(W\), widths are:

\[
\begin{aligned}
w(\mathsf{Unit})&=0,\\
w(\mathsf{I32})=w(\mathsf{Bool})&=1,\\
w(\mathsf{Data}\ T)=w(\mathsf{Option}\ A)&=1,\\
w(\mathsf{Ref}\ A)=w(\mathsf{Nbt}\ t)&=1,\\
w(\mathsf{Value}\ (A_1,\ldots,A_n))&=\sum_i w(A_i).
\end{aligned}
\]

Enums carry constructor tags. Payload ADTs and Option carry arena pointers. Inline value
types concatenate their scalar fields. These are normal-value representations.

Function return width depends on the declared failure effect:

\[
w_{\mathrm{return}}(g,A)=w(A)+[\mathsf{failure}\in g.\mathit{eff}].
\]

A potentially failing function prefixes normal values with 1 and failure padding with 0.
Successful zero is \((1,0)\); failure payload words are inaccessible from the normal
successor. `Prog.attempt` constructs ordinary Option data using lexical recovery.
See [failure and recovery](failure.md) and [object layouts](object-values.md).

## Demand equations

Demand masks select block parameters, function returns, and instruction result components.
All call sites share the resulting function ABI.
Let \(U_\mu(\bar a)\) collect the variables used by selected arguments:

\[
U_\mu(\bar a)=\bigcup_{i:\mu_i=1}\mathsf{FV}(a_i).
\]

An instruction introduces \(m\) fresh results before the old \(n\)-word context.
For successor demand \(D'\):

\[
\begin{aligned}
R&=D'[0:m],\\
D&=D'[m:m+n]\cup T_o(R).
\end{aligned}
\]

A pure operation needs no inputs when \(R\) is empty; otherwise it needs its operands.
Commands retain demand for their dynamic inputs.
A call to \(f(\bar a)\) contributes \(U_{P_f}(\bar a)\) and updates
\(R_f\gets R_f\cup R\).
A jump to \(b(\bar a)\) contributes \(U_{P_b}(\bar a)\), and a return contributes
\(U_{R_f}(\bar a)\). Branches additionally demand their discriminant.

[Demand](../Oria/Compiler/Analysis/Demand.lean) solves this monotone finite-bitmask problem
with a worklist. Block predecessors, callers, and return blocks are revisited when the
facts they consume change. Root return components are observable.
Calls retain their execution position even when their results are unused.

| Demanded command components | Target capture |
| --- | --- |
| Neither | Direct command execution |
| Success | `execute store success` |
| Result | `execute store result` |
| Both | Nested success/result stores |

An invocation with distinct normal/failure successors needs success. Control-flow
simplification can make a component unnecessary. Static and dynamic argument encoding is independent of this capture choice.
Internal calls return object results through component locations and use native
`return 0`. Public Unit wrappers translate the internal failure flag into native failure
after invocation cleanup.

## Analysis lifetime and validation

A Machine rewrite invalidates demand facts. Condition optimization computes the facts it
needs; final allocation recomputes them for the resulting CFG and shares them with encoding.
Dead-code elimination normalizes unobserved return words before CFG simplification and
repeats demand analysis after shrinking the graph. Scalar constant folding and backend
definition sharing are described in [optimization](optimization.md).

Scope, operand width, and edge arity are indexed. Reference interpreters and behavioral
checks cover matching and component transport. Parallel moves have a semantic certificate.
Complete pattern-compilation, effect-preservation, and end-to-end lowering theorems have
not been established. See [integration acceptance](../integration/datapack/README.md).
