# Source programs

Oria elaborates Lean terms into typed object expressions and structured computations.
`Val A r` represents a pure object expression; `Prog g A r` represents ordered computations
with requirement/effect grade `g`. Host functions, host-typed locals, and host collections
run during construction. Named `.call` sites remain object-level calls.
The [elaboration guide](elaboration.md) specifies the type and syntax dispatch rules.

## Inference and contracts

A body ascription fixes its result carrier while allowing grade synthesis:

```lean
@[mcfunction]
def readPoints := show Prog _ Int32 from do
  let n ← Scoreboard.get .self "points"
  return n + 1
```

Lean checks a definition header before its body. Place inferred grade holes in the body
ascription. An explicit grade checks the computation's exact grade; `Prog.weaken` records
an explicit upper bound. Statement branches compose with their own local result type.
Both host and object alternatives use the join of their grades.

Grade mismatches report named requirements and effects. Constructor checking uses the
expected source datatype. Annotate an arrow binder as `Val A` when a leading-dot constructor
needs that datatype; a qualified `A.constructor` can synthesize it from the constructor name.

## Numeric command parameters

Shared command parameters use Lean's numeric instances and coercion chains:

```lean
@[mcfunction]
def bump (n : Val Int32) := show Prog _ Int32 from do
  Scoreboard.set .self "points" (n + 1)
  Teleport.to .self (Vec3.absolute n 64.25 0.0)
```

Integer literals and host `Int32` values become static integer arguments. Runtime `Val Int32`
expressions become integer macro holes. `Decimal` also accepts decimal/scientific literals
and host `Float`/`Float32` values, preserving fractional spelling and signed zero. Thus
`Vec3.absolute 1 65.25 1` centers X/Z at 1.5, while `Vec3.absolute 1.0 65.25 1.0` keeps
X/Z at 1.0. The I32 forms retain the host's `Int32` arithmetic and wrapping behavior.

`Vec3.relative x y z` offsets the execution position. `Vec3.world` accepts a separate
absolute/relative constructor for each axis. `BlockPos.absolute` and `BlockPos.relative`
provide the corresponding integer block-coordinate forms. These constructors preserve
the existing fragment encoding and context requirements; each dynamic component contributes
only its own macro hole. `Scalar` and `Decimal` retain explicit constructors for library
authors who inspect host argument descriptions.

For an argument carrier with a coercion interface, the operator elaborator synthesizes
arithmetic in its numeric type before inserting the coercion. It uses Lean's operator
elaborator and isolated typeclass synthesis. Expressions such as `n + 1` therefore retain
their `Val Int32` arithmetic before entering `Scalar` or `Decimal`. A target with its own
arithmetic instance retains Lean's expected-type-directed elaboration.

## Records and regions

Within object `do`, `let x := e` gives a `Val` expression one shared object binding.
Host values and `Prog` descriptions retain Lean let semantics. Use `←` to execute a
computation and `return` to supply its normal result.

Structures deriving `Oria.Object` support pure field projection, construction, and update:

```lean
public structure Stats where
  wins : Int32
  losses : Int32
  rounds : Int32
  deriving Oria.Object

@[mcfunction]
def won {r : Region} (s : Val Stats r) : Prog .pure Stats := do
  return {s with wins := s.wins + 1, rounds := s.rounds + 1}
```

`s.wins : Val Int32 r` retains the source region. Projections compose, including
`s.child.count` for nested structures. Fields are resolved through Lean's structure metadata
and the generated typed projection functions. Parameterized structures retain their
source type arguments.

Construction supplies every field explicitly. Update supplies named field paths and
preserves the remaining fields. Shared path prefixes are reconstructed once. The source
is bound once. Reconstruction produces a fresh arena-neutral value. Updating a persistent
record therefore requires explicit
`persist` before a root or persistent Ref can receive the new value. A nested update can
write `return {s with child.count := s.child.count + 1}`. Overlapping field assignments
are rejected.

Tree retains a projection's constructor and type-correct field position. Object linking
certifies that the constructor is the sole constructor of its exact schema. ANF lowering
exposes its fields through Cont's existing constructor decomposition. Machine chooses the
physical offsets and demanded field reads.

## Lexical control flow

Object `do` supports statement `if`, `else if`, early return, and constructor/integer
matching. Return exits the nearest object `do` expression:

```lean
@[mcfunction]
def guarded (n : Val Int32) : Prog .pure Int32 := do
  if n < 0 then return 0
  if n == 0 then return 1
  return n + 1
```

A nested object `do` has its own return destination. An `if` or `match` statement inside
a block retains that block's return destination, while normal completion returns Unit
to its local continuation. Continuing alternatives share the following computation.
Root assignments keep their existing persistent-value requirement.

The elaborator reuses Lean's `DoOps`, `DoElemCont`, `ReturnCont`, and control information.
For a block containing nonlocal exits it installs a typed lexical destination. Tree has
`block k {body}` and `leave k value`; lowering resolves destinations to scoped Cont
joins/jumps. The runtime calling convention handles the resulting ordinary control flow.
The extension adapts the control machinery to graded object carriers, whose bind operations
compute a new grade.

Let \(K\) map lexical destinations to their payload types. A local continuation's result
type \(B\) may differ from the destination's payload type \(A\):

\[
\frac{k:A\in K\qquad\Gamma\vdash v:A}
     {\Gamma;K\vdash\operatorname{leave}\ k\ v:B\;!\;\mathsf{pure}}
\qquad
\frac{\Gamma;K,k:A\vdash C:A\;!\;g}
     {\Gamma;K\vdash\operatorname{block}\ k\ C:A\;!\;g}.
\]

ANF lowering maps each lexical destination to a typed return or join destination together
with its captured atoms. Context extension renames those atoms; introducing a join shifts
the stored join references. Normal completion and explicit leave share the block's result
continuation. The scoped Cont types check the destination's parameter telescope.

The underlying elaboration facilities are described in
[Ullrich and de Moura, *do Unchained*](https://lean-lang.org/papers/do.pdf).
The explicit join representation follows
[Maurer et al., *Compiling without Continuations*](https://simon.peytonjones.org/compiling-without-continuations/).

## Finite host iteration

`for` iterates a host List, Array, or bounded range. Construction expands iterations in
source order. Runtime recursion uses a typed local `let rec` or the `Prog.fix` builder.

For long computations, `Task.checkpoint` permits budget-driven parking and `Task.yield`
forces continuation on the next tick. Both contribute `Eff.suspend`; register the enclosing
zero-argument Unit computation with `Datapack.task`. See [cooperative tasks](tasks.md).

```lean
def digits : Prog scoreGrade Unit := do
  for n in ([1, 2, 3] : List Int32) do
    Scoreboard.set (.named "#digit") "points" n
  return Val.unit
```

All iterations share one declared grade bound. Host alternatives join their grades; the
list fold uses the proved idempotence of grade sequencing. Grade dependence on an element
requires an explicit uniform bound at the body interface. An empty collection returns
Unit successfully and performs no body effects.

`continue` exits the current iteration, and `break` exits the nearest loop. `return` exits
the enclosing object `do`. Nested loops introduce their own break/continue destinations.
Loop conditions may use host Bool/Prop values or runtime `Val Bool` expressions. Loop
binders are host identifiers or `_`; each loop currently has one collection clause.

Body failure stops iteration and propagates to the enclosing
computation. A Unit-returning body ignores a successful command payload while retaining
the success test. Effects preceding failure remain observable.

## Pattern and host bindings

Recovery uses the generic [Failure combinators](failure.md). Each action executes once;
fallbacks run only on failure. Arrow patterns inspect the normal result's source type:

```lean
def readOrZero : Prog (Scoreboard.readGrade .self).handled Int32 :=
  (Scoreboard.get .self "points").getD 0

def inspectCompletion : Prog (Scoreboard.readGrade .self).handled Int32 := do
  let .some n ← Prog.attempt (Scoreboard.get .self "points") | return 0
  return n
```

Object `let pattern := value | fallback` uses the same pattern matrix as `match`.
Coverage checks apply when a fallback is absent. Fallback return follows the block's
lexical destination. The continuation is elaborated in the pattern variables' object
context using Lean's deferred-term facility.

Local host functions and host pattern bindings use Lean's ordinary elaboration. Their
results can assemble object expressions, compute command arguments, or generate programs.
They retain the host stage's types and semantics.

[RoundLedger](../Oria/Examples/RoundLedger.lean) exercises these forms through generated
public entries. [Language acceptance](language-acceptance.md) records the server-observable
contracts and the register/stack variants.
