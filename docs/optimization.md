# Scalar and memory optimization

Optimization has three seams. Each consumes the representation that contains the information
needed for its decision.

| Stage | Transformation | Required information |
| --- | --- | --- |
| Cont | Scalar folding, copy substitution, constructor refinement, native load forwarding and presence checks | Typed operators, atomic operands, structured selections, lexical success and alias facts |
| Machine | Record decomposition, CFG constant propagation, predicates, bit returns and dead code | Frozen schemas, executable edges, scalar facts, bit guarantees and whole-program demand |
| DP121 | Entry storage, immediate arithmetic, native parameter preparation, tail-path layout and code sharing | Allocation plans, transitive resources, physical locations and macro schemas |

## Constant folding

[Cont simplification](../Oria/Compiler/Optimize/Cont.lean) evaluates literal operands of
negation, Boolean negation, arithmetic, and comparisons. Its existing typed substitution
propagates the result into later operations, command holes, and branches:

\[
\mathsf{let}\ x=o(\bar c)\ \mathsf{in}\ C
\;=\;
C[x\mapsto\llbracket o\rrbracket(\bar c)].
\]

Total scalar operations use wrapping Int32 arithmetic. Fallible division uses
`I32.divide`, which follows scoreboard floor division and returns `none` for zero divisors.
A constant division selects its existing normal or failure continuation. Commands, calls,
and memory operations are not evaluated by this transformation.

A folded command operand reaches DP121 as an immediate. The command encoder already
converts immediate I32 holes into static fragments. Thus `(-999 : Val Int32)` can become
the native literal `-999` without introducing command-specific arithmetic rules.

The pass is local substitution. It does not specialize named calls or compute a global
constant-propagation fixed point across all joins.

The same traversal applies I32 identities `x + 0 = x`, `x - 0 = x`, `x * 1 = x`,
and `x * 0 = 0`, including the commuted addition and multiplication forms. These are wrapping-Int32 equations;
Lean's `Init.Data.SInt.Lemmas` provides their arithmetic justification. The operands
are already atoms. Substitution therefore preserves earlier effectful or diverging calls.

Within a constructor arm, the scrutinee is known to be that constructor applied to the
arm's bound fields. Facts shift under binders using the shared typed renaming interface.
Repeated immutable projections reuse those fields. Join bodies start with their own
parameter facts. At Machine lowering, a single-constructor nominal schema decomposes
directly; demanded fields then share one address macro. Multi-constructor values retain
their discriminator tests. This uses schema identity already frozen in the representation
table, rather than reconstructing a record shape from emitted commands.

The approach follows Lean's
[constructor-discriminant simplification](https://github.com/leanprover/lean4/blob/v4.31.0-rc2/src/Lean/Compiler/LCNF/Simp/DiscrM.lean):
known constructors and their payloads are lexical simplifier facts.

## CFG constants and predicates

[Machine constant propagation](../Oria/Compiler/Optimize/Constants.lean) joins incoming
values on executable edges. Its flat lattice contains an unevaluated value, a single I32
constant, and an unknown value. Equal constants remain constant; distinct constants merge
to unknown. Function parameters start unknown. Loop backedges participate in the same
fixed point, so an initially constant induction variable becomes unknown when it changes.
Edge-local jump threading also substitutes the incoming tuple through a fully reducible
scalar prefix before selecting the next edge. This handles constant Boolean joins followed
by negation; calls, memory operations, and irreducible computations stop this traversal.

The transfer functions evaluate scalar operators using scoreboard arithmetic. Calls,
commands, and memory results are unknown. A constant nonzero divisor establishes success
even when its numerator is unknown; zero establishes failure. Known operands fold quotients,
and division by one substitutes the tuple `(1, numerator)`, justified by `I32.divide_one`.
Wrapping integer identities also remove neutral addition/multiplication, self-subtraction,
and reflexive comparisons. Scoped substitution replaces their result tuples without moving
effects. Subsequent CFG simplification removes unreachable edges, and demand analysis removes
unused result computations. Machine division exposes success as a scalar channel, so a
division whose two channels are unused can disappear.

The join and scalar lifting laws have kernel-checked proofs. These establish the local
abstract operations; whole-CFG semantic preservation remains a separate proof obligation.
The dataflow follows the executable-edge model of
[sparse conditional constant propagation](https://llvm.org/docs/Passes.html#sccp-sparse-conditional-constant-propagation).
Lean's LCNF folder operates on Lean expressions and declaration identities. This pass uses
the existing scoped Machine operations and `Std.DHashMap` for its arity-indexed block facts.

[Predicate simplification](../Oria/Compiler/Optimize/Conditions.lean) retains a comparison
and its polarity. Negating a known predicate flips the polarity; the final branch exchanges
its successors. This avoids materializing a comparison solely to negate and branch on it.
Predicate recipes cross a CFG edge when all their operands occur in the edge's argument
tuple (literals need no parameter). Every incoming edge must agree on the renamed recipe;
disagreement discards it. Function entries begin with unknown predicates, and loop backedges
participate in the fixed point. Recipes describe immutable scalar snapshots, not repeated
reads of mutable locations. No additional block parameters are introduced.

Predicates that also have scalar consumers retain their values. Register allocation runs
after this transformation and accounts for the operands now needed at the branch.

## Owned-document memory facts

Typed native accesses enter Tree with their root, field keys, scalar indices, selected
schema, and write source. The shared [path contract](../Oria/IR/Common/Nbt/Path.lean)
captures dynamic indices in the operation's typed operand telescope. Capture/restoration
theorems establish that substituting those operands reconstructs the original path and
write source. Field names remain individual keys, including keys containing punctuation.
Machine retains this descriptor; DP121 renders it when choosing physical locations.
Each address base is either an arena operand or a registered global's static storage path.
Global prefixes are included in the canonical path before alias comparison.

After scalar substitution, [Cont memory simplification](../Oria/Compiler/Optimize/Memory.lean)
uses the function's declared effect row to skip definitions that cannot access owned memory.
For participating definitions, it walks lexical continuations with a set of must-facts.
A location is a root binder plus a
sequence of fields and indices. Facts record that a selection exists and, when known,
its I32 value or list length. Each operation has separate success and failure transfers:

| Operation | Normal successor | Failure successor |
| --- | --- | --- |
| I32 read or length | Record presence and the returned scalar | Keep incoming facts |
| Set | Invalidate overlapping facts, record presence and any known I32 source | Invalidate overlapping facts |
| Clear | Invalidate overlapping facts, record presence and length zero | Invalidate overlapping facts |
| Copy | Invalidate destination overlaps, forward any known source I32 | Invalidate destination overlaps |
| Append | Invalidate destination overlaps, record destination presence | Invalidate destination overlaps |
| Snapshot | Record the successful singular selection | Keep incoming facts |
| Call, external command, Execute, or suspension | Start with empty facts | Start with empty facts |

Successful reads and writes can therefore establish the premises for later rewrites:

\[
\begin{aligned}
\mathsf{let}\ x\leftarrow\operatorname{read}(\ell);\ \operatorname{read}(\ell)
  &\rightsquigarrow \mathsf{let}\ x\leftarrow\operatorname{read}(\ell);\ \mathsf{return}\ x,\\
\operatorname{set}(\ell,v);\ \operatorname{read}(\ell)
  &\rightsquigarrow \operatorname{set}(\ell,v);\ \mathsf{return}\ v.
\end{aligned}
\]

Here the first read binds x, the second read has the same observation mode, and no
intervening operation may modify the location. Both equations describe the normal
continuation. The first access retains its failure exit and every write retains its
execution position. Presence facts can remove repeated read checks. Native mutations
retain their own failure behavior, including unchanged values; they can create missing
compound keys according to Minecraft's path rules. Indexing an array initially requires
a bounds-sensitive selection.

[Alias analysis](../Oria/Compiler/Analysis/Memory.lean) treats different root parameters
as potentially equal. Every Ref denotes a whole owned allocation, so different field keys
separate subtrees even when the roots alias. A prefix overlaps all of its descendants.
Equal atomic indices select the same element. Distinct constant indices with the same
sign select different elements; `0` and `-1` may coincide. The theorem
`separateIndices_sound` proves this separation for every list length. Replacing, clearing,
or appending to a list invalidates facts about its descendants, including negative indices.
Distinct storages are separate, as are registered global storage and the compiler-owned
arena. A global parent path overlaps all its descendants, regardless of how the access
was composed. Registration excludes compiler storage addresses and overlapping ownership.

Branch successors receive the incoming facts independently. Join bodies start with their
own parameter scope and empty facts. Calls also reset facts, including calls whose current
implementation happens to be read-only. This analysis is local and conservative; it does
not infer fresh-root separation or a fixed point over recursive calls and joins.

The separation between location aliasing and operation read/write behavior follows
[LLVM's alias-analysis interface](https://llvm.org/docs/AliasAnalysis.html).
[MemorySSA](https://llvm.org/docs/MemorySSA.html) provides the related dominance and
possible-clobber model. Cont's explicit normal/failure continuations supply the scope for
this implementation. Lean's LCNF passes consume Lean IR; this pass reuses Oria's typed
substitution and scope operations for its own indexed Cont.

Machine and DP121 consume the resulting check annotation. They preserve memory-operation
order and do not reconstruct alias facts from command text. The annotation is an internal
optimization result. Scoped typing and path restoration are proved; full native-heap
semantic preservation of the optimizer remains a proof obligation.
Presence alone does not establish numeric type. A retained scalar read still executes
its native numeric selection when only its success is demanded. An earlier successful
scalar read can supply both its value and its success through Cont's forwarding rule.

## Demand and dead code

[Machine dead-code elimination](../Oria/Compiler/Optimize/DeadCode.lean) uses the existing
whole-program demand analysis. If a function's return mask is \(\mu\), it first normalizes
its return vector:

\[
N_\mu(\bar v)_i =
\begin{cases}
v_i,&\mu_i=1,\\
0,&\mu_i=0.
\end{cases}
\]

Observed components retain their values. Unobserved positions remain padding in the
signature-indexed vector. Once two return successors agree, CFG simplification can remove
their distinguishing branch and then remove unreachable blocks.

A backward use-def traversal removes unused arithmetic, comparisons, ephemeral allocation,
tags, and immutable projections. Scoped substitution removes the corresponding binder
positions. Calls, commands, persistence operations, and native NBT operations retain their
execution positions. In particular, an ignored call can still contain a failure test that
skips a later world write; demand cannot remove that test while the two paths have different
effects.

The pass repeats after the total number of blocks and instructions decreases. Each round
recomputes demand for the rewritten program. Register allocation and caller-save analysis
run on the final CFG. This keeps their metadata tied to the program they analyze.

Bit analysis also permits `if b then return 1 else return 0` to return `b` directly.
The rewrite requires a bit-analysis fact that the word belongs to `{0, 1}` and two
successors containing only returns. Equal return components are preserved; unobserved
components use the canonical padding described above. Arbitrary I32 words and branches
containing effects do not satisfy this rule.

Lean's [LCNF constant folder](https://github.com/leanprover/lean4/blob/v4.31.0-rc2/src/Lean/Compiler/LCNF/Simp/ConstantFold.lean)
and [dead-binding pass](https://github.com/leanprover/lean4/blob/v4.31.0-rc2/src/Lean/Compiler/LCNF/ElimDead.lean)
provide the implementation reference. Their interfaces consume Lean declarations and LCNF;
Oria's passes operate on its own scoped Cont and Machine telescopes and reuse their
substitution and demand interfaces.

## Invocation resources

[Resource analysis](../Oria/Compiler/Lower/DP121/Resources.lean) summarizes each Machine
function after register allocation. It records arena allocation, projection scratch,
native-NBT scratch, command-macro arguments, persistent scratch, and stack storage.
Spill slots, return overflow, caller saves, and demanded Execute captures determine stack use.

The summary of a function includes its ordinary and Execute callees. Lean's Tarjan SCC
implementation computes the union for every recursive component in dependency-first order.
Each exported entry prepares and releases its own transitive resources. A scalar entry
can therefore coexist with arena-using or spilling entries without acquiring their storage
protocols. Native-NBT operations conservatively retain the arena protocol. Persistent-pack
readiness and panic checks remain part of the entry contract.

Execute freezes captured values before traversing selected contexts. Its outer frame exists
when captures or saved registers require it; the callee's spill frame is independently
controlled by the ordinary call convention. A direct, capture-free body with no observed
native channels can be the Execute target itself.

## Physical operations

The [arithmetic emitter](../Oria/Compiler/Lower/DP121/Arithmetic.lean) selects native
scoreboard `add`/`remove` for representable constant amounts. The DP121 constructors carry
nonnegativity proofs. `Int32.minValue`, whose positive magnitude exceeds Minecraft's
signed argument range, uses the general register operation. Operands are read before an
aliased result is published; allocation and spill conventions remain unchanged.
Commutative addition and multiplication place an operand already in the output register
on the left, avoiding a temporary save and reload.

[Transfer forwarding](../Oria/Compiler/Lower/DP121/Transfers.lean) replaces an immediate
reload of a just-written I32 storage leaf with a scoreboard copy from its initialized
source. If the source is already the destination, the reload disappears. The optimization
uses adjacent, unconditional compiler transfers with a valid scalar destination; calls,
native commands and intervening writes end the window. It retains the spill for later uses.

The persistent allocator captures success and result from one NBT read. Promotion of a
constructor with no recursive-copy actions copies its complete object into the allocation
draft and installs the persistent descriptor. The shared allocator supplies live-list and
mark metadata. The source-address memo still records the destination and layout plan, so
repeated references retain sharing. Constructors needing child promotion reserve and memoize
their destination before recursive traversal. GC and the allocation protocol consume the
same layouts in both cases.

## Native NBT lowering

[NBT lowering](../Oria/Compiler/Lower/DP121/Nbt.lean) prepares a typed selection's macro
fields directly from allocated locations. Preparation precedes result initialization, so
an output may reuse an input register after its argument has been copied. Multi-step
helpers that still read their input homes capture their final channels in the reserved
scratch registers and publish allocated results after returning. The register-layout
interface proves that ordinary registers and scratch registers are disjoint.

A typed set, append, or clear emits the native mutation with its structured selection.
Dynamic indices use typed macro parameters. Static command prefixes and suffixes are
assembled from the existing fragment algebra; the NBT encoder escapes strings, including
`$`, before literals enter a macro line.

I32 constants use `value`; allocated stack words use `from`; initialized score registers
use `compute default integer` with a fixed score provider. This selection happens after
register allocation, when the source's physical home is known. Static NBT values retain
their native tag and appear as SNBT literals.

Success comes from the native mutation. Set or copy of an equal value, and clear of an
empty array, fail because the target did not change. Missing compound keys can be created;
invalid list indices fail. A caller can explicitly handle Failure with `ignore`.

Each retained native primitive keeps its original execution position. Address preparation
is shared within that primitive. Cont forwards known scalar loads and records established
selection existence before physical register allocation.

## Reusing macro arguments

[Macro argument reuse](../Oria/Compiler/Optimize/MacroArguments.lean) runs after target
tail-path linearization. A local fact states that one macro field contains the current
I32 value of a score, a call-frame word, or an immediate. Repeating that preparation can
be omitted while the fact remains valid. The final command of a function is retained.

Score writes invalidate facts that depend on that score; swap invalidates both operands.
Stack mutation invalidates frame-word facts. Macro-field writes invalidate the affected
field, and writes to the complete macro compound invalidate every field. Conditional
writes invalidate conservatively. Facts start empty at every function entry.
An early-return guard retains incoming facts on its fallthrough path: the returning
branch cannot reach the following preparation.

Owned-document lowering marks native operations that preserve registers, frame words,
and the macro argument compound. The annotation stays attached to the structured target
invocation through sharing and linearization. Helper summaries are derived from target
constructors and these annotations. Opaque commands and calls invalidate the cache.
Capture destinations are processed as writes even when the enclosed native command fails.
Native NBT argument copies keep their own snapshot semantics; this pass reuses scalar fields.

## Backend sharing

[Sharing](../Oria/Compiler/Optimize/Sharing.lean) performs identical-code folding at the
DP121 encoding seam, after physical location selection. A candidate is identified by:

\[
(\text{complete command bytes},\ \text{plain or macro kind},\
  \text{ordered macro field schema}).
\]

The complete body is encoded through the existing `Std.Format` printer at width 120,
matching artifact output. `Std.HashMap` indexes these strings and compares complete keys;
hash collisions do not establish equivalence. Equal text alone is insufficient when macro
field types or codecs differ.

Only compiler-private definitions participate. Public entry resources and the
`__oria/load` and `__oria/tick` tag dispatchers retain their identities.
The first equivalent private definition becomes the representative. A typed
[reference traversal](../Oria/IR/DP121/Transform.lean) redirects direct calls, with-storage
calls, Execute bodies, and calls nested inside store/condition/return commands.
Call kinds, macro sources, parameter occurrences, line order, and execution context remain
unchanged. Every invocation still executes, including repeated calls with identical inputs.

Redirecting a callee can make its callers equivalent. Sharing repeats while definitions
are removed; file count is its termination measure. Recursive definitions are compared by
their current encodings. The pass does not infer graph isomorphisms between differently
named recursive cycles. Target construction checks unique identities, and the existing
call-closure checker certifies the resulting plain/macro reference graph before assembly.

[Tail-path layout](../Oria/Compiler/Optimize/Linearize.lean) runs between two sharing
rounds. The first round gives equivalent failure destinations a common identity. Layout
then splices a uniquely referenced private plain function into a tail-call site. An
explicit final return supplies the caller's return destination. For a conditional tail
edge, the other edge becomes an exit guard and the selected body follows it:

```text
if c then return f() else return g()
  = if not c then return g(); body(f)
```

The rewrite requires one structured reference to f and an explicitly returning body.
Use counts include scheduled, Execute, and macro-body references. Public entries and tag
dispatchers retain their identities. A changing round removes a definition; the final
sharing round folds equivalent resulting bodies. This transformation runs after task
region costs are bounded and removes function transitions, so those bounds remain
conservative.

This organization follows the definition-merging and caller-reconsideration approach of
[LLVM's MergeFunctions](https://llvm.org/docs/MergeFunctions.html). Oria's comparison is at
the final command encoding seam, where register names, storage paths, and complete macro
contracts are available. No command parsing or text replacement is used to redirect calls.

## Validation

- [ContOptimize](../Oria/Proofs/ContOptimize.lean) proves scalar folding equations.
- [Path](../Oria/IR/Common/Nbt/Path.lean) proves path and write capture/restoration;
  [Memory analysis](../Oria/Compiler/Analysis/Memory.lean) proves signed-index separation.
- [Memory acceptance](../Oria/Proofs/Fixtures/Memory.lean) compiles source programs covering
  parameter aliasing, dynamic and signed indices, parent replacement, resizing, failure
  recovery, call barriers, and joins. Native tests run register-backed and all-spill packs;
  final-artifact checks verify scalar forwarding and retained writes.
- [Transform](../Oria/IR/DP121/Transform.lean) proves identity renaming and preservation of
  macro parameter occurrences.
- [CommandPlan](../Oria/IR/DP121/CommandPlan.lean) proves that static syntax around a
  selection preserves its macro parameters.
- [Elaboration acceptance](../Oria/Proofs/Fixtures/RecursionRuntime.lean) exercises shared
  path scopes, repeated string writes, escaped literals, negative indices, I32 wraparound,
  and bounds failure in register-backed and all-spill builds.
- [Sharing](../Oria/Proofs/Sharing.lean) checks chained sharing, preserved public resources,
  and distinct macro schemas with equal command text.
- [WordLower](../Oria/Proofs/WordLower.lean) checks native channels through named calls.
- [Optimization](../Oria/Proofs/Fixtures/Optimization.lean) compiles through final datapacks
  with register budgets 128 and 6. Its artifact checks cover literal encoding, dead effects,
  dead arithmetic, shared macros, entry resources, empty capture frames, and grouped record
  projections. Native acceptance checks repeated effects, retained failure short-circuiting,
  overflow, division, minimum-I32 immediates, bit returns, projections, and invocation cleanup.
  Persistent acceptance additionally checks promotion sharing, root replacement, collection,
  slot reuse, and runtime NBT values.

These checks complement scoped types and closure certificates. Semantic preservation of
the complete demand analysis and optimization pipeline remains an unproved obligation.
