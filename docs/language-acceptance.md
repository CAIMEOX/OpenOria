# Language acceptance

[RoundLedger](../Oria/Examples/RoundLedger.lean) is a small cumulative round ledger. It
combines record construction, region-polymorphic calls, explicit promotion, root replacement,
failure recovery, runtime branches, and finite host-generated code. Its public datapack
entries provide observable results through `ledger.points`.

Run the Lean contracts and native Minecraft acceptance:

```bash
lake build Oria.Proofs.LanguageExample
./scripts/rps-test --language
```

The server runner compiles the example, writes two datapacks, and invokes their public
entries in the pinned Minecraft 26.3 / DP121 server. `ledger` uses the normal 128-register
budget. `ledgerstack` uses budget 6: four scratch and two result registers, with ordinary
values and overflow arguments in stack locations. Both runs use the same behavioral assertions.
Each invocation also checks that transient stack and arena storage has been released.

Build the example independently:

```bash
lake exe oria-ledger output/ledger
lake exe oria-ledger output/ledgerstack --stack
```

The destination must be absent or empty. Installing either pack creates `ledger.points`
on load and initializes its own persistent root. For example, invoke `ledger:reset`, set
`#visits` to zero, set `#input` to 1, and invoke `ledger:round`. Input 1 records a win,
2 records a loss, and 0 records a draw. `ledger:snapshot` publishes the current tally to
`#total`; `ledger:gc` runs manual collection after the ordinary entry has returned.

## Observable contracts

The tally of a record is `100 * wins + 10 * losses + rounds`. Control traces append decimal
digits to `#trace`, making execution order and repeated suffixes observable. The reporting
wrapper writes `#status = 1` and the returned payload on success; failure writes
`#status = 0` and `#result = -999`. Outputs are initialized to sentinels before assertions
so an omitted write cannot reuse a preceding case's result.

| Entries | Contract checked on the server |
| --- | --- |
| `records` | Updating `(2, 3, 5)` produces `(3, 3, 6)`; the original still tallies to 235 while the new value tallies to 336. |
| `round`, `snapshot` | Win, loss, and draw invocations accumulate 101, 112, and 113 in the persistent root. The shared visit update runs once per successful round. |
| `round` | An absent score or invalid input fails before committing a record; the previous tally and visit count remain visible. |
| `durable-records` | A previously read persistent value remains 113 after root replacement publishes 214. |
| `gc`, `snapshot`, `round` | Collection preserves the current root, and a later invocation can update it to 225. |
| `round`, `gc` | A failing visit read after the commit retains the already-published record, which survives collection with tally 326. |
| `control` | Negative, zero, and positive inputs yield traces 1, 124, and 134. The common suffix executes exactly once on continuing paths. |
| `control` | A failed command in the selected branch retains trace 1 and skips later effects. |
| `selection` | Integer alternatives yield 125, 135, and 145, each with one shared suffix. |
| `selection`, `nested` | A selected early return skips the suffix; an inner block return resumes its outer continuation. |
| `recovery` | A captured successful zero remains zero; an absent input becomes the explicit fallback -7, followed by trace 9. |
| `ignored` | Explicitly ignoring the failed read permits trace 7 and successful zero. |
| `batch` | A host list generates calls in order: 234 from zero, then 8234 and 8234234 across repeated invocations from seed 8. A failed initial read stops the batch. |
| `empty-batch` | The empty list succeeds with zero, retaining an existing trace or its absence. |
| `loop-control` | Continue skips digit 2; break terminates iteration while the outer suffix appends 9. |
| `loop-return` | Return from an iteration ends the enclosing object block; earlier effects remain visible. |
| `collections`, `native-loop` | Array and bounded-range iteration retain source order. Successful native command payloads are ignored in Unit-returning loop bodies. |
| `map`, `bind` | Mapping preserves failure; a dependent continuation executes once on success and is skipped on failure. |
| `fallback`, `orelse`, `is-success` | Fallback effects occur only on failure, retries preserve their own failure, and successful zero sets the success flag. |

[LanguageExample](../Oria/Proofs/LanguageExample.lean) proves equations for nine inferred
function grades. These check the public requirement/effect contracts through Lean's type
checker. The native tests cover command behavior, physical calling conventions, object
layout, and invocation lifetime, which those grade equations do not express.

## Source forms exercised

The result type remains explicit while the body determines its grade:

```lean
@[mcfunction]
def records := show Prog _ Unit from do
  let s : Val Stats ← {wins := 2, losses := 3, rounds := 5}
  let next ← won.call s
  let before ← tally.call s
  let after ← tally.call next
  (Scoreboard.set (.named "#old") scores (.dynamic before)).ignore
  (Scoreboard.set (.named "#new") scores (.dynamic after)).ignore
```

The record functions use projections and immutable updates. `won` allocates a fresh ephemeral
record; `durableRecords` explicitly calls `persist` before replacing the root. `tally`
accepts either arena through its region parameter. The batch uses ordinary `for` over a
finite host list. [Source programs](source-programs.md) describes inference, records,
pattern bindings, and control-flow semantics.

The local result of a statement branch is Unit. Binding uses the continuation's normal
result carrier. The return destination separately retains the enclosing block's result type.
In `control`, command statements within Unit-returning branches propagate failure through
the enclosing Int32-returning block.

The named-call builder also currently ties region-polymorphic parameters to one shared
region. `advance` accepts ordinary arena-neutral arguments; `won` and `tally` independently
exercise region-polymorphic calls. Use arena-neutral signatures when parameters can have
different regions.
