# Integration acceptance

The native suites compile Lean source through Tree, Cont, Machine, and DP121, write the
resulting datapacks, load them into Minecraft, and check observable behavior.
Separate artifact tests compare emitted files and a downstream Lake suite checks library use.

## Runners

| Command | Scope |
| --- | --- |
| `scripts/quality` | Theorems, behavior/diagnostic checks, documentation, final artifacts, and downstream Lake acceptance |
| `scripts/gametest` | Compiler runtime, core commands, invocation memory, persistent memory, and runtime NBT |
| `scripts/rps-test` | Player game, command arguments, and native command-family acceptance |
| `scripts/rps-test --language` | RoundLedger records, regions, control flow, recovery, and persistent state |
| `scripts/rps-test --admin` | Administrative state, tick control, permissions, transfers, and bulk scores |
| `scripts/rps-test --tasks` | Cooperative parking, recursive continuations, quota, cancellation, and task memory |
| `scripts/rps-test --merge-sort` | Native-list sorting, full output comparison, checkpoints, and buffer lifetime |
| `scripts/rps-test --globals` | Typed global storage, reload/schema gates, native copies, and task interference |
| `scripts/lake-test` | Isolated downstream-package builds and incremental datapack export |

The server runners use Java 25 and verify the server SHA-1 from
[minecraft-26.3.lock.json](../../minecraft-26.3.lock.json).
Set `ORIA_JAVA` and `ORIA_SERVER_JAR` to use an existing installation.
The default server path is `.lake/minecraft/server-26.3.jar`.
Downloads are managed separately from acceptance.

Runs create isolated `.lake/gametest.*`, `.lake/rps-test.*`, or `.lake/lake-test.*` directories.
Server runs retain their packs, world, logs, and XML report.
One GameTest registration executes many cases and assertions; XML test counts do not
measure command or language coverage.

## Core runtime

[scripts/gametest](../../scripts/gametest) uses Minecraft's native GameTest entry point.
Its driver checks:

| Area | Scenarios |
| --- | --- |
| Artifact and callbacks | Initialization before user callbacks, registration order/repetition, load/tick tags, shared public aliases, normal Unit success/result |
| Calls | Typed arguments/results, long chains, shared-callee trees, 24 arguments, retained locals, caller saves, spills, and stack parameters |
| Recursion | Sum, Fibonacci, lexical captures, nested helpers, and self-tail loops |
| Source values | Regular recursive data, Unit fields, Option payloads, records, and cross-function transport |
| Value types | Zero-/one-/multiword products, nested fields, recursive calls, sparse demand, multiword roots and Ref snapshots, boxed parents, reload and GC at budgets 128 and 6 |
| Failure | Failure short-circuiting, successful zero, explicit Option materialization, recovery, and cleanup |
| Optimization | Scalar constants and overflow, dead arithmetic and branches, ignored named-call results, shared macros, repeated effects, and preserved failure short-circuiting at budgets 128 and 6 |
| Persistent memory | Promotion sharing, mixed arena references, Ref cycles, old local references after replacement, manual GC, free-slot reuse, load preservation, and schema mismatch |
| NBT | Integer widths, arrays, mixed lists, escaping, negative zero, and extreme finite doubles |
| Data and Compute | Storage CRUD, insertion/selection, string slicing, entity/block NBT, typed dynamic provider inputs, integer overflow/zero failure, explicit float conversion, dynamic paths, and native failure behavior |
| Execute | Context changes, conditions, captured values, branch invocations, result receivers, and cleanup |
| Runtime snapshots | readOne/readAll cardinality, empty results, filters, dynamic indices, native copy, ADT/function transport, macro serialization, persistence, and GC recovery |
| Scoreboard and trigger | Objective setup/removal, missing scores, resets, trigger enable and non-player failure |

Calls use budgets 128, 8, and 6.
Register and recursion fixtures include all-stack variants; Execute also has an all-stack pack.
Runtime NBT uses budgets 12 and 6.
The tests check invocation arena, stack, draft, and temporary storage cleanup as applicable.

The suite also runs the [elaboration examples](../../Oria/Examples/Elaboration.lean):
shared pure expressions, nested record updates, object patterns, local Fibonacci and tail
recursion, host recursion, typed native reads/writes, and bounds-failure recovery. It runs
both register-backed and all-spill builds, including equal string assignments, macro-like
literal text, negative indices, and I32 wraparound. `flow-artifact-test` compares the complete final
datapack for a pure let with the corresponding explicit bind.

The fixtures live in [Oria.Proofs.Fixtures](../../Oria/Proofs/Fixtures).
Driver functions live in [integration/datapack/driver](driver).
The structure asset uses Minecraft accept/fail test blocks to report the aggregate result.

## Player and command families

[scripts/rps-test](../../scripts/rps-test) registers native ServerPlayer instances with
embedded connections. It inspects world state, scoreboard state, and outgoing packets.

[PlayerAcceptance](../rps/PlayerAcceptance.java) runs the command-family checks and the complete
[rock-paper-scissors game](../../docs/rock-paper-scissors.md):
all nine move pairs, first-to-two endings, draws, invalid values, trigger locking,
two independent players, failed draws, recovery, chat, actual resource reload, and production
tick processing.

The additional native groups cover:

| Group | Scenarios |
| --- | --- |
| Shared arguments | Constant/typed providers without an executor, numeric failures, structured selectors, decimal/integer/mixed coordinates |
| Entities | Kill, Summon, Effect, mixed selections, passengers, duplicate UUID failure, runtime compounds, and duration variants |
| Presentation | Tags, title/action-bar packets, timings, sound routing/filtering, stop filters, particles, and post effects |
| World and players | Weather, clocks/timelines, difficulty, borders, modes, experience, recipes, enchantment, damage, and advancement graphs |
| Management | Bossbar and team properties/membership, fake holders, repeated updates, and native zero results |
| Gameplay control | Game rules, attributes, forceload, cameras, riding, respawn data, rotation, safe-ground placement, and display formats |
| Items and blocks | Component patches/predicates, slots, modifiers, loot, runtime NBT, set/fill/clone modes, and cross-dimension copies |
| Execute | Structured conditions, context transforms, multi-subject bodies, capture, and receivers |
| Generation | FillBiome, named/inline features, templates, jigsaw, structure placement, waypoint icons, and stopwatches |
| Discovery and interaction | Locate, chat routing, dialog packets, server information, and numeric score operations |

The [Batch fixture](../../Oria/Proofs/Fixtures/Batch.lean) combines world, player, management,
control, movement, display, item, block, and execution entries at budget 6.
[Generation](../../Oria/Proofs/Fixtures/Generation.lean) and
[Utility](../../Oria/Proofs/Fixtures/Utility.lean) use separate compiled packs.
Final command text and macro writes are checked by artifact snapshots before native execution.

## Language acceptance

`scripts/rps-test --language` builds
[RoundLedger](../../Oria/Examples/RoundLedger.lean) with budgets 128 and 6.
The same observations check record construction/projection/update, original-value
preservation, region-polymorphic calls, explicit promotion, root replacement, GC,
Failure combinators, command failure, fallback, early return, shared branch continuations,
pattern bindings, and finite host loops with break/continue.
See [the case contracts](../../docs/language-acceptance.md).

## Administrative acceptance

`scripts/rps-test --admin` runs [AdminAcceptance](../rps/AdminAcceptance.java) in a separate server.
It checks function compilation permissions, tick rate/freeze/step/sprint, whitelist and
ban state, operators, idle timeout, grouped scores, and transfer packets.
The fixture restores mutated administrative state where needed.

The GameTest server is unpublished: Kick's native publication guard is exercised.
Transfer checks the requested packet, not a completed connection to another server.

## Cooperative tasks

`scripts/rps-test --tasks` runs the [Tasks fixture](../../Oria/Proofs/Fixtures/Tasks.lean)
with default registers and an all-spill configuration. The server command quota is 512.
[TaskAcceptance](../rps/TaskAcceptance.java) checks non-tail recursive returns, retained
locals and arena objects, self-tail backedges, multiword results, exact effect counts,
ordinary entries between slices, persistent
publication, Failure recovery, busy submission, and collector exclusion. It also checks
atomic background entries, cancellation ownership and workspace cleanup, replacement
submission, and a quota reduced to 64 that cannot admit a region.

The runner fails if Minecraft reports command-quota exhaustion. Artifact acceptance verifies
that an ordinary synchronous pack emits no task runtime. See [cooperative tasks](../../docs/tasks.md).

## NBT sorting

`scripts/rps-test --merge-sort` builds [MergeSort](../../Oria/Examples/MergeSort.lean)
with default registers and an all-spill configuration. The server and slice quotas are 2048.
Complete output lists are compared with Java integer sorting, and input tags are preserved.
Cases include empty and singleton inputs, duplicates, negative values, I32 extrema,
repeated sorted inputs, 65 reversed elements, and 129 deterministic random elements.
The suite checks budget parking, a two-object arena bound, workspace cleanup, numeric-read
failure, cancellation, and successful resubmission. A typed-document fixture also covers
derived nested fields, native copies, equal writes, empty clearing, bounds failures,
cross-function aliases, and direct reads from persistent snapshots.
The [memory fixture](../../Oria/Proofs/Fixtures/Memory.lean) adds seven groups at budgets
128 and 6: scalar store forwarding across disjoint-field writes, aliased parameters and
dynamic indices, positive/negative index aliasing, list resizing and parent replacement,
call barriers, failed writes, and branch joins. The native assertions inspect each entry's
success channel. `typed-nbt-artifact-test` checks that the forwarded read is absent from
the final commands while its write remains; `flow-artifact-test` checks the dominated
setter's existence precheck.
The join cases use indexed assignment syntax inside non-tail branches. They also check
unselected out-of-bounds writes, failure short-circuiting, exactly-once continuation
effects, early return, and host-iteration bodies.
Command-quota exhaustion fails the runner.
See [the example guide](../../docs/merge-sort.md).

## Native global storage

`scripts/rps-test --globals` runs registered native documents at register budgets 128 and 6.
Both packs reuse the same global declarations and typed source functions. A scalar pack
changes only `Spec.settings.ns` and checks that its data is isolated from the original pack.
An additional all-spill pack retains a global snapshot in a managed root, changes the native
source, and checks both values after collection and reload.
It checks first-load contents, cross-entry updates, matching-schema reloads, global/arena
copies, immutable snapshots, equal writes, dynamic and negative indices, whole-document
replacement, disjoint roots, and external-command invalidation. Schema mismatches and missing
initialized roots gate entries without reseeding their contents. A suspended task must read
an ordinary entry's intervening update after it resumes.
Field deletion and replacement with a different native tag must make the corresponding
numeric read fail, including when only its success is observed. Typed writes can recreate
missing compound fields; repeated equal writes and out-of-bounds writes retain native failure.

`global-nbt-artifact-test` fixes a scalar-only pack's final output and checks that static
global access uses neither arena allocation nor function macros. Source diagnostics and
kernel proofs cover registration, field-only root paths, codec correspondence, and absolute
path normalization. See [GlobalNbt](../../Oria/Proofs/GlobalNbt.lean).

## Downstream Lake acceptance

[scripts/lake-test](../../scripts/lake-test) copies the
[consumer project](../lake) to an isolated directory.
[LakeBuild](../../tests/LakeBuild.lean) checks:

- Default facets export a private pack and its imported function dependencies.
- Unchanged builds preserve output timestamps.
- Missing generated files are restored.
- Imported-source changes update the compiled output.
- Renamed entries and removed pack declarations update the generated-file inventory.
- Application-owned files survive inventory cleanup.

This suite is included in `scripts/quality`.

## Coverage boundaries

These are selected behavioral contracts, not exhaustive combinations of all command
overloads, selectors, parser errors, dimensions, or world states.
Native ServerPlayer and packet inspection do not test network login, client rendering,
audio playback, or the visual contents of dialogs.

Reload is exercised by the game; a complete process restart with retained persistent
storage, crashes during execution, large-heap stress, and elapsed-time benchmarks are separate
acceptance concerns. The language's fatal-failure model provides no crash recovery.
See [persistent memory](../../docs/persistent-memory.md) for its execution contract.
