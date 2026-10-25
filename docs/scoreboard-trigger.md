# Scoreboards and player trigger input

These interfaces target the server pinned in `minecraft-26.3.lock.json`.
They use ordinary command declarations and codecs, followed by the existing compiler pipeline.

## Interface contracts

| Interface | Success payload | Requirements and failure |
| --- | --- | --- |
| `Scoreboard.Objectives.add objective criterion` | Total objective count after creation | No executor required; an existing name fails and retains its criterion and scores |
| `Scoreboard.Objectives.remove objective` | Remaining objective count | No executor required; a missing objective fails |
| `Scoreboard.reset holder objective` | 1 | Holder context required; missing objective or unresolved holder fails; an absent score still succeeds |
| `Scoreboard.resetAll holder` | 1 | Holder context required; removes this holder's scores across objectives, including trigger authorization |
| `Scoreboard.enable holder objective` | 1 | Holder context required; objective must be trigger; an already-unlocked score fails |
| `Trigger.run objective` | Updated score after adding 1 | Executing player must have an enabled trigger score |
| `Trigger.add objective value` | Updated score | Same authorization; signed static or dynamic I32 delta |
| `Trigger.set objective value` | Written score | Same authorization; signed static or dynamic I32 value |

Score holders are singular: a named holder or self. Apply `Execute.forEach` to operate on
multiple selected players. Objective operations and trigger enabling declare scoreboard
read/write effects. Reset uses the existing scoreboard-write grade. Trigger operations
require `Req.executor` and scoreboard read/write effects. Whether the executor is a player,
the objective is a trigger, and the score is unlocked are runtime checks that may take the failure exit.

`Criterion.dummy` and `Criterion.trigger` cover explicit state and player input.
`Criterion.named` accepts another validated native token, such as
`"minecraft.used:minecraft.carrot_on_a_stick"`. Minecraft validates native criterion names
when parsing the command. Objective display components and display-slot management are
outside this batch's interface.

The implementations retain native return values. Objective counts are global to the server.
An objective removal can return a successful zero; failure propagation uses the native success bit.
An enabled trigger accepts a successful write of zero and still consumes its authorization.

## Initialization and input processing

Create the trigger objective during load and deliberately ignore duplicate-name failure:

```lean
@[mcfunction]
def setup : Prog Scoreboard.objectiveGrade.handled Unit :=
  (Scoreboard.Objectives.add "game.choice" .trigger).ignore
```

Existing scores survive this initialization. A conflicting existing criterion is retained
as well; enabling it subsequently fails. Objective removal belongs to explicit teardown.
Use separate application objectives. The compiler's objective, normally namespace.oria,
stores its registers and runtime state and must remain available during generated execution.
Resetting all scores of a named holder also affects that name in other objectives.

Enabling a missing trigger score creates it at zero and unlocks it. A successful trigger
locks the score before applying the numeric change. Another submission requires enabling
it again. Setting the numeric score preserves the lock state. Resetting the score removes
the score and its authorization, and the next enable starts it at zero.

[The trigger example](../examples/Trigger.lean) registers load and tick callbacks. Each tick
selects all players, enables their input, reads its value, and echoes nonzero input after
setting it back to zero. The example treats zero as an empty input slot. This is application
policy; native trigger writes of zero remain successful operations.

```bash
lake exe oria-trigger output/trigger
```

Install the resulting directory under the world's datapacks directory and run `/reload`.
An ordinary player can then submit `/trigger input.choice set 3` and receive the numeric
message. A later tick re-enables input. Repeating `/reload` preserves existing scores.

## Verification

`Oria.Proofs.StdScoreboardTrigger` checks criterion requirements, executor requirements,
Execute context provision, command rendering, and dynamic macro fields. The finite command
catalog retains its signature/template checks. No IR or compiler intrinsic was added.

`Oria.Proofs.Fixtures.ScoreboardRuntime` compiles through the full pipeline with a register
budget of 6. The command snapshot is `tests/golden/scoreboard.dp121`; `scripts/quality`
checks it through `scoreboard-artifact-test`. `scripts/gametest` deploys that same artifact
and checks initialization, objective counts, duplicate and missing objectives, reset scope,
trigger enabling, and failure/recovery control flow under a non-player executor.

`scripts/rps-test` installs this fixture alongside the playable game. Native ServerPlayer
instances exercise successful run/add/set, dynamic zero and negative arguments, authorization
consumption, and repeated-call failure. The game also checks permission-free `/trigger`
input and re-enabling between ticks. See [rock-paper-scissors acceptance](rock-paper-scissors.md).
For an interactive check with the fixture installed and operator permissions available,
use this sequence while executing as the player:

1. Run `/scoreboard players reset @s sbtest.choice`, then
   `/scoreboard players enable @s sbtest.choice`.
2. Run `/function sbtest:trigger`. Expect `#status = 1` and `#result = 1` in `sbtest.oria`.
3. Run it again without enabling. Expect `#status = 0`; the player's score stays 1.
4. Enable again, set `#n` in `sbtest.oria` to 0, and run `/function sbtest:trigger-set`.
   Expect successful zero, followed by failure on an immediate second call.
5. Enable again, set `#n` to -3, and run `/function sbtest:trigger-add`.
   Expect successful -3 and a consumed authorization.

These contracts were checked against the pinned server's `ScoreboardCommand`,
`CommandResponseTracker`, and `TriggerCommand` implementations and the generated datapack.
