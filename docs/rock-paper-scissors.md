# Rock-paper-scissors

The [game module](../Oria/Examples/RockPaperScissors.lean) implements a first-to-two match
for each online player. It uses Scoreboard, Random, Tellraw, and Execute with the existing
Tree → Cont → Machine → DP121 pipeline.
The outcome branches use `.draw`, `.win`, and `.lose`; their expected result type selects
the object constructors. See [type-directed construction](object-construction.md).
Move decoding, round scores, and input state use [integer literal patterns](integer-patterns.md).

## Install and play

From the Oria repository, generate a fresh output directory:

```bash
lake exe oria-rps output/rps
```

Install `output/rps` in the world's `datapacks` directory on the server pinned by
`minecraft-26.3.lock.json`, then run `/reload`. The pack registers load and tick callbacks.
Each new player receives instructions on the next tick. Players need no operator permissions.

| Command | Action |
| --- | --- |
| `/trigger rps.input set 4` | Start or restart a match at 0-0 |
| `/trigger rps.input set 1` | Rock |
| `/trigger rps.input set 2` | Paper |
| `/trigger rps.input set 3` | Scissors |

The computer samples one move from the named sequence `rps:computer` for each accepted
round. Messages announce that move and the outcome. Draws leave both scores unchanged.
A second win finishes the match at 2-0 or 2-1. The final score remains until a restart.
Submitting a move without an active match displays the start command.

## State and command results

| Objective | Meaning |
| --- | --- |
| `rps.input` | Trigger input; 0 is the empty slot |
| `rps.active` | 1 during a match, 0 before starting or after finishing |
| `rps.player` | Player's round wins |
| `rps.server` | Computer's round wins |

Each objective uses the player's score holder. Minecraft saves these scores with the world.
Load creates missing objectives and preserves existing scores. These names are owned by
the example; reserve them for this pack and retain their declared criteria.
The compiler uses `rps.oria` for its own runtime bookkeeping.

A successful native trigger locks further submissions until the next polling pass. The
handler enables the trigger, reads the input, and resets nonzero input before processing it.
Minecraft executes that handler within one tick. An immediate second trigger cannot replace
the first pending move. Zero is accepted by Minecraft but interpreted as no input by the game;
other out-of-range values produce a help message without changing the match.

Scoreboard commands propagate failure; messages use `.ignore` so processing can continue
when delivery fails. A failed computer draw leaves the scores unchanged and consumes the input. Named
calls pass typed `Choice` and `Outcome` enums; their values and temporary storage are local
to the current invocation.

## Acceptance

```bash
./scripts/quality
./scripts/rps-test
```

The quality gate elaborates the game, collects its dependencies, and compiles both the
playable artifact and deterministic acceptance artifact. The server test then checks:

- All nine move pairs through the compiled `judge` and enum calling convention.
- New-player initialization, start/restart, draws, 2-0 and 2-1 endings in either direction.
- Invalid inputs, a successful zero input, idle polling, and moves after a finished match.
- Two simultaneous players, distinct scores, trigger locking, and permission-free input.
- A failed draw, failure propagation, input consumption, and subsequent recovery.
- Chat packet contents, including exactly one computer announcement for a production round.
- An actual resource reload, score preservation, and automatic production tick processing.
- Invocation storage cleanup with the acceptance pack's all-stack register budget of 6.
- Cross-function nested integer patterns at the signed I32 endpoints and negative values.
- Compiled Trigger run/add/set success, dynamic arguments, and repeated-submission failure.

The acceptance fixture supplies a typed fixed computer move to `receive`; the production
pack supplies the random action. The game logic is shared. The random production path runs
under the normal tick tag after reloading the actual pack.

The runner verifies the pinned server checksum and registers its test using Minecraft's
`TestFunctionLoader`. Named `ServerPlayer` instances join through the native player list
with Netty embedded connections. This exercises server commands and inspects outgoing chat
packets. Client rendering and network login are outside this test's scope.
Artifacts, logs, the test world, and the XML report are retained in `.lake/rps-test.*`.
