# Discovery and interaction

Oria targets Minecraft Java 26.3 / DP121. This group adds native location queries,
source-attributed chat, server information, and group score updates. The functions retain
Minecraft's success bit and integer result through normal and failure exits.

## Interfaces and results

| Interface | Native command | Success payload |
| --- | --- | --- |
| Locate.structure | locate structure | Floored horizontal distance |
| Locate.biome | locate biome | Floored three-dimensional distance |
| Locate.poi | locate poi | Floored horizontal distance |
| Chat.say | say | 1 |
| Chat.me | me | 1 |
| Chat.tell | msg | Selected recipient count |
| Chat.team | teammsg | Selected team-recipient count |
| ServerInfo.players | list / list uuids | Online player count |
| ServerInfo.seed | seed | Low signed 32 bits of the world seed |
| ServerInfo.version | version | 1 |
| Scoreboard.add / remove | scoreboard players add / remove | Sum of resulting scores |

An integer zero can be successful. Team chat from a non-player teammate can have zero
online recipients. Adding zero to scores can also succeed without changing their values.
Command success describes native processing, not network delivery or client acknowledgement.

## Message construction

Native chat uses Minecraft's greedy message grammar. Text-component commands such as Tellraw
use SNBT. Message is a shared codec for native chat, with constructors that establish context
requirements before lowering.

| Constructor | Contents | Requirements |
| --- | --- | --- |
| String literal / ofString | Nonblank, single-line text without selector markers | none |
| selector | Structured entity-name expansion | Selector requirements |
| number | Static or dynamic I32 in decimal spelling | none |
| native | Checked single-line native message syntax | all |
| join | Space-separated complete messages | Union of members |

```lean
Chat.say "The arena is ready."
Chat.tell .self "Choose a move."
Chat.team "Regroup."
Chat.me "waves"

Chat.say (Message.join "Player"
  [.selector .self, "scored", .number (.dynamic n)])
```

Join requires a first message and a list of remaining messages. It inserts a space between
each pair. This separation is part of the contract: appending a bracketed suffix directly
to an unfiltered selector could turn text into selector arguments and introduce requirements
that were absent from the original selector. Joining all-players with a text suffix produces
`@a [distance=..1]`, with a space before the suffix.

Plain strings reject control characters, blank content, selector markers, and macro
substitutions. Use parse for computed host strings. Native message text uses the existing
Inline validation and delegates grammar to Minecraft; its full-context requirement covers
opaque selectors. Literal validation uses Lean's standard cbv evaluation followed by simp
and decide, producing kernel-checkable evidence usable in inferred public types.

The fragment implementation reuses Inline, Selector, Scalar, Fragment.spaced, and ArgCodec.
There is no runtime message AST. A dynamic integer becomes a typed macro hole; the rest of
the message stays static.

## Chat context and routing

Plain say and me messages do not need an executor: a server source has its own native name.
Selectors inside the message can add executor, position, rotation, dimension, or anchor
requirements. Tell adds the selected players' requirements. Team always needs an executor;
membership in a team is checked by Minecraft at execution time.

Team chat uses current native membership. Its count includes a player sender;
a non-player executor can send to online members of its team. An executor with no team fails.
Minecraft suppresses source feedback during function execution. Private messages retain
recipient delivery, while the sender's outgoing echo is suppressed for both private and team chat.

Messages produced by datapack functions follow Minecraft's native message-resolution path.
Signed input can involve filtering and ordering facilities; these wrappers do not wait for
client delivery. Their grades retain the existing world/selection/chat effect bound.

## Native location queries

All Locate functions require position and dimension. ResourceOrTag supplies host registry
IDs or tags. Coordinates remain operator feedback; the program receives the distance integer.
The interface does not decode feedback text into a runtime vector.

Structure lookup follows the generator's placement policy with a native bound of 100.
Random-spread search advances according to structure placement spacing; concentric-ring
placements use their ring positions. A fixed block-radius interpretation would be inaccurate.
Missing structures and invalid structure resources fail.

Biome lookup uses a 6400-block search radius with horizontal/vertical sample steps of 32/64.
POI lookup uses a 256-block radius and accepts any occupancy state. Its result is horizontal
distance even when the selected POI differs in height. Native sampling, candidate selection,
and floating-point distance calculations determine the exact result.

Searches can be expensive. The library leaves query timing to the caller.
[reportMeetingDistance](../Oria/Examples/StandardLibrary.lean) shows a query inside as/at so
each player supplies the origin of their own search.

## Group score updates

```lean
Scoreboard.add (.one .self) "demo.points" (.static 1)
Scoreboard.remove (.entities (.selector .allPlayers)) "demo.points" (.static 2)
Scoreboard.add (.one (.named "#counter")) "demo.points" (.dynamic amount)
```

Holders reuses single holders, entity selectors, and the native tracked-holder wildcard.
The objective must exist. Missing scores begin at zero. Amounts must be nonnegative, while
resulting scores may be negative. Dynamic bounds are checked by Minecraft.

The return value is the sum of resulting scores. Both each update and the sum follow I32
overflow behavior. The wildcard addresses the scoreboard's tracked holders across objectives,
not just holders that already have a score in the selected objective. It can create scores
for additional tracked holders. Generated runtime objectives should remain outside
application mutations.

## Server information

Players returns the online count. The UUID option changes the native report format.
Version returns 1; its payload is not a version identifier. Ordinary function execution
suppresses these report texts, so generated programs consume their integer results.

The native seed report contains the complete 64-bit world seed, while Java's long-to-int
conversion returns only its low signed I32 bits. Functions suppress the report; this interface
cannot recover the full seed from its payload. It requires the current dimension.
Players and version use server-wide information and need no implicit execution context.

## Verification and sources

The [utility fixture](../Oria/Proofs/Fixtures/Utility.lean) compiles the interfaces with a
separate [golden](../tests/golden/utility.dp121).
[StdUtility](../Oria/Proofs/StdUtility.lean) proves context summaries and checks lexical
validation, selector separation, exact command text, and numeric holes.

[Native acceptance](../integration/rps/UtilityAcceptance.java) checks chat packet kinds and
recipient routing, operator feedback, POI distance, generator-based searches, grouped score
results, zero results, overflow, and invalid dynamic amounts. Location expectations use the
pinned native generator's search policy.

The reference is the server in
[minecraft-26.3.lock.json](../minecraft-26.3.lock.json), particularly LocateCommand,
MessageArgument, the four native chat commands, ListPlayersCommand, SeedCommand,
VersionCommand, ScoreboardCommand, and CommandResponseTracker.
The command-family history is recorded in the
[22w19a release notes](https://feedback.minecraft.net/hc/en-us/articles/6189944134541-Minecraft-Java-Edition-Snapshot-22w19a),
and the version command in the
[1.21.6 release notes](https://www.minecraft.net/en-us/article/minecraft-java-edition-1-21-6).

The additions use the existing command declarations and argument codecs. IR, command-result
demand analysis, and datapack lowering are unchanged.
