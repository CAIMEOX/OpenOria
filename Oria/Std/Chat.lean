module

public import Oria.Std.Command.Arg.Message
import Oria.Std.Command.Declarations.Utility
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Native chat

Say and me broadcast messages with native source attribution. Tell sends private messages;
team addresses the executor's current team. Messages use Minecraft's greedy message grammar,
including entity-name expansion, rather than the SNBT text-component grammar used by Tellraw.

String literals construct plain Message values. Message.selector and Message.number add
structured selection and static/runtime integers. Message.join inserts separating spaces;
Message.native accepts native message syntax with a conservative full-context requirement.
Command success describes native processing, not client delivery or acknowledgement.
Minecraft functions suppress source feedback. Incoming private messages are delivered;
the source's outgoing echo is suppressed.
-/

namespace Oria.Std.Chat
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Combine message and recipient requirements with chat and native selection effects. -/
@[expose] public def grade (message : Message) (req : ReqRow := Req.none) : Grade :=
  ⟨req ||| message.requirements, Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.chat ||| Eff.failure⟩

/-- Broadcast a source-attributed message and return 1, including when no players are online.
Selector resolution follows native permissions and failure rules. -/
public def say (message : Message) : Prog (grade message) Int32 := do
  emit <| Command.Declarations.chatSay.call <| .cons (encode message) .nil

/-- Privately message selected players and return their count. Recipient delivery remains
active in functions, while native source feedback is suppressed. An unresolved player target fails.
Target and message selectors retain
their distinct context requirements. -/
public def tell (targets : Players) (message : Message) :
    Prog (grade message targets.requirements) Int32 := do
  emit <| Command.Declarations.chatTell.call <| .cons (encode targets) <| .cons (encode message) .nil

/-- Message the executor's team, returning the selected player count. Requires an executor;
having a team is checked at runtime. A non-player teammate can send to online team members. -/
public def team (message : Message) : Prog (grade message Req.executor) Int32 := do
  emit <| Command.Declarations.chatTeam.call <| .cons (encode message) .nil

/-- Broadcast a native emote attributed to the source and return 1. A server source is valid.
Dynamic integers are serialized through the shared command macro protocol. -/
public def me (message : Message) : Prog (grade message) Int32 := do
  emit <| Command.Declarations.chatMe.call <| .cons (encode message) .nil

end Oria.Std.Chat
