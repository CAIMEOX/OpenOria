module

public import Oria.Std.Command.Arg.Text
public import Oria.Nbt.Encode
import Oria.Std.Command.Declarations

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Text components and messages

`Tellraw.send` accepts complete host-side NBT text components, including styles, translations,
score, selector, and NBT references, and click/hover events. Helpers such as `text` and `number`
construct common components. The target Minecraft version interprets their fields.

All entry points return `Int32` with the recipient count on success. No matching players
causes failure. `text` and `number` require only the target's context. `send` and helpers
containing arbitrary components or native text retain `Req.all` as an extra requirement.
All functions retain a conservative effect bound. `send` accepts host values; `number`
accepts runtime integers. The game resolves score, selector, and NBT components.
-/

namespace Oria.Std.Tellraw

universe u

open Oria.Std.Command.Arg

/-- Combine target and message requirements, retaining the conservative chat, world,
scoreboard-reading, and random effect bound. Arbitrary NBT messages add Req.all. -/
@[expose] public def grade (targets : Players) (extraReq : ReqRow := Req.none) : Grade :=
  {
  req := Players.requirements targets ||| extraReq
  eff := Eff.chat ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure }

private def emit (targets : Players) (message : TextComponent) :
    Prog (grade targets message.requirements) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, Players.requirements, Oria.Command.Call.grade,
    Oria.Command.Call.requirements, Oria.Command.Ref.call,
    Command.Declarations.tellraw, Req.none] using
    (Oria.Command.emit <| Command.Declarations.tellraw.call <|
      .cons (Oria.Command.encode targets) <| .cons (Oria.Command.encode message) .nil)

/--
Send a host-side text component with an {name}`Oria.Nbt.ToNbt` instance to players.
Returns the recipient count on success and fails if no players match. Minecraft parses
static components when loading the function. Arbitrary components require the full context,
including an executor, even when their NBT representation is known at construction time.

```lean
open Oria Oria.Std
example := Tellraw.send .all (nbt% {text: "Ready", color: "gold", bold: true})
```
-/
public def send {a : Type u} [Nbt.ToNbt a] (targets : Players) (message : a) :
    Prog (grade targets Req.all) Int32 :=
  emit targets (.ofNbt message)

/-- Send literal text known at construction time. Returns the recipient count and fails
for an empty player selection. Context requirements come only from the targets;
broadcasting to all players can run in load or tick callbacks. Effects follow send. -/
public def text (targets : Players) (message : String) :
    Prog (grade targets) Int32 :=
  emit targets (.literal message)

/--
Send a static or dynamic I32 as a numeric text-component argument. Dynamic values use one
integer macro argument. Returns the recipient count on success; no matching players causes
failure. Context requirements come only from the targets. The computation producing a
dynamic value retains its own effects in the enclosing program.

```lean
open Oria Oria.Std
example (n : Val Int32) := Tellraw.number .self (.dynamic n)
```
-/
public def number (targets : Players) (value : Scalar) :
    Prog (grade targets) Int32 :=
  emit targets (.number value)

/-- Send a translation component. The key, interpolation arguments, and optional fallback
are supplied at construction time and resolved by the game's text-component rules.
The success payload and failure conditions follow send. -/
public def translate (targets : Players) (key : String) (args : List Nbt.Any := [])
    (fallback : Option String := none) : Prog (grade targets Req.all) Int32 :=
  let fields := Nbt.Fields.cons ⟨"translate"⟩ (.string key) <|
    .cons ⟨"with"⟩ (.list (.ofValues args.toArray)) <|
      match fallback with
      | none => .nil
      | some value => .cons ⟨"fallback"⟩ (.string value) .nil
  send targets (Nbt.Value.compound fields)

/-- Send a scoreboard text component, resolving the score during command execution.
The name is the component's score-holder text; objective identifies the score's objective.
The command payload is the recipient count. -/
public def score (targets : Players) (name : String) (objective : Oria.Command.Objective) :
    Prog (grade targets Req.all) Int32 :=
  send targets (nbt% {score: {name: $(name), objective: $(objective.token.text)}})

/-- Send an entity-selector text component. The game resolves the inner selector at execution
time; the outer targets determine the recipients. -/
public def selector (targets : Players) (selector : String) :
    Prog (grade targets Req.all) Int32 :=
  send targets (nbt% {selector: $(selector)})

/-- Send a text component referencing a storage path. When interpret is true, the selected
text is itself interpreted as a text component. NBT is read at execution time;
the command payload is the recipient count. -/
public def fromStorage (targets : Players) (storage : ResourceId) (path : Nbt.Path)
    (interpret : Bool := false) : Prog (grade targets Req.all) Int32 :=
  send targets (nbt% {nbt: $(path.format.pretty 120), storage: $(storage.text), interpret: $(interpret)})

/-- Send a text component referencing entity NBT. The entity argument is the inner selector
text; interpret controls whether the selected text is parsed as a component.
The command payload and outer player-selection failure conditions follow send. -/
public def fromEntity (targets : Players) (entity : String) (path : Nbt.Path)
    (interpret : Bool := false) : Prog (grade targets Req.all) Int32 :=
  send targets (nbt% {nbt: $(path.format.pretty 120), entity: $(entity), interpret: $(interpret)})

/-- Send a text component referencing block NBT. Position is native block-position text;
interpret controls whether the selected text is parsed as a component. The game resolves
the position and path during execution. -/
public def fromBlock (targets : Players) (position : String) (path : Nbt.Path)
    (interpret : Bool := false) : Prog (grade targets Req.all) Int32 :=
  send targets (nbt% {nbt: $(path.format.pretty 120), block: $(position), interpret: $(interpret)})

end Oria.Std.Tellraw
