module

public import Oria.Std.Command.Arg.Item
import Oria.Std.Command.Declarations.Content
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Clear

Clear matches items using IDs, tags, and component conditions. An omitted maximum removes
all matches; zero counts them without removal. A positive maximum applies per player.
No matching items produces native failure, including in count-only mode.
-/

namespace Oria.Std.Clear
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Player and predicate requirements. -/
@[expose] public def grade (players : Players) (predicate : ItemPredicate := {}) : Grade :=
  ⟨players.requirements ||| predicate.requirements, Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound ||| Eff.failure⟩

/-- Remove or count matching items and return the native aggregate item count. All item
types are selected by the default predicate. Native player inventory rules determine the slots. -/
public def run (players : Players := .self) (predicate : ItemPredicate := {})
    (limit : Option Scalar := none) : Prog (grade players predicate) Int32 :=
  match limit with
  | none => do
      emit <| Command.Declarations.clearItems.call <|
        .cons (encode players) <| .cons (encode predicate) <| .nil
  | some limit => do
      emit <| Command.Declarations.clearItemsLimit.call <|
        .cons (encode players) <| .cons (encode predicate) <| .cons (encode limit) <| .nil

end Oria.Std.Clear
