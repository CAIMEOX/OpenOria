module

public import Oria.Std.Command.Arg.Item
import Oria.Std.Command.Declarations.Content
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Give

Give constructs stacks from an item ID and a component patch. Counts may be dynamic.
Minecraft enforces positive counts, its stack-batch limit, component schemas, and player
selection. Full inventories can produce dropped items. Successful results count players.
-/

namespace Oria.Std.Give
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Player selection and component dependencies, including native inventory and pickup effects. -/
@[expose] public def grade (players : Players) (item : ItemSpec) : Grade :=
  ⟨players.requirements ||| item.requirements, Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound ||| Eff.failure⟩

/-- Give the requested count to every selected player. Static invalid syntax can prevent
function loading; dynamic invalid counts or components fail when the macro is invoked. -/
public def to (players : Players) (item : ItemSpec) (count : Scalar := .static 1) :
    Prog (grade players item) Int32 := do
  emit <| Command.Declarations.giveItems.call <|
    .cons (encode players) <| .cons (encode item) <| .cons (encode count) <| .nil

end Oria.Std.Give
