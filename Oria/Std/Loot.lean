module

public import Oria.Std.Command.Arg.Loot
import Oria.Std.Command.Declarations.Content
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Loot

Loot evaluates a table, mining context, fishing context, or an entity death table and sends
the generated stacks to the chosen destination. Mining and kill sources do not remove the
block or kill the entity. Native results count successfully distributed stack entries,
not the total number of items. External tables may depend on the full execution context.
-/

namespace Oria.Std.Loot
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Source/destination requirements and native loot generation effects. -/
@[expose] public def grade (target : LootTarget) (source : LootSource) : Grade :=
  ⟨Req.dimension ||| (target.requirements ||| source.requirements), Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound ||| Eff.failure⟩

/-- Generate and distribute loot. Loaded-block, container, entity, and table requirements
are checked natively. Successful zero and distribution to a subset of targets retain native semantics. -/
public def run (target : LootTarget) (source : LootSource) :
    Prog (grade target source) Int32 := do
  emit <| Command.Declarations.lootItems.call <|
    .cons (encode target) <| .cons (encode source) <| .nil

end Oria.Std.Loot
