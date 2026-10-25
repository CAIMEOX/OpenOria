module

public import Oria.Std.Command.Arg.Gameplay
import Oria.Std.Command.Declarations.Player
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Enchant

Enchant applies a registered enchantment to selected living entities' held items. Native item
compatibility, enchantment compatibility, and maximum-level checks are preserved; successful results
count changed entities.
-/

namespace Oria.Std.Enchant

open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Target-selection requirements and gameplay effects. -/
@[expose] public def grade (targets : Target) : Grade :=
  ⟨targets.requirements,
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.chat ||| Eff.failure⟩

/-- Enchant eligible main-hand items. Level defaults to one and can be dynamic.
An empty or wholly ineligible selection fails. -/
public def apply (targets : Target) (enchantment : ResourceId) (level : Scalar := .static 1) :
    Prog (grade targets) Int32 := do
  emit <| Command.Declarations.enchant.call <|
    .cons (encode targets) <| .cons (encode enchantment) <| .cons (encode level) <| .nil

end Oria.Std.Enchant
