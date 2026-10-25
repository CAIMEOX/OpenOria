module

public import Oria.Std.Command.Arg.Block
import Oria.Std.Command.Declarations.Content
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Setblock

Setblock accepts a concrete state with optional block-entity NBT. Omitting NBT preserves
existing data when the native operation retains that block entity; an explicit empty
compound supplies empty data. Strict placement suppresses neighbor and shape updates.
-/

namespace Oria.Std.Setblock
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Dimension, coordinate, property, and NBT-fragment requirements. -/
@[expose] public def grade (position : BlockPos) (block : BlockState) : Grade :=
  ⟨Req.dimension ||| ((encode position).requirements ||| block.requirements), Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound ||| Eff.failure⟩

/-- Place one block, returning 1 when the native state or data operation succeeds.
Keep only places in air; unchanged-state, bounds, and unloaded-chunk failures remain native. -/
public def set (position : BlockPos) (block : BlockState) (mode : SetBlockMode := .replace) :
    Prog (grade position block) Int32 := do
  emit <| Command.Declarations.setBlock.call <|
    .cons (encode position) <| .cons (encode block) <| .cons (encode mode) <| .nil

end Oria.Std.Setblock
