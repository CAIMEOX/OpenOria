module

public import Oria.Std.Command.Arg.Block
import Oria.Std.Command.Declarations.Content
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Fill

Fill uses an inclusive region and concrete block state. Keep is a separate mode; replacement
may combine a block predicate with normal, destroy, hollow, outline, or strict placement.
Minecraft enforces loaded chunks, build bounds, and its block-modification limit.
-/

namespace Oria.Std.Fill
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Dimension, corners, block description, and optional filter requirements. -/
@[expose] public def grade (box : BlockBox) (block : BlockState) (mode : FillMode := .replace) : Grade :=
  ⟨Req.dimension ||| (box.requirements ||| (block.requirements ||| mode.requirements)), Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound ||| Eff.failure⟩

/-- Fill a region and return the native changed-block count. No changes fail.
Native filtering, NBT matching, and updates to individual blocks determine the result. -/
public def run (box : BlockBox) (block : BlockState) (mode : FillMode := .replace) :
    Prog (grade box block mode) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, BlockBox.requirements, BlockDesc.requirements, FillMode.requirements,
    Oria.Command.Call.grade, Oria.Command.Call.requirements, Oria.Command.Ref.call,
    Command.Declarations.fillBlocks, Req.none, BitVec.or_assoc] using
    (emit <| Command.Declarations.fillBlocks.call <|
      .cons (encode box) <| .cons (encode block) <| .cons (encode mode) <| .nil)

end Oria.Std.Fill
