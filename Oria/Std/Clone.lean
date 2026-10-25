module

public import Oria.Std.Command.Arg.Block
import Oria.Std.Command.Declarations.Content
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Clone

Clone copies a region to another position, optionally across dimensions. Omitted source and
destination dimensions each use the command dimension. Relative positions resolve against
the command context. Normal rejects overlap, force permits it, and move removes selected
source blocks. Strict suppresses neighbor and shape updates.
-/

namespace Oria.Std.Clone
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Request dependencies and the command dimension's block-modification rules. -/
@[expose] public def grade (request : CloneSpec) : Grade :=
  ⟨Req.dimension ||| request.requirements, Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound ||| Eff.failure⟩

/-- Clone selected blocks, retaining native block-entity copying and tick handling.
Return the native copied-block count; invalid bounds, overlap, limits, and no-copy cases fail. -/
public def run (request : CloneSpec) : Prog (grade request) Int32 := do
  emit <| Command.Declarations.cloneBlocks.call <|
    .cons (encode request) <| .nil

end Oria.Std.Clone
