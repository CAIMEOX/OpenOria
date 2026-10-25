module

public import Oria.Std.Command.Arg.Block
import Oria.Std.Command.Declarations.Generation
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# FillBiome

Biome storage has one sample per 4 by 4 by 4 block cell. Minecraft quantizes both corners
down to this grid and includes both endpoints. The result counts cells whose stored biome
changed, rather than blocks in the requested region. Block-level biome queries also apply
Minecraft's neighboring-sample selection.
-/

namespace Oria.Std.FillBiome
open Oria.Std.Command.Arg
open Oria.Command (encode emit ResourceOrTag)

/-- Region coordinates and the current dimension; mutation carries the world effect. -/
@[expose] public def grade (box : BlockBox) : Grade :=
  ⟨Req.dimension ||| box.requirements, Eff.world ||| Eff.failure⟩

/-- Replace stored biome samples, optionally filtering their current biome by ID or tag.
Returns the changed-cell count. An unchanged selection, an unavailable chunk, or a region
exceeding the native modification limit fails. Corners may include runtime I32 coordinates. -/
public def run (box : BlockBox) (biome : ResourceId) (filter : Option ResourceOrTag := none) :
    Prog (grade box) Int32 := by
  cases filter with
  | none =>
    simpa [Eff.failure, Grade.seq, Grade.failure, grade, BlockBox.requirements, Oria.Command.Call.grade,
      Oria.Command.Call.requirements, Oria.Command.Ref.call,
      Command.Declarations.fillBiome, Req.none] using
      (emit <| Command.Declarations.fillBiome.call <|
        .cons (encode box) <| .cons (encode biome) .nil)
  | some filter =>
    simpa [Eff.failure, Grade.seq, Grade.failure, grade, BlockBox.requirements, Oria.Command.Call.grade,
      Oria.Command.Call.requirements, Oria.Command.Ref.call,
      Command.Declarations.fillBiomeFiltered, Req.none] using
      (emit <| Command.Declarations.fillBiomeFiltered.call <|
        .cons (encode box) <| .cons (encode biome) <| .cons (encode filter) .nil)

end Oria.Std.FillBiome
