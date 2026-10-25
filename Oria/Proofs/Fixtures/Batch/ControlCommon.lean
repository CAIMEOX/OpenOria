module

public import Oria.Proofs.Fixtures.Batch.Common
public meta import Oria.Proofs.Fixtures.Batch.Common

namespace Oria.Proofs.Fixtures.Batch
open Oria.Std.Command.Arg

@[expose] public def rider : Target := .selector (.allEntities {tags := [.include "control.rider"], limit := some 1})
@[expose] public def vehicle : Target := .selector (.allEntities {tags := [.include "control.vehicle"], limit := some 1})
@[expose] public def column : ColumnPos := ⟨.absolute (.static 0), .absolute (.static 0)⟩
@[expose] public def blockOrigin : BlockPos :=
  .world (.relative (.static 0)) (.relative (.static 0)) (.relative (.static 0))

end Oria.Proofs.Fixtures.Batch
