module

import Oria.IR.Representation.Physical
import Oria.IR.Catalog.Object
meta import Oria.IR.Representation.Physical
meta import Oria.IR.Catalog.Object

namespace Oria.Proofs.ObjectLayout

open Oria Oria.IR Oria.Representation

private def record : TypeId := ⟨`Example.Record, []⟩
private def schema : ObjectSchema :=
  ⟨record, [⟨`Example.Record.mk, [.i32, .unit, .option .i32]⟩], .ordinary⟩
private def table := (Table.build #[schema]).toOption.get (by native_decide)
private def constructor : Constructor (.data record) [.i32, .unit, .option .i32] :=
  .data ⟨`Example.Record.mk⟩

example : table.width (.data record) = 1 := by native_decide
example : table.arity [.i32, .unit, .option .i32] = 2 := rfl

example : ((table.layout constructor).toOption.map HeapLayout.scanCode) = some 6 := by native_decide
example : ((table.layout constructor).toOption.map (·.payload.toList)) =
    some [.scalar, .pointer (.option .i32)] := by native_decide



end Oria.Proofs.ObjectLayout
