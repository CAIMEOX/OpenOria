module

import Oria.IR.Machine.Program

namespace Oria.Proofs.Components

open Oria.Representation

example (table : Table) : table.width (.option .i32) = 1 := rfl
example (table : Table) : table.width (.option (.option .i32)) = 1 := rfl
example (table : Table) : table.width (.option .unit) = 1 := rfl
example (table : Table) : table.arity [.unit, .option .i32, .bool] = 2 := rfl

example (table : Table) : table.width .i32 = 1 := rfl
example (table : Table) :
    (IR.Machine.signature table ⟨[], .i32, .failure⟩).result = 2 := rfl

end Oria.Proofs.Components
