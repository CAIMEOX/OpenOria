module

public import Oria
public import Oria.Datapack
meta import Oria
meta import Oria.Datapack

namespace Oria.Proofs.Fixtures.Datapack

open Oria Oria.Datapack

@[mcfunction]
public def increment (x : Val Int32) : Prog .pure Int32 := Prog.pure (x + 1)

@[mcfunction]
public def run : Prog (Grade.handled .pure) Unit := (increment.call 7).ignore

@[datapack]
public def imported : Spec :=
  build { ns := "imported" } do
    entry "run" run.ref

end Oria.Proofs.Fixtures.Datapack
