module

public import Oria.Meta.McFunction
public meta import Oria.Meta.McFunction

namespace Oria.Proofs.Fixtures.McFunction

open Oria

@[mcfunction]
public def increment (value : Val Int32) : Prog .pure Int32 :=
  Prog.pure (I32.add value (I32.lit 1))

public def plain (value : Val Int32) : Prog .pure Int32 :=
  Prog.pure value

end Oria.Proofs.Fixtures.McFunction
