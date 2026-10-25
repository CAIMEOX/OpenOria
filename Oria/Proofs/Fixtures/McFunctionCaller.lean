module

public import Oria.Proofs.Fixtures.McFunction
public meta import Oria.Meta.McFunction

namespace Oria.Proofs.Fixtures.McFunctionCaller

open Oria
open Oria.Proofs.Fixtures.McFunction

@[mcfunction]
public def caller (value : Val Int32) : Prog .pure Int32 :=
  increment.call value

end Oria.Proofs.Fixtures.McFunctionCaller
