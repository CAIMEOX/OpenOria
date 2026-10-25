module

public import Oria.Meta.Elab.ProgDo
public import Oria.Meta.McFunction
public import Oria.Std
meta import Oria.Meta.McFunction
meta import Oria.Std

namespace Oria.Proofs.Fixtures.CommandClosure

open Oria

/-- A function with two command dependencies for collection and closure checks. -/
@[mcfunction]
public def moveAndRead (x : Val Int32) := show Prog _ Int32 from do
  Std.Teleport.to .self (.world
    (.relative (.dynamic x)) (.absolute (.static 80)) (.relative (.static 0)))
  let n ← Std.Scoreboard.get .self "collect.points"
  return n + 1

end Oria.Proofs.Fixtures.CommandClosure
