module

import Oria
meta import Oria
meta import Lean.Elab.GuardMsgs

namespace Oria.Tests.StdVisibility

open Oria Oria.Std Oria.Std.Command.Arg

@[mcfunction]
private def move (x : Val Int32) : Prog ⟨11#8, 2115#16⟩ Int32 := do
  Teleport.to .self <| .world
    (.relative (.dynamic x)) (.absolute (.static 80)) (.relative (.static 0))

@[mcfunction]
private def setAndRead (x : Val Int32) :
    Prog ((Scoreboard.writeGrade .self).seq (Scoreboard.readGrade .self)) Int32 := do
  let objective := Command.Objective.ofString "oria.points"
  (Scoreboard.set .self objective (.dynamic x)).ignore
  Scoreboard.get .self objective

example : move.signature.grade = ⟨11#8, 2115#16⟩ := rfl
example : setAndRead.signature.grade =
    (Scoreboard.writeGrade .self).seq (Scoreboard.readGrade .self) := rfl

end Oria.Tests.StdVisibility
