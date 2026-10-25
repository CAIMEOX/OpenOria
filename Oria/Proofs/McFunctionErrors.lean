module

import Oria.Meta.McFunction
meta import Oria.Meta.McFunction
meta import Lean.Elab.GuardMsgs

namespace Oria.Proofs.McFunctionErrors

open Oria

/--
error: mcfunction parameters must have type `Val A`
-/
#guard_msgs(error, substring := true) in
@[mcfunction]
def invalidParameter (_value : Int32) : Prog .pure Int32 :=
  Prog.pure (I32.lit 0)

/--
error: mcfunction result must have type `Prog grade A`
-/
#guard_msgs(error, substring := true) in
@[mcfunction]
def invalidResult (_value : Val Int32) : Int32 :=
  0

def collision.signature : Nat := 0

/--
error: generated mcfunction declaration
-/
#guard_msgs(error, substring := true) in
@[mcfunction]
def collision (value : Val Int32) : Prog .pure Int32 :=
  Prog.pure value

end Oria.Proofs.McFunctionErrors
