module

public import Oria.Proofs.Fixtures.McFunction
meta import Oria.Meta.McFunction
meta import Lean.Elab.GuardMsgs

open Oria.Proofs.Fixtures.McFunction

/--
error: `mcfunction` must be applied in the declaration's defining module
-/
#guard_msgs(error, substring := true) in
attribute [mcfunction] plain

/--
error: failed to evaluate mcfunction
-/
#guard_msgs(error, substring := true) in
@[mcfunction]
def importedInlineHelper (value : Oria.Val Int32) : Oria.Prog .pure Int32 :=
  plain value
