module

import Oria.IR.Cont.Definition
meta import Lean.Elab.GuardMsgs

namespace Oria.Tests.ContVisibility

open Oria Oria.IR Oria.IR.Cont

private def signature : Signature := ⟨[], .i32, .pure⟩
private def definition : Def signature := .build fun .nil => .ret (.i32 0)

#check definition
#check Comp.switch
#check Arms.cons

private def linked : Comp [] .i32 [] :=
  .letJoin (.ret (.local Scope.Var.head))
    (.jump Scope.Var.head (.cons (.i32 1) .nil))

#check linked

end Oria.Tests.ContVisibility
