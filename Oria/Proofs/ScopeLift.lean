module

import Oria.Compiler.Lower.Scope
import Oria.IR.Tree.Dependencies
meta import Oria.Compiler.Lower.Scope
meta import Oria.IR.Tree.Dependencies

namespace Oria.Proofs.ScopeLift

open Oria.IR

private def scope : Execute.Scope Tree.Expr := Execute.Scope.ofSteps [.as .allPlayers]
private def signature : Signature := ⟨[.i32], .unit, scope.grade .pure⟩
private def source : Tree.Def signature := Tree.Def.build fun
  | .cons value .nil => pure (Tree.Tree.scoped scope
      (Tree.Tree.ret value))
private def lifted := Lower.Scope.lower `example source

#guard lifted.helpers.size == 1
#guard lifted.helpers[0]?.any (·.signature.args == [.i32])
#guard lifted.helpers[0]?.any (·.signature.result == .i32)
#guard lifted.helpers[0]?.any (·.source == Lean.Name.num `example 0)
#guard lifted.main.dependencies.functions.size == 1

end Oria.Proofs.ScopeLift
