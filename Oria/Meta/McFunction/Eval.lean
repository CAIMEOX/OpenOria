module

meta import all Oria.Language.Builder
import Lean.Meta.Eval

namespace Oria.McFunction.Eval

open Lean

/-- Audited adapter for evaluating one isolated inert compiler carrier. -/
private unsafe def recipeImpl
    (value : Expr) : MetaM (Except String McFunction.Internal.Recipe) := do
  try
    pure (.ok (← Lean.Meta.evalExpr McFunction.Internal.Recipe
      (mkConst ``McFunction.Internal.Recipe) value))
  catch error =>
    pure (.error (← error.toMessageData.toString))

@[implemented_by recipeImpl]
opaque recipe (value : Expr) : MetaM (Except String McFunction.Internal.Recipe)

end Oria.McFunction.Eval
