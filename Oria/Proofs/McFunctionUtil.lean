module

public import Oria.Meta.McFunction
meta import Oria.Meta.McFunction

namespace Oria.Proofs.McFunctionUtil

open Lean Lean.Elab Command

public def elaborate (decl : Name) : CommandElabM ElaboratedDef := do
  match McFunctionRegistry.elaborate (← getEnv) decl with
  | .ok elaborated => pure elaborated
  | .error diagnostic =>
      throwError "failed to elaborate mcfunction `{decl}`: {repr diagnostic}"

end Oria.Proofs.McFunctionUtil
