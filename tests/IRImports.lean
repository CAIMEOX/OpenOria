module

import Oria.IR.Tree.Definition
import Oria.IR.Cont.Definition
import Oria.IR.Machine.Program
import Oria.IR.DP121.Program
meta import Lean.Elab.Command

open Lean Lean.Elab Command

run_cmd do
  let forbidden := [`Oria.Compiler, `Oria.Meta, `Oria.Language, `Oria.Std,
    `Oria.McFunction, `Oria.Builder, `Oria.Elab, `Oria.Collect, `Oria.Lower]
  for imported in (← getEnv).header.moduleNames do
    if forbidden.any (·.isPrefixOf imported) then
      throwError "IR imports a construction or compilation module: {imported}"
