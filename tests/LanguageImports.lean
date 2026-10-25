module

import Oria
meta import Oria
meta import Lean.Elab.Command

open Lean Lean.Elab Command

run_cmd do
  let forbidden := [`Oria.Compiler, `Oria.IR.Machine, `Oria.IR.DP121,
    `Oria.NumberProvider, `Oria.Meta.Collect]
  for imported in (← getEnv).header.moduleNames do
    if forbidden.any (·.isPrefixOf imported) then
      throwError "The language entry imports an optional compiler or library module: {imported}"
