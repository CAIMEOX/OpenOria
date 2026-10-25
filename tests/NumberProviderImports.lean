module

import Oria.NumberProvider
meta import Lean.Elab.Command
meta import Lean.Elab.GuardMsgs

open Lean Lean.Elab Command

run_cmd do
  let forbidden := [`Oria.IR, `Oria.Language, `Oria.Meta, `Oria.Compiler,
    `Oria.Diagnostic, `Oria.Std]
  for imported in (← getEnv).header.moduleNames do
    if forbidden.any (·.isPrefixOf imported) then
      throwError "NumberProvider imports the object-program stack through {imported}"
