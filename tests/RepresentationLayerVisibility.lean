module

import Oria.IR.Representation.Physical
import Oria.IR.Machine.Program
meta import Lean.Elab.GuardMsgs
meta import Lean.Elab.Command

namespace Oria.Tests.RepresentationLayerVisibility

open Oria Oria.Representation Lean Lean.Elab.Command

#check Table.build
#check Table.tag
#check IR.Machine.Signature
#check IR.Machine.Program

run_cmd
  for name in (← getEnv).header.moduleNames do
    if (`Oria.Compiler).isPrefixOf name then
      throwError "IR imports compiler implementation: {name}"

end Oria.Tests.RepresentationLayerVisibility
