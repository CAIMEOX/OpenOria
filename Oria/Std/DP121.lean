module

public import Oria.IR.DP121.CommandPlan
public import Oria.Std.Manifest

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# DP121 standard command planning

Target compilation and command-expansion tools use this module to pass a command call and
the [standard catalog](##Oria.Std.Manifest) to the DP121 command planner.
-/

namespace Oria.Std.DP121

open Oria.Target.DP121

/-- Plan a command call using the standard catalog, retaining its value parameters.
Declaration and template errors are returned as diagnostics. -/
public def plan {v : ObjTy → Type} {sig : Command.Signature} (request : Command.Call v sig) :
    Except Diagnostic (CommandPlan v sig) := do
  let catalog ← Oria.Std.Manifest.commandCatalog
  planWithCatalog catalog request

end Oria.Std.DP121
