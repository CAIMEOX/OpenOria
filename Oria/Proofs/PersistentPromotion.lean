module

import Oria.Compiler.Lower.DP121.Persistent.Promote
import Oria.IR.DP121.Pretty
import Lean.Elab.Command
public meta import Lean.Elab.Command
meta import Oria.Compiler.Lower.DP121.Persistent.Promote
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.PersistentPromotion

open Oria Oria.Target.DP121 Oria.Representation

private def config : Oria.Runtime.Config :=
  ⟨.ofString "memory", .ofString "memory:persistent", .ofString "memory:runtime", .ofString "memory.vm"⟩

run_cmd
  let .ok table := Table.build #[] | throwError "layout preparation failed"
  let plans ← match Persistent.build table #[.option (.option .i32)] with
    | .ok plans => pure plans
    | .error diagnostic => throwError "plans: {repr diagnostic}"
  let functions ← match Lower.DP121.Persistent.Promote.generate config plans with
    | .ok functions => pure functions
    | .error diagnostic => throwError "promotion: {repr diagnostic}"
  let bodies := functions.map fun ⟨_, definition⟩ => definition.body.pretty 160

end Oria.Proofs.PersistentPromotion
