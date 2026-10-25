module

import Oria.Language.Builder
import Oria.Meta.McFunction
import Oria.Proofs.BackendUtil
import Oria.Compiler.Lower.DP121.Program
import Oria.IR.DP121.Pretty
meta import Oria.Language.Builder
meta import Oria.Meta.McFunction
meta import Oria.Proofs.BackendUtil
meta import Oria.Compiler.Lower.DP121.Program
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.HeapLower

open Oria Lean Lean.Elab.Command

@[mcfunction]
private def wrap (x : Val Int32) : Prog .pure (Option Int32) := Oria.Option.some x

@[mcfunction]
private def unwrap (x : Val (Option Int32)) : Prog .pure Int32 :=
  Oria.Option.elim x (Prog.pure (-1)) Prog.pure

@[mcfunction]
private def acrossCall (x : Val Int32) : Prog .pure Int32 :=
  Prog.bind (wrap.call x) unwrap.call

@[mcfunction]
private def localCase (x : Val Int32) : Prog .pure Int32 :=
  Prog.bind (Oria.Option.some x) fun value =>
    Oria.Option.elim value (Prog.pure (-1)) Prog.pure

private def config : Lower.DP121.Config :=
  { resourceNamespace := .ofString "heap", objective := .ofString "heap.vm" }

run_cmd
  let commands ← match Std.Manifest.commandCatalog with
    | .ok commands => pure commands
    | .error error => throwError "command catalog: {repr error}"
  for (root, boxes) in [(⟨_, acrossCall.ref⟩, true), (⟨_, localCase.ref⟩, false)] do
    let ⟨_, machine⟩ ← BackendUtil.compile #[root]
    let target ← match Lower.DP121.lower config machine commands with
      | .ok target => pure target
      | .error error => throwError "heap lowering: {repr error}"
    unless target.checkCalls.isOk do throwError "heap helper calls did not close"
    let bodies := target.functions.toList.map fun ⟨_, definition⟩ => definition.body.pretty 120
    unless bodies.any (·.contains "append from storage") == boxes do
      throwError "allocation demand disagrees with object escape"
    unless bodies.any (·.contains "[$(p0)]") == boxes do
      throwError "projection demand disagrees with object escape"

end Oria.Proofs.HeapLower
