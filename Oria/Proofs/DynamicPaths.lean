module

import Oria.Proofs.Fixtures.DynamicPaths
import Oria.Std.Command.Declarations
import Oria.Std.DP121
import Oria.IR.DP121.Pretty
import Oria.Proofs.BackendUtil
import Oria.Compiler.Lower.DP121.Program
meta import Oria.Std.DP121
meta import Oria.IR.DP121.Pretty
meta import Oria.Proofs.BackendUtil
meta import Oria.Compiler.Lower.DP121.Program
meta import Oria.Proofs.Fixtures.DynamicPaths

namespace Oria.Proofs.DynamicPaths

open Oria Oria.Std.Command.Arg

private def rendered (path : Nbt.Path Scalar (Nbt.Value .compound)) : Except Diagnostic (String × Nat) := do
  let request := Std.Command.Declarations.dataGetPath.call <|
    .cons (Command.encode (DataTarget.storage "demo:data")) <| .cons (Command.encode path) .nil
  let plan ← Std.DP121.plan request
  plan.withInvocation
    (fun invocation => pure ((Target.DP121.Command.invoke invocation).pretty 160, 0))
    (fun schema _ _ invocation _ =>
      pure ((Target.DP121.Command.invoke invocation).pretty 160, schema.fields.length))

#guard (rendered (((Nbt.Path.key "slots").at (.static 3)).field "two words")).toOption ==
  some ("data get storage demo:data \"slots\"[3].\"two words\"", 0)

#guard (rendered ((((Nbt.Path.key "slots").at (.dynamic (0 : Val Int32))).field "payload").at (.static 1))).toOption ==
  some ("data get storage demo:data \"slots\"[$(p0)].\"payload\"[1]", 1)

#guard (rendered (((Nbt.Path.key "matrix").at (.dynamic (0 : Val Int32))).at (.dynamic (1 : Val Int32)))).toOption ==
  some ("data get storage demo:data \"matrix\"[$(p0)][$(p1)]", 2)

#guard (rendered ((Nbt.Path.key "$(injected)").at (.dynamic (0 : Val Int32)))) matches .error _

open Lean Lean.Elab.Command in
run_cmd do
  let ⟨_, machine⟩ ← BackendUtil.compile #[⟨_, Fixtures.DynamicPaths.constant.ref⟩]
  let .ok commands := Std.Manifest.commandCatalog | throwError "missing command catalogue"
  let config : Lower.DP121.Config := { resourceNamespace := "constant", objective := "constant.vm" }
  let .ok target := Lower.DP121.lower config machine commands | throwError "constant path lowering failed"
  unless target.functions.all (fun ⟨kind, _⟩ => match kind with | .plain => true | .macro _ => false) do
    throwError "a constant index produced a function macro"

end Oria.Proofs.DynamicPaths
