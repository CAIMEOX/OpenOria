module

import Oria.Compiler.Definition
import Oria.IR.Cont.Pretty
import Oria.Proofs.McFunctionUtil
meta import Oria.Compiler.Definition
meta import Oria.IR.Cont.Pretty
meta import Oria.Proofs.McFunctionUtil
import Lean.Elab.Command

namespace Oria.Proofs.Compiler

open Oria
open Lean Lean.Elab Command
open Oria.Proofs.McFunctionUtil

@[mcfunction]
private def callee (value : Val Int32) : Prog .pure Int32 :=
  Prog.pure (I32.add value (I32.lit 1))

@[mcfunction]
private def caller (value : Val Int32) : Prog .pure Int32 :=
  callee.call value

run_cmd
  let callerDefinition ← elaborate ``caller
  let .ok functions := Function.Catalog.build []
    | throwError "failed to build the empty function catalog"
  let .ok objects := ObjectCatalog.build []
    | throwError "failed to build the primitive object catalog"
  let .ok commands := Oria.Command.Catalog.build []
    | throwError "failed to build the empty command catalog"
  match Oria.Compiler.compile functions objects commands callerDefinition with
  | .error (.unknownFunction name) =>
      unless name == ``callee do
        throwError "unknown-function diagnostic carried the wrong identity"
  | .error diagnostic =>
      throwError "expected unknown function, got {repr diagnostic}"
  | .ok _ => throwError "caller compiled without its callee"

end Oria.Proofs.Compiler
