module

import Oria.IR.Catalog.Function
import Oria.Proofs.McFunctionUtil
meta import Oria.IR.Catalog.Function
meta import Oria.Proofs.McFunctionUtil

namespace Oria.Proofs.TreeFunctionCatalog

open Oria Oria.IR
open Lean Lean.Elab Command
open Oria.Proofs.McFunctionUtil

@[mcfunction]
private def callee (value : Val Int32) : Prog .pure Int32 :=
  Prog.pure (I32.add value (I32.lit 1))

@[mcfunction]
private def caller (value : Val Int32) : Prog .pure Int32 :=
  callee.call value

@[mcfunction]
private def nestedCaller (condition : Val Bool) (value : Val Int32) : Prog .pure Int32 :=
  Prog.bind (Prog.pure value) fun bound =>
    Prog.branch condition
      (callee.call bound)
      (Prog.pure bound)

private def wrongSignature : Signature :=
  { args := [.bool], result := .i32, grade := .pure }

private def wrongRef : DeclRef wrongSignature :=
  .named ``callee

private def wrongClaim : IR.Tree.Def wrongSignature :=
  .build fun | .cons value .nil => pure (.perform (.call wrongRef (.cons value .nil)))

run_cmd
  let calleeDefinition ← elaborate ``callee
  let callerDefinition ← elaborate ``caller
  let .ok functions := Function.Catalog.build [calleeDefinition, callerDefinition]
    | throwError "failed to build the valid function catalog"
  let .ok objects := ObjectCatalog.build []
    | throwError "failed to build the primitive object catalog"
  let .ok objectLinked := objects.link callerDefinition.definition
    | throwError "caller failed object linking"
  let .ok commands := Oria.Command.Catalog.build []
    | throwError "failed to build the empty command catalog"
  let .ok commandLinked := commands.link objectLinked
    | throwError "caller failed command linking"
  unless (functions.link commandLinked).isOk do
    throwError "valid function reference failed linking"

run_cmd
  let callerDefinition ← elaborate ``caller
  let .ok functions := Function.Catalog.build []
    | throwError "failed to build the empty function catalog"
  let .ok objects := ObjectCatalog.build []
    | throwError "failed to build the primitive object catalog"
  let .ok objectLinked := objects.link callerDefinition.definition
    | throwError "caller failed object linking"
  let .ok commands := Oria.Command.Catalog.build []
    | throwError "failed to build the empty command catalog"
  let .ok commandLinked := commands.link objectLinked
    | throwError "caller failed command linking"
  match functions.link commandLinked with
  | .error (.unknownFunction name) =>
      unless name == ``callee do
        throwError "unknown-function diagnostic carried the wrong identity"
  | .error diagnostic =>
      throwError "expected unknown function, got {repr diagnostic}"
  | .ok _ => throwError "missing callee unexpectedly linked"

run_cmd
  let calleeDefinition ← elaborate ``callee
  let wrongDefinition := wrongClaim
  let .ok functions := Function.Catalog.build [calleeDefinition]
    | throwError "failed to build the function catalog"
  let .ok objects := ObjectCatalog.build []
    | throwError "failed to build the primitive object catalog"
  let .ok objectLinked := objects.link wrongDefinition
    | throwError "wrong-signature caller failed object linking"
  let .ok commands := Oria.Command.Catalog.build []
    | throwError "failed to build the empty command catalog"
  let .ok commandLinked := commands.link objectLinked
    | throwError "wrong-signature caller failed command linking"
  match functions.link commandLinked with
  | .error (.functionSignatureMismatch name expected actual) =>
      unless name == ``callee && expected == calleeDefinition.signature &&
          actual == wrongSignature do
        throwError "signature-mismatch diagnostic carried the wrong evidence"
  | .error diagnostic =>
      throwError "expected function signature mismatch, got {repr diagnostic}"
  | .ok _ => throwError "wrong function signature unexpectedly linked"

run_cmd
  let calleeDefinition ← elaborate ``callee
  match Function.Catalog.build [calleeDefinition, calleeDefinition] with
  | .error (.duplicateFunction name) =>
      unless name == ``callee do
        throwError "duplicate-function diagnostic carried the wrong identity"
  | .error diagnostic =>
      throwError "expected duplicate function, got {repr diagnostic}"
  | .ok _ => throwError "duplicate function catalog unexpectedly built"

run_cmd
  let nestedDefinition ← elaborate ``nestedCaller
  let .ok functions := Function.Catalog.build []
    | throwError "failed to build the empty function catalog"
  let .ok objects := ObjectCatalog.build []
    | throwError "failed to build the primitive object catalog"
  let .ok objectLinked := objects.link nestedDefinition.definition
    | throwError "nested caller failed object linking"
  let .ok commands := Oria.Command.Catalog.build []
    | throwError "failed to build the empty command catalog"
  let .ok commandLinked := commands.link objectLinked
    | throwError "nested caller failed command linking"
  match functions.link commandLinked with
  | .error (.unknownFunction name) =>
      unless name == ``callee do
        throwError "nested unknown-function diagnostic carried the wrong identity"
  | .error diagnostic =>
      throwError "expected nested unknown function, got {repr diagnostic}"
  | .ok _ => throwError "nested missing callee unexpectedly linked"

end Oria.Proofs.TreeFunctionCatalog
