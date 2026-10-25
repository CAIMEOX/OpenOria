module

public import Oria.Proofs.Fixtures.McFunctionCaller
import Oria.IR.Tree.Pretty
meta import Oria.Meta.McFunction
meta import Oria.IR.Tree.Pretty

namespace Oria.Proofs.McFunctionImport

open Oria Oria.IR
open Oria.Proofs.Fixtures.McFunction
open Oria.Proofs.Fixtures.McFunctionCaller
open Lean Lean.Elab

example : DeclRef increment.signature := increment.ref

example : Val Int32 → Prog .pure Int32 := increment.call

example : Val Int32 → Prog .pure Int32 := caller.call

run_cmd
  let env ← getEnv
  let expected : Signature :=
    { args := [.i32], result := .i32, grade := .pure }
  let some entry := McFunctionRegistry.find? env ``increment
    | throwError "imported mcfunction is absent from the registry"
  unless entry.signature == expected do
    throwError "imported mcfunction has the wrong signature"
  match McFunctionRegistry.elaborate env ``increment with
  | .ok elaborated =>
      unless elaborated.signature == expected do
        throwError "imported recipe has the wrong signature"
  | .error diagnostic =>
      throwError "imported mcfunction failed to elaborate: {repr diagnostic}"
  match McFunctionRegistry.elaborate env ``caller with
  | .ok elaborated =>
      unless elaborated.definition.pretty 120 |>.contains "call Oria.Proofs.Fixtures.McFunction.increment" do
        throwError "cross-module caller did not retain the named call"
  | .error diagnostic =>
      throwError "cross-module caller failed to elaborate: {repr diagnostic}"

end Oria.Proofs.McFunctionImport
