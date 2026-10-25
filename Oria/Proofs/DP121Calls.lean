module

import Oria.IR.DP121.Program
meta import Oria.IR.DP121.Program

namespace Oria.Proofs.DP121Calls

open Oria Oria.Target.DP121

private def caller : FunctionRef .plain :=
  .ofId (.ofParts (.ofString "test") (.ofString "caller"))

private def target : FunctionRef .plain :=
  .ofId (.ofParts (.ofString "test") (.ofString "target"))

private def closed : Target.DP121.Program := .of #[
  ⟨.plain, ⟨caller, .plain #[.returnRun (.function target)]⟩⟩,
  ⟨.plain, ⟨target, .plain #[.returnValue 0]⟩⟩
] (by native_decide)

private def missing : Target.DP121.Program := .of #[
  ⟨.plain, ⟨caller, .plain #[.returnRun (.function target)]⟩⟩
] (by native_decide)

private def schema : MacroSchema := .ofFields [⟨.i32, .i32⟩]
private def otherSchema : MacroSchema := .ofFields []

private def macroRef : FunctionRef (.macro schema) := .ofId target.id
private def otherRef : FunctionRef (.macro otherSchema) := .ofId target.id
private def arguments : MacroSource schema := ⟨.ofString "test:runtime", none⟩

private def macroClosed : Target.DP121.Program := .of #[
  ⟨.plain, ⟨caller, .plain #[.returnRun (.functionWithStorage macroRef arguments)]⟩⟩,
  ⟨.macro schema, ⟨macroRef, .macro #[]⟩⟩
] (by native_decide)

private def macroMismatch : Target.DP121.Program := .of #[
  ⟨.plain, ⟨caller, .plain #[.returnRun (.functionWithStorage macroRef arguments)]⟩⟩,
  ⟨.macro otherSchema, ⟨otherRef, .macro #[]⟩⟩
] (by native_decide)

#guard closed.checkCalls.isOk
#guard macroClosed.checkCalls.isOk
#guard match missing.checkCalls with
  | .error (.unresolvedTargetFunction "test:target") => true
  | _ => false
#guard match macroMismatch.checkCalls with
  | .error (.unresolvedTargetFunction "test:target") => true
  | _ => false

end Oria.Proofs.DP121Calls
