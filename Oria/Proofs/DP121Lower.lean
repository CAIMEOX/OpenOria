module

import Oria.IR.DP121.Program
meta import Oria.IR.DP121.Program

namespace Oria.Proofs.DP121Lower

open Oria Oria.Target.DP121

private def plainRef : FunctionRef .plain :=
  .ofId (.ofParts (.ofString "oria") (.ofString "plain"))

private def plainDef : FunctionDef .plain :=
  { ref := plainRef, body := .plain #[.returnValue 1] }

private def schema : MacroSchema :=
  .ofFields [{ ty := .i32, codec := .i32 }]

private def macroRef : FunctionRef (.macro schema) :=
  .ofId (.ofParts (.ofString "oria") (.ofString "macro"))

private def macroDef : FunctionDef (.macro schema) :=
  { ref := macroRef, body := .macro #[] }

private def functions : Array ((kind : FunctionKind) × FunctionDef kind) :=
  #[⟨.plain, plainDef⟩, ⟨.macro schema, macroDef⟩]

private def program : Target.DP121.Program :=
  .of functions (by native_decide)

example :
    (program.functions.toList.map fun ⟨_, d⟩ => d.ref.id.render).Nodup :=
  program.unique

end Oria.Proofs.DP121Lower
