module

public import Oria.Meta.Collect
public import Oria.Compiler.Program
public import Oria.Compiler.Lower.Machine
public import Oria.Std.Manifest
meta import Oria.Meta.Collect
meta import Oria.Compiler.Program
meta import Oria.Compiler.Lower.Machine
meta import Oria.Std.Manifest

namespace Oria.Proofs.BackendUtil

open Lean Lean.Elab.Command

private meta def require {a : Type} (value : Except Diagnostic a) : CommandElabM a :=
  match value with
  | .ok value => pure value
  | .error diagnostic => throwError "backend fixture failed: {repr diagnostic}"

public meta def compile (entries : Array IR.DeclRef.Some) :
    CommandElabM ((source : Oria.Program.ClosedProgram) × IR.Machine.Program source) := do
  let commands ← require Std.Manifest.commandCatalog
  let candidate ← require (Oria.collect (← getEnv) entries commands)
  let collected ← require candidate.checkClosure
  let program ← require (Oria.Program.compile collected)
  let source := program.closed
  let prepared ← require (Lower.Machine.prepare candidate)
  let machine ← require (Lower.Machine.lowerProgram source prepared)
  pure ⟨source, machine⟩

end Oria.Proofs.BackendUtil
