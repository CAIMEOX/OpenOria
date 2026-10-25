module

public import Oria.IR.DP121.Syntax

namespace Oria.Target.DP121

/-- One target function whose identity and body share the same call kind. -/
public structure FunctionDef (kind : FunctionKind) where
  ref : FunctionRef kind
  body : FunctionBody kind

/-- A heterogeneous target program with unique rendered function identities. -/
public structure Program where
  private mk ::
  functions : Array ((kind : FunctionKind) × FunctionDef kind)
  unique : (functions.toList.map fun ⟨_, d⟩ => d.ref.id.render).Nodup

/-- Structured outgoing references, retaining their exact call kinds. -/
public def Command.calls {mode : Mode} : Command mode → List (FunctionKind × String)
  | .function ref | .schedule ref | .execute _ ref => [(.plain, ref.id.render)]
  | .functionWithStorage (schema := schema) ref _ => [(.macro schema, ref.id.render)]
  | .when _ _ command | .store _ _ command | .returnRun command => command.calls
  | .scoreboard _ | .data _ | .invoke _ | .native _ | .commandLimit | .returnValue _ | .returnFail => []

/-- References from both static lines and macro-scoped lines. -/
public def FunctionBody.calls {kind : FunctionKind} : FunctionBody kind → List (FunctionKind × String)
  | .plain commands => commands.toList.flatMap Command.calls
  | .macro lines => lines.toList.flatMap fun
      | .static command => command.calls
      | .macro line => line.command.calls

namespace Program

private def declarations (program : Program) : List (FunctionKind × String) :=
  program.functions.toList.map fun ⟨kind, definition⟩ => (kind, definition.ref.id.render)

/-- Every structured call resolves with its exact plain or macro signature. -/
public def Closed (program : Program) : Prop :=
  ∀ ref ∈ program.functions.toList.flatMap (fun ⟨_, d⟩ => d.body.calls),
    ref ∈ declarations program

public def checkCalls (program : Program) : Except Diagnostic (PLift program.Closed) := do
  let names := declarations program
  let calls := program.functions.toList.flatMap fun ⟨_, d⟩ => d.body.calls
  if closed : ∀ ref ∈ calls, ref ∈ names then
    pure ⟨by simpa [Closed, calls, names] using closed⟩
  else
    let missing := calls.find? fun ref => decide (ref ∉ names)
    throw (.unresolvedTargetFunction (missing.map Prod.snd |>.getD ""))

@[expose] public def of
    (functions : Array ((kind : FunctionKind) × FunctionDef kind))
    (unique : (functions.toList.map fun ⟨_, d⟩ => d.ref.id.render).Nodup) :
    Program :=
  private_decl% ⟨functions, unique⟩

end Program

end Oria.Target.DP121
