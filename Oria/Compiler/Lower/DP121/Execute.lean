module

public import Oria.Compiler.Lower.DP121.Calling
public import Oria.Compiler.Lower.DP121.Command

namespace Oria.Lower.DP121.Execute

open Oria.IR Oria.Target.DP121

variable {source : Oria.Program.ClosedProgram} {program : Machine.Program source} {k : Nat}

/-- Freeze captures outside the fork, then prepare a fresh call at every selected context. -/
public def emit {params : Nat} (ctx : Calling.Context program k) (path : String)
    (scope : Oria.Execute.Scope (fun _ => Transfer.Source Place))
    (canFail : Bool)
    (callee : IR.Scope.Var Unit (Machine.signatures program.table source) ⟨params, canFail.toNat + 1⟩)
    (saved : Array (Fin k)) (captures : List (Transfer.Move Place)) :
    Except Diagnostic Emitted := do
  let frozen (frame : Stack.Frame) (index : Nat) : Place :=
    .storage (Stack.slot ctx.storage frame .locals index)
  let inputs := captures.zipIdx.map fun (move, index) =>
    Stack.move ⟨frozen .current index, move.source⟩
  let save := saved.toList.zipIdx.map fun (r, index) =>
    Stack.move ⟨.storage (Stack.slot ctx.storage .current .saved index),
      .loc (.score ctx.bank.registers[r])⟩
  let restore := saved.toList.zipIdx.map fun (r, index) =>
    Stack.move ⟨.score ctx.bank.registers[r],
      .loc (.storage (Stack.slot ctx.storage .current .saved index))⟩
  let returns := callee.typeCorrect ▸
    ((ctx.plan.functions.get callee.index).returns.map (Option.map (Calling.resultPlace ctx)))
  let outputs ← (List.finRange (canFail.toNat + 1)).filterMapM fun channel => do
    let flag := canFail && channel.val == 0
    if (if flag then scope.captureSuccess else scope.captureResult) then
      let some location := returns[channel] | throw (.unsupportedMachineLowering .anonymous)
      pure (some (⟨.score (if flag then ctx.bank.scratch[2] else ctx.bank.scratch[3]), .loc location⟩ : Transfer.Move Place))
    else pure none
  let call ← Calling.invoke ctx callee.index #[]
    (fun frame => pure (captures.zipIdx.map fun (move, index) =>
      ⟨move.target, .loc (frozen frame index)⟩))
    (fun _ => pure outputs)
  let finish : List (Command .plain) :=
    (if canFail && scope.captureSuccess then
      [.when .negative (.matches ctx.bank.scratch[2] (.exact 1)) .returnFail] else []) ++
    [if scope.captureResult then .returnRun (.scoreboard (.get ctx.bank.scratch[3])) else .returnValue 0]
  let (target, helpers) ← match call with
    | [.function target] =>
        if !scope.captureSuccess && !scope.captureResult then pure (target, []) else wrap call finish
    | _ => wrap call finish
  let chain ← Command.execute ctx.config ctx.bank (path ++ "/macro") scope.fragment target
  let shape : Stack.Shape := ⟨captures.length, saved.size, 0⟩
  pure ⟨(if shape.needed then Stack.push ctx.storage shape else []) ++
      inputs ++ save ++ chain.commands ++ restore ++
      (if shape.needed then Stack.pop ctx.storage else []),
    helpers ++ chain.helpers⟩
where
  wrap (call finish : List (Command .plain)) : Except Diagnostic (FunctionRef .plain × List PackedFunction) := do
    let wrapper ← ctx.config.function (path ++ "/body")
    pure (wrapper, [⟨.plain, ⟨wrapper, .plain (call ++ finish).toArray⟩⟩])

end Oria.Lower.DP121.Execute
