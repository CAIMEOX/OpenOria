module

public import Oria.Compiler.RegAlloc
public import Oria.Compiler.Lower.DP121.Emit
public import Oria.Compiler.Lower.DP121.Resources

namespace Oria.Lower.DP121.Calling

open Oria.IR Oria.Target.DP121

public structure Context {source : Oria.Program.ClosedProgram} (program : Machine.Program source)
    (k : Nat) where
  config : Config
  plan : RegAlloc.Plan program k
  bank : Layout k
  storage : ResourceId
  resources : Vector Resources.Usage (Machine.signatures program.table source).length

variable {source : Oria.Program.ClosedProgram} {program : Machine.Program source} {k : Nat}

public def resultPlace {slots : Nat} (ctx : Context program k) : RegAlloc.Loc 2 slots → Place
  | .reg r => .score ctx.bank.results[r]
  | .stack s => .storage (Stack.slot ctx.storage .current .result s.val)

/-- The callee frame owns spill words; its saved region protects this call site's caller. -/
public def invoke (ctx : Context program k)
    (callee : Fin (Machine.signatures program.table source).length) (saved : Array (Fin k))
    (arguments results : Stack.Frame → Except Diagnostic (List (Transfer.Move Place))) :
    Except Diagnostic (List (Command .plain)) := do
  let plan := ctx.plan.functions.get callee
  let shape : Stack.Shape := ⟨plan.slots, saved.size, plan.resultOverflow⟩
  let frame := if shape.needed then Stack.Frame.caller else .current
  let arguments ← arguments frame
  let results ← results frame
  let save := saved.toList.zipIdx.map fun (r, i) =>
    Stack.move ⟨.storage (Stack.slot ctx.storage .current .saved i),
      .loc (.score ctx.bank.registers[r])⟩
  let restore := saved.toList.zipIdx.map fun (r, i) =>
    Stack.move ⟨.score ctx.bank.registers[r],
      .loc (.storage (Stack.slot ctx.storage .current .saved i))⟩
  let stackArguments := arguments.filter fun move => match move.target with
    | .storage _ => true | .score _ => false
  let registerArguments := arguments.filter fun move => match move.target with
    | .score _ => true | .storage _ => false
  let inputs ← Stack.parallel ctx.bank registerArguments
  let outputs ← Stack.parallel ctx.bank results
  let defn := program.definitionAt callee
  let target ← ctx.config.function s!"__oria/m{callee.val}/b{defn.entry.index.val}"
  pure ((if shape.needed then Stack.push ctx.storage shape else []) ++ save ++
    stackArguments.map Stack.move ++ inputs ++ [.function target] ++ restore ++ outputs ++
    (if shape.needed then Stack.pop ctx.storage else []))

end Oria.Lower.DP121.Calling
