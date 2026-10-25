module

public import Oria.Compiler.Lower.DP121.Calling

namespace Oria.Lower.DP121.Values

open Oria.IR Oria.Target.DP121

variable {source : Oria.Program.ClosedProgram} {program : Machine.Program source} {k : Nat}

private def failure (i : Fin (Machine.signatures program.table source).length) : Diagnostic :=
  .invalidRegisterAllocation source.members[Machine.memberPosition program.table source i].source

public def position (ctx : Calling.Context program k)
    (i : Fin (Machine.signatures program.table source).length) (b : Fin (program.definitionAt i).layout.length)
    (id : Nat) (frame : Stack.Frame) : Except Diagnostic (Option Place) := do
  let assigned := (ctx.plan.functions.get i).blocks.get b |>.assignment
  let some home := assigned.homes.toArray[id]? | throw (failure i)
  pure (home.map (Stack.place ctx.bank ctx.storage frame))

public def operand {n : Nat} (ctx : Calling.Context program k)
    (i : Fin (Machine.signatures program.table source).length) (b : Fin (program.definitionAt i).layout.length)
    (frame : Stack.Frame) : Machine.Atom n → Except Diagnostic (Transfer.Source Place)
  | .lit value => pure (.imm value)
  | .var x => do
      let some home ← position ctx i b (Analysis.Machine.number x) frame | throw (failure i)
      pure (.loc home)

public def targets (ctx : Calling.Context program k)
    (i : Fin (Machine.signatures program.table source).length) (b : Fin (program.definitionAt i).layout.length)
    (scope results : Nat) (frame : Stack.Frame) : Except Diagnostic (Vector (Option Place) results) :=
  Vector.ofFnM fun j => position ctx i b (scope + results - 1 - j.val) frame

public def parameters (ctx : Calling.Context program k)
    (i : Fin (Machine.signatures program.table source).length) (b : Fin (program.definitionAt i).layout.length) :
    Except Diagnostic (Vector (Option Place) ((program.definitionAt i).layout.get b)) :=
  targets ctx i b 0 _ .current

public def copies {m n : Nat} (ctx : Calling.Context program k)
    (i : Fin (Machine.signatures program.table source).length) (b : Fin (program.definitionAt i).layout.length)
    (frame : Stack.Frame) (destinations : Vector (Option Place) m)
    (values : Vector (Machine.Atom n) m) : Except Diagnostic (List (Transfer.Move Place)) :=
  (List.finRange m).filterMapM fun j => do
    match destinations.get j with
    | none => pure none
    | some target => pure (some ⟨target, ← operand ctx i b frame (values.get j)⟩)

end Oria.Lower.DP121.Values
