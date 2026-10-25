module

public import Oria.Compiler.Optimize.ControlFlow
public import Oria.Compiler.Optimize.Conditions
public import Oria.Compiler.Optimize.DeadCode

namespace Oria.Optimize.Machine

open Oria.IR Oria.IR.Machine

/-- A self call returning its result unchanged transfers directly to the entry block. -/
private def body {functions : List IR.Machine.Signature} {sig : IR.Machine.Signature}
    {layout : List Nat} {n : Nat}
    (self : Scope.Var Unit functions sig) (entry : Scope.Var Unit layout sig.args) :
    Body functions layout sig.result n → Body functions layout sig.result n
  | .done exit => .done exit
  | .step (.call (sig := calleeSig) callee args) (.done (.ret values)) =>
      if same : callee.index = self.index then
        have signature : calleeSig = sig :=
          callee.typeCorrect.symm.trans ((congrArg functions.get same).trans self.typeCorrect)
        have resultSame := congrArg IR.Machine.Signature.result signature
        let results : Vector (Atom (calleeSig.result + n)) sig.result :=
          Vector.ofFn fun i => .var ⟨i.val, by omega⟩
        if values = results then
          .done (.jump ⟨entry, congrArg IR.Machine.Signature.args signature ▸ args⟩)
        else .step (.call callee args) (.done (.ret values))
      else .step (.call callee args) (.done (.ret values))
  | .step op next => .step op (body self entry next)

/-- Reuse one activation for self tail recursion before demand and register allocation. -/
public def tailCalls {functions : List IR.Machine.Signature} {sig : IR.Machine.Signature}
    (self : Scope.Var Unit functions sig) (definition : Def functions sig) : Def functions sig :=
  { definition with blocks := Data.IndexedVector.ofFn (fun i =>
      body self definition.entry (definition.blocks.get i)) }

/-- Expose tail calls through linear joins, then simplify their new backedges. -/
public def run {f : List IR.Machine.Signature} {s : IR.Machine.Signature}
    (source : Lean.Name) (self : Scope.Var Unit f s) (definition : Def f s) :
    Except Diagnostic (Def f s) := do
  let definition ← controlFlow source definition
  controlFlow source (tailCalls self definition)

end Oria.Optimize.Machine
