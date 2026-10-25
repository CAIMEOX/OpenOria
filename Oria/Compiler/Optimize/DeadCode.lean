module

public import Oria.Compiler.Analysis.Demand
public import Oria.Compiler.Optimize.ControlFlow

namespace Oria.Optimize.DeadCode

open Oria.IR Oria.IR.Machine

/- Lean's LCNF use-def pass is indexed by Lean declarations. Oria reuses its Machine
   demand analysis and scoped substitutions. Machine division exposes failure as an
   ordinary result word; discarding both words discards the whole scalar computation. -/
private def discardable {f : List IR.Machine.Signature} {n m : Nat} : Op f n m → Bool
  | .unary .. | .binary .. | .division .. | .allocate .. | .tag .. | .project .. => true
  | _ => false

/-- Canonical padding gives all unobserved return channels the same representation. -/
private def returns {l : List Nat} {r n : Nat} (mask : BitVec r) :
    Terminator l r n → Terminator l r n
  | .ret values => .ret (Vector.ofFn fun i => if mask.getLsb i then values[i] else .lit 0)
  | exit => exit

/-- One backward traversal removes dead pure prefixes and their binder positions. -/
private def body {f : List IR.Machine.Signature} {l : List Nat} {r n : Nat}
    (params : {m : Nat} → Scope.Var Unit l m → BitVec m)
    (calls : {sig : IR.Machine.Signature} → Scope.Var Unit f sig → BitVec sig.args)
    (result : BitVec r) : Body f l r n → BitVec n × Body f l r n
  | .done exit =>
      let exit := returns result exit
      (Analysis.Machine.exit params result exit, .done exit)
  | .step (m := m) op next =>
      let (used, next) := body params calls result next
      let out := used.extractLsb' 0 m
      let before := used.extractLsb' m n
      if discardable op && out == 0 then
        let σ : Subst (m + n) n := fun i =>
          if h : i.val < m then .lit 0 else .var ⟨i.val - m, by omega⟩
        (before, next.subst σ)
      else
        (before ||| Analysis.Machine.inputs calls op out, .step op next)

private def instructions {f : List IR.Machine.Signature} {l : List Nat} {r n : Nat} : Body f l r n → Nat
  | .done _ => 0
  | .step _ next => 1 + instructions next

private def weight {s : Oria.Program.ClosedProgram} (p : Machine.Program s) : Nat :=
  (List.finRange (signatures p.table s).length).foldl (init := 0) fun total i =>
    let d := p.definitionAt i
    total + d.layout.length + (List.finRange d.layout.length).foldl
      (fun total b => total + instructions (d.blocks.get b)) 0

/-- Recompute demand after each shrinking CFG rewrite, before freezing allocation metadata. -/
public def run {s : Oria.Program.ClosedProgram} (p : Machine.Program s) :
    Except Diagnostic (Machine.Program s) := do
  let demand := Analysis.Demand.analyze p
  let definitions ← Data.IndexedVector.ofFnM fun i => do
    let d := p.definitionAt i
    let info := Analysis.Demand.functionInfo p demand i
    let blocks := Data.IndexedVector.ofFn fun b =>
      body (fun target => target.typeCorrect ▸
        (Analysis.Demand.blockInfo p demand i target.index).parameters)
        (Analysis.Demand.parameters p demand) info.result (d.blocks.get b) |>.2
    Optimize.Machine.controlFlow s.members[memberPosition p.table s i].source { d with blocks }
  let next := { p with definitions }
  if _h : weight next < weight p then run next else pure next
termination_by weight p

end Oria.Optimize.DeadCode
