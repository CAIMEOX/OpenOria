module

public import Oria.Compiler.RegAlloc
public import Init.Data.Format.Basic

namespace Oria.RegAlloc

open Std Std.Format Oria.IR

private def location {k slots : Nat} : Loc k slots → Format
  | .reg r => "r" ++ toString r.val
  | .stack s => "stack[" ++ toString s.val ++ "]"

private def sequence (values : List Format) : Format :=
  group ("[" ++ nest 2 (joinSep values ("," ++ line)) ++ "]")

private def block {k n : Nat} (block : BlockPlan k n) : Format :=
  let homes := (List.finRange block.info.ranges.size).filterMap fun i => do
    let range ← block.info.ranges[i.val]
    let home ← block.assignment.homes[i.val]
    pure ("v" ++ toString i.val ++ " : [" ++ toString range.start ++ ", " ++
      toString range.stop ++ ") -> " ++ location home : Format)
  let calls := block.info.points.toList.zipIdx.filterMap fun (point, i) => do
    let callee ← point.callee
    let saved := block.saved[i]?.getD #[]
    pure ("call i" ++ toString i ++ " @" ++ toString callee ++ " save " ++
      sequence (saved.toList.map fun r => "r" ++ toString r.val) : Format)
  joinSep (homes ++ calls) line

public def Plan.format {k : Nat} {source : Oria.Program.ClosedProgram}
    {program : Machine.Program source} (plan : Plan program k) : Format :=
  let functions := (List.finRange (Machine.signatures program.table source).length).map fun i =>
    let function := plan.functions.get i
    let blocks := (List.finRange (program.definitionAt i).layout.length).map fun b =>
      "b" ++ toString b.val ++ " {" ++ nest 2 (line ++ block (function.blocks.get b)) ++ line ++ "}"
    let returns := function.returns.toList.map fun
      | none => "dead"
      | some (.reg r) => "ret" ++ toString r.val
      | some (.stack s) => "result[" ++ toString s.val ++ "]"
    group ("@" ++ toString i.val ++ " locals=" ++ toString function.slots ++
      " returns=" ++ sequence returns) ++ line ++ joinSep blocks line
  "registers=" ++ toString k ++ line ++ joinSep functions (line ++ line)

end Oria.RegAlloc
