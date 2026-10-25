module

public import Oria.IR.Machine.Program
import Oria.IR.Machine.Transform

namespace Oria.Analysis.Suspension

open Oria.IR Oria.IR.Machine

/-- Actual suspension through the closed call graph, independent of effect upper bounds. -/
public def analyze {s : Oria.Program.ClosedProgram} (p : IR.Machine.Program s) :
    Vector Bool (signatures p.table s).length := Id.run do
  let count := (signatures p.table s).length
  let mut known := Vector.replicate count false
  let mut changed := true
  while changed do
    changed := false
    for i in List.finRange count do
      let found := (List.finRange (p.definitionAt i).layout.length).any fun b =>
        ((p.definitionAt i).blocks.get b).foldOps (fun found op => found || match op with
          | .checkpoint _ => true
          | .call callee _ | .execute _ _ callee _ => known[callee.index]
          | _ => false) false
      if found && !known[i] then
        known := known.set i true
        changed := true
  return known

end Oria.Analysis.Suspension
