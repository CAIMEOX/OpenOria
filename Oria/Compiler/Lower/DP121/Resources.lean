module

public import Oria.Compiler.RegAlloc
import Oria.IR.Machine.Transform
import Lean.Util.SCC

namespace Oria.Lower.DP121.Resources

open Oria.IR Oria.IR.Machine

/-- Invocation-owned storage required by an entry's transitive callees. -/
public structure Usage where
  arena : Bool := false
  projection : Bool := false
  nbt : Bool := false
  macros : Bool := false
  memory : Bool := false
  stack : Bool := false

private def Usage.union (a b : Usage) : Usage :=
  ⟨a.arena || b.arena, a.projection || b.projection, a.nbt || b.nbt,
    a.macros || b.macros, a.memory || b.memory, a.stack || b.stack⟩

private def hole {n : Nat} {a : ObjTy} (value : Atom n) : Usage :=
  { macros := match a, value with | .i32, .lit _ => false | _, _ => true,
    projection := match a with | .nbt _ => true | _ => false }

private def operation {f : List IR.Machine.Signature} {n m : Nat} : Op f n m → Usage
  | .allocate .. => { arena := true }
  | .checkpoint _ => {}
  | .tag _ | .project .. => { projection := true }
  | .promote .. => { memory := true }
  | .rootGet _ | .rootSet .. | .refNew .. | .refGet .. | .refSet .. => { memory := true }
  | .nbt .forget _ => {}
  | .nbt (.inspectRef (.global _) path _) args =>
      { macros := path.segments.any fun
          | .index i => match i.lookup args with | .lit _ => false | _ => true
          | _ => false }
  | .nbt (.putRef (.global _) ..) _ | .nbt (.clearRef (.global _) ..) _
  | .nbt (.copyRef (.global _) _ (.global _) _ _) _ => { macros := true }
  | .nbt (.exportRef (.global _) ..) _ => { projection := true, macros := true }
  | .nbt _ _ => { arena := true, projection := true, nbt := true, macros := true }
  | .command request => request.traverseK
      (fun {a} value next => (hole (a := a) value).union (next value)) (fun _ => {})
  | .execute scope _ _ _ => scope.traverseK
      (fun {a} value next => (hole (a := a) value).union (next value)) (fun _ => {})
  | .unary .. | .binary .. | .division .. | .call .. => {}

/-- Lean's dependency-first SCC order computes the same storage union for every recursive member.
The scan consumes Machine operations and allocation results, before entry wrappers are emitted. -/
public def analyze {s : Oria.Program.ClosedProgram} {k : Nat} (p : IR.Machine.Program s)
    (plan : RegAlloc.Plan p k) : Vector Usage (signatures p.table s).length := Id.run do
  let count := (signatures p.table s).length
  let direct := Vector.ofFn fun i : Fin count =>
    let fn := plan.functions.get i
    (List.finRange (p.definitionAt i).layout.length).foldl (init :=
      ({ stack := fn.slots != 0 || fn.resultOverflow != 0 } : Usage)) fun usage b =>
      let block := fn.blocks.get b
      let stack := block.saved.any (! ·.isEmpty) || block.info.points.any fun point =>
        point.forks && point.callee.any fun j =>
          if h : j < count then
            (Analysis.Demand.blockInfo p plan.demand ⟨j, h⟩ (p.definitionAt ⟨j, h⟩).entry.index).parameters != 0
          else false
      let usage := { usage with stack := usage.stack || stack }
      ((p.definitionAt i).blocks.get b).foldOps (fun usage op => usage.union (operation op)) usage
  let callees i := (List.finRange (p.definitionAt i).layout.length).flatMap fun b =>
    (plan.functions.get i |>.blocks.get b).info.points.toList.filterMap fun point => do
      let j ← point.callee
      if h : j < count then some (⟨j, h⟩ : Fin count) else none
  let mut summaries := Vector.replicate count ({} : Usage)
  for group in Lean.SCC.scc (List.finRange count) callees do
    let usage := group.foldl (init := ({} : Usage)) fun usage i =>
      (callees i).foldl (fun usage j => usage.union summaries[j]) (usage.union direct[i])
    for i in group do summaries := summaries.set i usage
  return summaries

end Oria.Lower.DP121.Resources
