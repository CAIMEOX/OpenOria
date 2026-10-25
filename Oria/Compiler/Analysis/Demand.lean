module

public import Oria.Compiler.Analysis.Machine
public import Std.Data.DHashMap.Basic
import Init.Data.Queue
import Std.Data.HashSet.Basic

namespace Oria.Analysis.Demand

open Oria.IR Oria.IR.Machine

/-- One mask for block parameters and one flat mask per instruction result tuple. -/
public structure BlockInfo (n : Nat) where
  parameters : BitVec n := 0
  outputs : Array Nat := #[]
  deriving BEq, Inhabited

public structure FunctionInfo (layout : List Nat) (result : Nat) where
  result : BitVec result := 0
  blocks : Std.DHashMap (Fin layout.length) (fun i => BlockInfo (layout.get i)) := {}

public instance {layout : List Nat} {result : Nat} : Inhabited (FunctionInfo layout result) :=
  ⟨{}⟩
public instance {layout : List Nat} {result : Nat} : BEq (FunctionInfo layout result) where
  beq a b := a.result == b.result && a.blocks.beq b.blocks

/-- Sparse tables use the zero demand as their missing-entry interpretation. -/
public abbrev Info {source : Oria.Program.ClosedProgram} (program : IR.Machine.Program source) :=
  Std.DHashMap (Fin (signatures program.table source).length) fun i =>
    FunctionInfo (program.definitionAt i).layout ((signatures program.table source).get i).result

public def functionInfo {source : Oria.Program.ClosedProgram}
    (program : IR.Machine.Program source) (info : Info program)
    (i : Fin (signatures program.table source).length) :=
  info.getD i {}

public def blockInfo {source : Oria.Program.ClosedProgram}
    (program : IR.Machine.Program source) (info : Info program)
    (i : Fin (signatures program.table source).length) (b : Fin (program.definitionAt i).layout.length) :=
  (functionInfo program info i).blocks.getD b {}

public def parameters {source : Oria.Program.ClosedProgram} {sig : IR.Machine.Signature}
    (program : IR.Machine.Program source) (info : Info program)
    (callee : Scope.Var Unit (signatures program.table source) sig) : BitVec sig.args :=
  let demand := functionInfo program info callee.index
  let defn := program.definitionAt callee.index
  let mask := (demand.blocks.getD defn.entry.index {}).parameters
  callee.typeCorrect ▸ (defn.entry.typeCorrect ▸ mask)

public def terminatorUses {layout : List Nat} {result n : Nat}
    (info : FunctionInfo layout result) :
    Terminator layout result n → BitVec n :=
  Analysis.Machine.exit (fun target => target.typeCorrect ▸
    (info.blocks.getD target.index {}).parameters) info.result

private def operationUses {source : Oria.Program.ClosedProgram} {n m : Nat}
    (program : IR.Machine.Program source)
    (operation : Op (signatures program.table source) n m) (out : BitVec m) :
    StateM (Info program) (BitVec n) := do
  match operation with
  | .execute scope canFail callee _ =>
      let info ← get
      let demand := functionInfo program info callee.index
      let mask : BitVec (canFail.toNat + 1) := BitVec.ofNat _
        ((if canFail && scope.captureSuccess then 1 else 0) +
          (if scope.captureResult then 2 ^ canFail.toNat else 0))
      let result : BitVec ((signatures program.table source).get callee.index).result :=
        callee.typeCorrect.symm ▸ mask
      set (info.insert callee.index { demand with result := demand.result ||| result })
  | .call callee _ =>
      let info ← get
      let demand := functionInfo program info callee.index
      let result : BitVec ((signatures program.table source).get callee.index).result :=
        callee.typeCorrect.symm ▸ out
      let demand := { demand with result := demand.result ||| result }
      set (info.insert callee.index demand)
  | _ => pure ()
  pure (Analysis.Machine.inputs (parameters program (← get)) operation out)

private def walk {source : Oria.Program.ClosedProgram} {n : Nat}
    (program : IR.Machine.Program source)
    (i : Fin (signatures program.table source).length)
    (comp : Body (signatures program.table source) (program.definitionAt i).layout
      ((signatures program.table source).get i).result n) :
    StateM (Info program) (BitVec n × List Nat) := do
  match comp with
  | .done exit =>
      pure (terminatorUses (functionInfo program (← get) i) exit, [])
  | .step (m := m) op next =>
      let (after, outputs) ← walk program i next
      let demanded := after.extractLsb' 0 m
      let inputs ← operationUses program op demanded
      let before := after.extractLsb' m n ||| inputs
      pure (before, demanded.toNat :: outputs)

private abbrev Work {source : Oria.Program.ClosedProgram} (program : IR.Machine.Program source) :=
  (i : Fin (signatures program.table source).length) × Fin (program.definitionAt i).layout.length

private def key {source : Oria.Program.ClosedProgram} {program : IR.Machine.Program source}
    (work : Work program) : Nat × Nat := (work.1.val, work.2.val)

private structure Dependencies {source : Oria.Program.ClosedProgram}
    (program : IR.Machine.Program source) where
  predecessors : Std.HashMap (Nat × Nat) (List (Work program)) := {}
  callers : Std.HashMap Nat (List (Work program)) := {}
  returns : Std.HashMap Nat (List (Work program)) := {}

private def dependencies {source : Oria.Program.ClosedProgram} {n : Nat}
    (program : IR.Machine.Program source) (work : Work program) :
    Body (signatures program.table source) (program.definitionAt work.1).layout
      ((signatures program.table source).get work.1).result n → StateM (Dependencies program) Unit
  | .step op next => do
      match op with
      | .call callee _ | .execute _ _ callee _ => modify fun d => { d with
          callers := d.callers.insert callee.index.val (work :: d.callers.getD callee.index.val []) }
      | _ => pure ()
      dependencies program work next
  | .done exit => do
      match exit with
      | .ret _ => modify fun d => { d with
          returns := d.returns.insert work.1.val (work :: d.returns.getD work.1.val []) }
      | .jump edge => addEdge edge
      | .branch _ yes no => addEdge yes *> addEdge no
      | .switch _ cases fallback =>
          cases.forM (addEdge ·.2) *> fallback.forM addEdge
where
  addEdge {n : Nat} (edge : Edge (program.definitionAt work.1).layout n) :
      StateM (Dependencies program) Unit :=
    modify fun d =>
      let target := (work.1.val, edge.target.index.val)
      { d with predecessors := d.predecessors.insert target (work :: d.predecessors.getD target []) }

private structure Pending {source : Oria.Program.ClosedProgram}
    (program : IR.Machine.Program source) where
  queue : Std.Queue (Work program) := .empty
  queued : Std.HashSet (Nat × Nat) := {}

private def enqueue {source : Oria.Program.ClosedProgram} {program : IR.Machine.Program source}
    (pending : Pending program) (work : Work program) : Pending program :=
  if pending.queued.contains (key work) then pending
  else ⟨pending.queue.enqueue work, pending.queued.insert (key work)⟩

/-- Monotone worklist propagation, revisiting only consumers of changed demands. -/
private def solve {source : Oria.Program.ClosedProgram}
    (program : IR.Machine.Program source) (initial : Info program) : Info program := Id.run do
  let mut pending : Pending program := {}
  let mut deps : Dependencies program := {}
  for i in List.finRange (signatures program.table source).length do
    for b in List.finRange (program.definitionAt i).layout.length do
      let work : Work program := ⟨i, b⟩
      pending := enqueue pending work
      deps := (dependencies program work ((program.definitionAt i).blocks.get b)).run deps |>.2
  let mut info := initial
  while let some (work, rest) := pending.queue.dequeue? do
    pending := ⟨rest, pending.queued.erase (key work)⟩
    let previous := info
    let ((parameters, outputs), next) :=
      (walk program work.1 ((program.definitionAt work.1).blocks.get work.2)).run info
    let demand := functionInfo program next work.1
    info := next.insert work.1 { demand with
      blocks := demand.blocks.insert work.2 ⟨parameters, outputs.toArray⟩ }
    if parameters != (blockInfo program previous work.1 work.2).parameters then
      pending := (deps.predecessors.getD (key work) []).foldl enqueue pending
      if work.2 == (program.definitionAt work.1).entry.index then
        pending := (deps.callers.getD work.1.val []).foldl enqueue pending
    for i in List.finRange (signatures program.table source).length do
      if (functionInfo program previous i).result != (functionInfo program info i).result then
        pending := (deps.returns.getD i.val []).foldl enqueue pending
  return info

public def analyze {source : Oria.Program.ClosedProgram}
    (program : IR.Machine.Program source) : Info program :=
  let roots := source.roots.foldl (init := ({} : Info program)) fun info entry =>
    let index := (referenceAt program.table source entry.position).index
    let demand := functionInfo program info index
    info.insert index { demand with result := BitVec.allOnes _ }
  solve program roots

end Oria.Analysis.Demand
