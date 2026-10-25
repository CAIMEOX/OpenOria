module

public import Oria.Compiler.Analysis.Liveness
public import Oria.Compiler.RegAlloc.LinearScan
public import Oria.Diagnostic
import Oria.IR.Machine.Transform
import Lean.Util.SCC

namespace Oria.RegAlloc

open Oria.IR Oria.IR.Machine

public structure BlockPlan (registers : Nat) (scope : Nat) where
  info : Analysis.Liveness.Block scope
  assignment : Assignment registers info.ranges
  saved : Array (Array (Fin registers))

public structure FunctionPlan {source : Oria.Program.ClosedProgram}
    (program : Machine.Program source)
    (demand : Analysis.Demand.Info program)
    (registers : Nat)
    (i : Fin (Machine.signatures program.table source).length) where
  blocks : Data.IndexedVector (fun b =>
    BlockPlan registers ((program.definitionAt i).layout.get b))
  slots : Nat
  resultOverflow : Nat
  returns : Vector (Option (Loc 2 resultOverflow))
    ((Machine.signatures program.table source).get i).result
  clobbers : BitVec registers

public structure Plan {source : Oria.Program.ClosedProgram}
    (program : Machine.Program source) (registers : Nat) where
  demand : Analysis.Demand.Info program
  functions : Data.IndexedVector (fun i => FunctionPlan program demand registers i)

private def resultDemanded {result : Nat} (demand : BitVec result) : List (Fin result) :=
  (List.finRange result).filter (fun i => demand.getLsb i)

private def rankBefore {result : Nat} (demand : BitVec result) (i : Fin result) : Nat :=
  (List.finRange result).filter (fun j =>
    j.val < i.val && demand.getLsb j) |>.length

private def returnHome (overflow rank : Nat) : Option (Loc 2 overflow) :=
  if h : rank < 2 then
    some (.reg ⟨rank, h⟩)
  else
    let slot := rank - 2
    if h : slot < overflow then some (.stack ⟨slot, h⟩) else none

private def returnVector {result : Nat} (demand : BitVec result) :
    Sigma (fun overflow => Vector (Option (Loc 2 overflow)) result) :=
  let demanded := resultDemanded demand
  let overflow := demanded.length - 2
  ⟨overflow, Vector.ofFn fun i =>
    if demand.getLsb i then returnHome overflow (rankBefore demand i) else none⟩

private def blockSlots
    {registers : Nat} {layout : List Nat}
    (blocks : Data.IndexedVector (fun b => BlockPlan registers (layout.get b))) : Nat :=
  (List.finRange layout.length).foldl
    (fun slots b => max slots (blocks.get b).assignment.slots) 0

private def blockPlanWith {source : Oria.Program.ClosedProgram}
    (program : Machine.Program source)
    (demand : Analysis.Demand.Info program)
    (registers : Nat)
    (i : Fin (Machine.signatures program.table source).length)
    (cost : Nat → Fin registers → Nat)
    (b : Fin (program.definitionAt i).layout.length) :
    Except Diagnostic (BlockPlan registers ((program.definitionAt i).layout.get b)) := do
  let info := Analysis.Liveness.analyzeBlock program demand i b
  let some assignment := RegAlloc.allocate registers info.ranges cost
    | let position : Fin source.members.size :=
        ⟨i.val, by simpa [Machine.signatures] using i.isLt⟩
      throw (.invalidRegisterAllocation source.members[position].source)
  pure { info, assignment, saved := #[] }

private def baseFunctionWith {source : Oria.Program.ClosedProgram}
    (program : Machine.Program source)
    (demand : Analysis.Demand.Info program)
    (registers : Nat)
    (i : Fin (Machine.signatures program.table source).length)
    (cost : (b : Fin (program.definitionAt i).layout.length) →
      Nat → Fin registers → Nat) :
    Except Diagnostic (FunctionPlan program demand registers i) := do
  let blocks ← Data.IndexedVector.ofFnM
    (fun b => blockPlanWith program demand registers i (cost b) b)
  let result := Analysis.Demand.functionInfo program demand i |>.result
  let ⟨overflow, returns⟩ := returnVector result
  pure {
    blocks := blocks
    slots := blockSlots blocks
    resultOverflow := overflow
    returns := returns
    clobbers := 0
  }

private def baseFunction {source : Oria.Program.ClosedProgram}
    (program : Machine.Program source)
    (demand : Analysis.Demand.Info program)
    (registers : Nat)
    (i : Fin (Machine.signatures program.table source).length) :
    Except Diagnostic (FunctionPlan program demand registers i) := do
  baseFunctionWith program demand registers i (fun _ _ _ => 0)

private def baseFunctions {source : Oria.Program.ClosedProgram}
    (program : Machine.Program source)
    (demand : Analysis.Demand.Info program)
    (registers : Nat) :
    Except Diagnostic (Data.IndexedVector (fun i =>
      FunctionPlan program demand registers i)) :=
  Data.IndexedVector.ofFnM (fun i => baseFunction program demand registers i)

private def registerBit (registers : Nat) (register : Fin registers) : BitVec registers :=
  BitVec.ofNat registers (1 <<< register.val)

private def homeMask
    {size registers slots : Nat}
    (homes : Vector (Option (Loc registers slots)) size) : BitVec registers :=
  (List.finRange size).foldl (fun mask i =>
    match homes.get i with
    | some (.reg register) => mask ||| registerBit registers register
    | _ => mask) 0

private def blockMask {registers scope : Nat}
    (block : BlockPlan registers scope) : BitVec registers :=
  homeMask block.assignment.homes

private def parametersMask
    {registers scope : Nat} (block : BlockPlan registers scope) : BitVec registers :=
  (List.finRange scope).foldl (fun mask i =>
    if block.info.parameters.getLsb i then
      let stable := scope - 1 - i.val
      match block.assignment.homes.toArray[stable]? with
      | some (some (.reg register)) => mask ||| registerBit registers register
      | _ => mask
    else mask) 0

private def allBlockMask {source : Oria.Program.ClosedProgram} {program : Machine.Program source}
    {registers : Nat} {i : Fin (Machine.signatures program.table source).length}
    (demand : Analysis.Demand.Info program)
    (base : FunctionPlan program demand registers i) : BitVec registers :=
  (List.finRange (program.definitionAt i).layout.length).foldl
    (fun mask b => mask ||| blockMask (base.blocks.get b)) 0

private def entryMask {source : Oria.Program.ClosedProgram} {registers : Nat}
    (program : Machine.Program source)
    (demand : Analysis.Demand.Info program)
    (baseFunctions : Data.IndexedVector (fun i => FunctionPlan program demand registers i))
    (callee : Nat) : BitVec registers :=
  if h : callee < (Machine.signatures program.table source).length then
    let target : Fin (Machine.signatures program.table source).length := ⟨callee, h⟩
    let defn := program.definitionAt target
    parametersMask (baseFunctions.get target |>.blocks.get defn.entry.index)
  else
    0

private def callMask {source : Oria.Program.ClosedProgram} {registers : Nat}
    (program : Machine.Program source)
    (demand : Analysis.Demand.Info program)
    (baseFunctions : Data.IndexedVector (fun i => FunctionPlan program demand registers i))
    (known : Array (BitVec registers))
    (point : Analysis.Liveness.Point) : BitVec registers :=
  match point.callee with
  | none => 0
  | some callee => (known[callee]?).getD 0 ||| entryMask program demand baseFunctions callee

private def functionClobber {source : Oria.Program.ClosedProgram} {registers : Nat}
    (program : Machine.Program source)
    (demand : Analysis.Demand.Info program)
    (baseFunctions : Data.IndexedVector (fun i => FunctionPlan program demand registers i))
    (known : Array (BitVec registers))
    (i : Fin (Machine.signatures program.table source).length) : BitVec registers :=
  let base := baseFunctions.get i
  let bodyMask := (List.finRange (program.definitionAt i).layout.length).foldl
    (fun mask b =>
      (base.blocks.get b).info.points.foldl
        (fun mask point => mask ||| callMask program demand baseFunctions known point) mask) 0
  allBlockMask demand base ||| bodyMask

private def clobbers {source : Oria.Program.ClosedProgram} {registers : Nat}
    (program : Machine.Program source)
    (demand : Analysis.Demand.Info program)
    (baseFunctions : Data.IndexedVector (fun i => FunctionPlan program demand registers i)) :
    Array (BitVec registers) := Id.run do
  let count := (Machine.signatures program.table source).length
  let mut values : Array (BitVec registers) := Array.replicate count 0
  let mut changed := true
  while changed do
    changed := false
    for i in List.finRange count do
      let next := functionClobber program demand baseFunctions values i
      if next != (values[i.val]?).getD 0 then
        values := values.set! i.val next
        changed := true
  return values

-- Placement preferences carry no correctness evidence: interval validation and
-- the final clobber/save analysis check the selected assignment independently.
private def affinities {source : Oria.Program.ClosedProgram} {registers : Nat}
    (program : Machine.Program source) (demand : Analysis.Demand.Info program)
    (i : Fin (Machine.signatures program.table source).length)
    (seed : FunctionPlan program demand registers i) : Array (List (Nat × Fin registers)) := Id.run do
  let d := program.definitionAt i
  let home (block : Fin d.layout.length) (id : Nat) : Option (Fin registers) := do
    let some (.reg r) ← (seed.blocks.get block).assignment.homes.toArray[id]? | none
    pure r
  let mut hints := Array.replicate d.layout.length []
  for p in List.finRange d.layout.length do
    let ⟨_, exit⟩ := (d.blocks.get p).exit
    let (_, edges) := (exit.traverse Atom.var (fun e => do
      modify (e :: ·)
      pure e) : StateM _ _).run []
    for e in edges do
      for j in List.finRange e.arity do
        if let .var v := e.values[j] then
          let src := Analysis.Machine.number v
          let dst := e.arity - 1 - j.val
          if let some r := home e.target.index dst then
            hints := hints.modify p.val ((src, r) :: ·)
          if let some r := home p src then
            hints := hints.modify e.target.index.val ((dst, r) :: ·)
  for b in List.finRange d.layout.length do
    let localHints := (d.blocks.get b).foldOps (fun {n m} hints op =>
      let input : Option (Machine.Atom n) := match op with
        | .binary .add l _ | .binary .sub l _ | .binary .mul l _ | .division l _ => some l
        | _ => none
      match input with
      | some (.var v) =>
          match home b (Analysis.Machine.number v) with
          | some r =>
              let output := match op with | .division .. => 1 | _ => 0
              (n + m - 1 - output, r) :: hints
          | none => hints
      | _ => hints) (hints[b.val]?.getD [])
    hints := hints.set! b.val localHints
  return hints

private def preferredBaseFunction {source : Oria.Program.ClosedProgram}
    (program : Machine.Program source)
    (demand : Analysis.Demand.Info program)
    (registers : Nat)
    (seedBases : Data.IndexedVector (fun i => FunctionPlan program demand registers i))
    (known : Array (BitVec registers))
    (i : Fin (Machine.signatures program.table source).length) :
    Except Diagnostic (FunctionPlan program demand registers i) := do
  let seed := seedBases.get i
  let affinities := affinities program demand i seed
  let blocks ← Data.IndexedVector.ofFnM (fun b => do
    let block := seed.blocks.get b
    let hints := affinities[b.val]?.getD []
    let cost : Nat → Fin registers → Nat :=
      fun id register =>
        let calls := block.info.points.foldl (fun cost point =>
          if point.acrossValue id &&
              (callMask program demand seedBases known point).getLsb register then cost + 1
          else cost) 0
        calls * (hints.length + 1) +
          (hints.filter fun (v, preferred) => v == id && register != preferred).length
    let some assignment := RegAlloc.allocate registers block.info.ranges cost
      | let position : Fin source.members.size :=
          ⟨i.val, by simpa [Machine.signatures] using i.isLt⟩
        throw (.invalidRegisterAllocation source.members[position].source)
    pure { info := block.info, assignment, saved := #[] })
  pure {
    blocks := blocks
    slots := blockSlots blocks
    resultOverflow := seed.resultOverflow
    returns := seed.returns
    clobbers := 0
  }

private def preferredBaseFunctions {source : Oria.Program.ClosedProgram}
    (program : Machine.Program source)
    (demand : Analysis.Demand.Info program)
    (registers : Nat)
    (seedBases : Data.IndexedVector (fun i => FunctionPlan program demand registers i)) :
    Except Diagnostic (Data.IndexedVector (fun i => FunctionPlan program demand registers i)) := do
  let count := (Machine.signatures program.table source).length
  let successors i := (List.finRange (program.definitionAt i).layout.length).flatMap fun b =>
    (seedBases.get i |>.blocks.get b).info.points.toList.filterMap fun point => do
      let callee ← point.callee
      if h : callee < count then some (⟨callee, h⟩ : Fin count) else none
  let mut bases := seedBases
  let mut known : Array (BitVec registers) := Array.replicate count 0
  -- Lean.SCC emits callees before callers. A recursive component uses one frozen
  -- preference layout; the final save analysis independently consumes the completed plans.
  for members in Lean.SCC.scc (List.finRange count) successors do
    let summarize bases := members.foldl (fun mask i =>
      mask ||| functionClobber program demand bases known i) 0
    let frozen := bases
    let hint := summarize frozen
    let masks := members.foldl (fun masks i => masks.set! i.val hint) known
    for i in members do
      bases := bases.set i (← preferredBaseFunction program demand registers frozen masks i)
    let writes := summarize bases
    for i in members do known := known.set! i.val writes
  return bases

private def acrossRegisters
    {ranges : Array (Option Range)} {registers : Nat}
    (assignment : Assignment registers ranges)
    (point : Analysis.Liveness.Point)
    (guarded : BitVec registers) : List (Fin registers) :=
  (List.finRange point.scope).filterMap fun i =>
    if point.across.getLsb i then
      let stable := point.scope - 1 - i.val
      match assignment.homes.toArray[stable]? with
      | some (some (.reg register)) =>
          if guarded.getLsb register then some register else none
      | _ => none
    else
      none

private def savedForBlock {source : Oria.Program.ClosedProgram} {registers : Nat}
    (program : Machine.Program source)
    (demand : Analysis.Demand.Info program)
    (baseFunctions : Data.IndexedVector (fun i => FunctionPlan program demand registers i))
    (known : Array (BitVec registers))
    (i : Fin (Machine.signatures program.table source).length)
    (b : Fin (program.definitionAt i).layout.length)
    (block : BlockPlan registers ((program.definitionAt i).layout.get b)) :
    Array (Array (Fin registers)) :=
  let points := block.info.points.toList
  (points.map (fun point =>
    match point.callee with
    | none => #[]
    | some _ =>
        let guarded := callMask program demand baseFunctions known point
        (acrossRegisters block.assignment point guarded).toArray)).toArray

private def finalBlock {source : Oria.Program.ClosedProgram} {registers : Nat}
    (program : Machine.Program source)
    (demand : Analysis.Demand.Info program)
    (baseFunctions : Data.IndexedVector (fun i => FunctionPlan program demand registers i))
    (known : Array (BitVec registers))
    (i : Fin (Machine.signatures program.table source).length)
    (b : Fin (program.definitionAt i).layout.length)
    (block : BlockPlan registers ((program.definitionAt i).layout.get b)) :
    BlockPlan registers ((program.definitionAt i).layout.get b) :=
  { info := block.info,
    assignment := block.assignment,
    saved := savedForBlock program demand baseFunctions known i b block }

private def finalFunction {source : Oria.Program.ClosedProgram}
    (program : Machine.Program source)
    (demand : Analysis.Demand.Info program)
    (registers : Nat)
    (baseFunctions : Data.IndexedVector (fun i => FunctionPlan program demand registers i))
    (known : Array (BitVec registers))
    (i : Fin (Machine.signatures program.table source).length) :
    FunctionPlan program demand registers i :=
  let base := baseFunctions.get i
  let blocks := Data.IndexedVector.ofFn fun b =>
    finalBlock program demand baseFunctions known i b (base.blocks.get b)
  { blocks := blocks,
    slots := base.slots,
    resultOverflow := base.resultOverflow,
    returns := base.returns,
    clobbers := (known[i.val]?).getD 0 }

public def build {source : Oria.Program.ClosedProgram}
    (registers : Nat) (program : Machine.Program source) :
    Except Diagnostic (Plan program registers) := do
  let demand := Analysis.Demand.analyze program
  let seedBases ← baseFunctions program demand registers
  let bases ← preferredBaseFunctions program demand registers seedBases
  let known := clobbers program demand bases
  let functions := Data.IndexedVector.ofFn fun i =>
    finalFunction program demand registers bases known i
  pure { demand, functions }

end Oria.RegAlloc
