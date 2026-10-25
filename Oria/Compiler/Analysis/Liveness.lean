module

public import Oria.Compiler.Analysis.Demand
public import Oria.Compiler.RegAlloc.Location

namespace Oria.Analysis.Liveness

open Oria.IR

/-- Uses precede the simultaneous definition of the result tuple. -/
public structure Point where
  scope : Nat
  results : Nat
  inputs : BitVec scope
  across : BitVec scope
  outputs : BitVec results
  callee : Option Nat := none
  forks : Bool := false

public def Point.acrossValue (point : Point) (id : Nat) : Bool :=
  if h : id < point.scope then
    point.across.getLsb ⟨point.scope - 1 - id, by omega⟩
  else false

public theorem Point.acrossValue_number (point : Point) (i : Fin point.scope) :
    point.acrossValue (Analysis.Machine.number i) = point.across.getLsb i := by
  unfold Point.acrossValue Analysis.Machine.number
  split
  · congr 1
    apply Fin.ext
    change point.scope - 1 - (point.scope - 1 - i.val) = i.val
    omega
  · omega

public structure Block (n : Nat) where
  parameters : BitVec n
  points : Array Point
  ranges : Array (Option RegAlloc.Range)

private def walk
    {functions : List IR.Machine.Signature} {layout : List Nat} {result n : Nat}
    (params : {sig : IR.Machine.Signature} → Scope.Var Unit functions sig → BitVec sig.args)
    (exit : {n : Nat} → IR.Machine.Terminator layout result n → BitVec n) :
    IR.Machine.Body functions layout result n →
      BitVec n × List Point × ((m : Nat) × BitVec m)
  | .done done => (exit done, [], ⟨n, exit done⟩)
  | .step (m := m) op next =>
      let (after, points, terminal) := walk params exit next
      let outputs := after.extractLsb' 0 m
      let across := after.extractLsb' m n
      let inputs := Analysis.Machine.inputs params op outputs
      let callee := match op with
        | .call target _ | .execute _ _ target _ => some target.index.val
        | _ => none
      let forks := match op with | .execute .. => true | _ => false
      (across ||| inputs, ⟨n, m, inputs, across, outputs, callee, forks⟩ :: points, terminal)

private def touch {n : Nat} (ranges : Array (Option RegAlloc.Range))
    (mask : BitVec n) (event : Nat) : Array (Option RegAlloc.Range) :=
  (List.finRange n).foldl (init := ranges) fun ranges i =>
    if mask.getLsb i then
      ranges.modify (Analysis.Machine.number i)
        (Option.map fun r => { r with stop := max r.stop (event + 1) })
    else ranges

/-- Freeze a block's liveness and half-open intervals after demand propagation. -/
public def scan
    {functions : List IR.Machine.Signature} {layout : List Nat} {result n : Nat}
    (params : {sig : IR.Machine.Signature} → Scope.Var Unit functions sig → BitVec sig.args)
    (exit : {n : Nat} → IR.Machine.Terminator layout result n → BitVec n)
    (body : IR.Machine.Body functions layout result n) : Block n := Id.run do
  let (parameters, points, terminal) := walk params exit body
  let mut ranges : Array (Option RegAlloc.Range) := Array.replicate terminal.1 none
  for i in List.finRange n do
    if parameters.getLsb i then
      ranges := ranges.set! (Analysis.Machine.number i) (some ⟨0, 1⟩)
  for (point, index) in points.zipIdx do
    ranges := touch ranges point.inputs (2 * index + 1)
    for i in List.finRange point.results do
      if point.outputs.getLsb i then
        ranges := ranges.set! (point.scope + point.results - 1 - i.val)
          (some ⟨2 * index + 2, 2 * index + 3⟩)
  ranges := touch ranges terminal.2 (2 * points.length + 1)
  return ⟨parameters, points.toArray, ranges⟩

public def analyzeBlock {source : Oria.Program.ClosedProgram}
    (program : IR.Machine.Program source) (demand : Demand.Info program)
    (i : Fin (IR.Machine.signatures program.table source).length)
    (b : Fin (program.definitionAt i).layout.length) :
    Block ((program.definitionAt i).layout.get b) :=
  scan (Demand.parameters program demand)
    (Demand.terminatorUses (Demand.functionInfo program demand i))
    ((program.definitionAt i).blocks.get b)

end Oria.Analysis.Liveness
