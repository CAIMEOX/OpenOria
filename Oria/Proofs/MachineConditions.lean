module

import Oria
import Oria.Proofs.BackendUtil
import Oria.Proofs.Fixtures.RecursionRuntime
import Oria.Compiler.Analysis.Bits
import Oria.Compiler.Analysis.Demand
import Oria.IR.Machine.Pretty
meta import Oria
meta import Oria.Proofs.BackendUtil
meta import Oria.Proofs.Fixtures.RecursionRuntime
meta import Oria.Compiler.Analysis.Bits
meta import Oria.Compiler.Analysis.Demand
meta import Oria.IR.Machine.Pretty

namespace Oria.Proofs.MachineConditions

open Oria Oria.IR Lean Lean.Elab.Command

@[mcfunction]
private def branch (x y : Val Int32) : Prog .pure Int32 := do
  if x < y then return 7 else return 9

@[mcfunction]
private def observed (x y : Val Int32) : Prog .pure Bool := do
  let c ← Prog.pure (x < y)
  if c then return c else return Bool.lit false

@[mcfunction]
private def unknown (x : Val Int32) : Prog .pure Int32 := return x

@[mcfunction]
private def bit : Val Int32 → Prog .pure Bool :=
  Prog.fix fun again n => do
    if n <= 0 then return Bool.lit true
    else again (n - 1)

@[mcfunction]
private def read : Prog (Oria.Std.Scoreboard.readGrade (.named "#input")) Int32 :=
  Oria.Std.Scoreboard.get (.named "#input") "conditions.oria"

@[mcfunction]
private def successful : Prog (Oria.Std.Scoreboard.readGrade (.named "#input")).handled Bool :=
  read.call.isSuccess

run_cmd do
  let ⟨source, p⟩ ← BackendUtil.compile
    #[⟨_, branch.ref⟩, ⟨_, observed.ref⟩, ⟨_, unknown.ref⟩, ⟨_, bit.ref⟩, ⟨_, successful.ref⟩,
      ⟨_, Fixtures.RecursionRuntime.acrossCall.ref⟩]
  let bits := Analysis.Bits.analyze p
  let demand := Analysis.Demand.analyze p
  let locate (name : Name) : CommandElabM (Fin (Machine.signatures p.table source).length) := do
    let some i := source.position? name | throwError "missing fixture {name}"
    return (Machine.referenceAt p.table source i).index
  let i ← locate ``branch
  let d := p.definitionAt i
  match (d.block d.entry).exit.2 with
  | .branch (.compare .lt _ _) _ _ => pure ()
  | _ => throwError "comparison was not fused:\n{d.pretty 100}"
  unless (Analysis.Demand.blockInfo p demand i d.entry.index).outputs.isEmpty do
    throwError "condition-only comparison is still materialized"
  let i ← locate ``Fixtures.RecursionRuntime.acrossCall
  let d := p.definitionAt i
  match (d.block d.entry).exit.2 with
  | .branch (.compare .lt _ _) _ _ => pure ()
  | _ => throwError "comparison operands did not remain available across a call"
  unless (Analysis.Demand.blockInfo p demand i d.entry.index).outputs == #[1] do
    throwError "cross-call predicate retained an intermediate Boolean or lost the call result"
  let i ← locate ``observed
  let d := p.definitionAt i
  unless (Analysis.Demand.blockInfo p demand i d.entry.index).outputs == #[1] do
    throwError "observed comparison has lost its value"
  for name in [``observed, ``bit, ``successful, ``read] do
    let i ← locate name
    let used := (Analysis.Demand.functionInfo p demand i).result
    unless ((Analysis.Bits.functionInfo p bits i).result &&& used).toNat == 1 do
      throwError "bit return summary differs for {name}"
  let i ← locate ``unknown
  unless (Analysis.Bits.functionInfo p bits i).result.toNat == 0 do
    throwError "arbitrary I32 was classified as a bit"
  for i in List.finRange (Machine.signatures p.table source).length do
    unless Analysis.Bits.parameters p bits i (p.definitionAt i).entry.index == 0 do
      throwError "function parameters were narrowed without evidence"
  let i ← locate ``successful
  let d := p.definitionAt i
  match (d.block d.entry).exit.2 with
  | .ret values =>
      unless values.toArray.any (fun | .var _ => true | _ => false) do
        throwError "call success did not retain its computed bit"
  | _ => throwError "call success was not returned directly"

end Oria.Proofs.MachineConditions
