module

import Oria.Compiler.Lower.DP121.Resources
import Oria.Proofs.BackendUtil
import Oria.Examples.Calls
meta import Oria.Compiler.Lower.DP121.Resources
meta import Oria.Proofs.BackendUtil
meta import Oria.Examples.Calls

namespace Oria.Proofs.CallAllocation

open Oria
open Lean Lean.Elab Command
open Oria.Proofs.BackendUtil

private def usesStack {s : Oria.Program.ClosedProgram} {p : IR.Machine.Program s} {k : Nat}
    (plan : RegAlloc.Plan p k) : Bool :=
  (Lower.DP121.Resources.analyze p plan).any (·.stack)

@[mcfunction]
private def increment (value : Val Int32) : Prog .pure Int32 :=
  Prog.pure (value + 1)

@[mcfunction]
private def wide (value : Val Int32) : Prog .pure Int32 :=
  Prog.bind (Prog.pure (value + 1)) fun x =>
    Prog.bind (Prog.pure (value + 2)) fun y => Prog.pure (x + y)

@[mcfunction]
private def inputOnly (value : Val Int32) : Prog .pure Int32 :=
  Prog.bind (increment.call value) fun _ => Prog.pure value

@[mcfunction]
private def acrossCall (value : Val Int32) : Prog .pure Int32 :=
  Prog.bind (Prog.pure (value + 5)) fun old =>
    Prog.bind (Prog.pure (value + 1)) fun arg =>
      Prog.bind (wide.call arg) fun y => Prog.pure (old + y)

private meta def memberIndex
    (source : Oria.Program.ClosedProgram) (table : Representation.Table) (name : Lean.Name) :
    CommandElabM (Fin (IR.Machine.signatures table source).length) := do
  let some position := source.position? name
    | throwError "missing machine member `{name}`"
  pure (IR.Machine.referenceAt table source position).index

run_cmd
  let ⟨source, machine⟩ ← BackendUtil.compile #[⟨_, inputOnly.ref⟩]
  let .ok plan := RegAlloc.build 1 machine
    | throwError "input-only call allocation failed"
  let index ← memberIndex source machine.table ``inputOnly
  let defn := machine.definitionAt index
  let block := (plan.functions.get index).blocks.get defn.entry.index
  unless block.saved.all (fun saves => saves.isEmpty) do
    throwError "input-only call unexpectedly saved an across value"
  unless usesStack plan == false do
    throwError "input-only scalar call allocated a stack frame"

run_cmd
  let ⟨source, machine⟩ ← BackendUtil.compile #[⟨_, acrossCall.ref⟩]
  let .ok plan := RegAlloc.build 2 machine
    | throwError "across-call allocation failed"
  let index ← memberIndex source machine.table ``acrossCall
  let defn := machine.definitionAt index
  let block := (plan.functions.get index).blocks.get defn.entry.index
  unless block.saved.size == 4 do
    throwError s!"saved facts are not aligned with four instructions: {block.saved.size}"
  unless block.saved[0]? == some #[] && block.saved[1]? == some #[] do
    throwError "non-call instruction before call unexpectedly saved a value"
  unless block.saved[2]?.any (fun saves => !saves.isEmpty) do
    throwError "live value across call was not saved at the call point"
  unless block.saved[3]? == some #[] do
    throwError "non-call instruction after call unexpectedly saved a value"

run_cmd
  let ⟨_, machine⟩ ← BackendUtil.compile #[⟨_, Examples.Calls.chain3.ref⟩]
  let .ok plan := RegAlloc.build 122 machine | throwError "call-chain allocation failed"
  unless usesStack plan == false do
    throwError "the four-function chain should retain its values in registers"

run_cmd
  let ⟨source, machine⟩ ← BackendUtil.compile #[⟨_, Examples.Calls.chain7.ref⟩]
  unless source.members.size == 8 do throwError "the long chain has eight named functions"
  let .ok plan := RegAlloc.build 122 machine | throwError "long-chain allocation failed"
  unless usesStack plan == false do throwError "the long chain should use register-only calls"
  let .ok limited := RegAlloc.build 2 machine | throwError "limited chain allocation failed"
  unless usesStack limited do throwError "the limited chain needs call-preserved storage"

run_cmd
  let ⟨source, machine⟩ ← BackendUtil.compile
    #[⟨_, Examples.Calls.tree.ref⟩, ⟨_, Examples.Calls.choose.ref⟩]
  unless source.members.size == 7 do throwError "the tree shares its named callees"
  let .ok plan := RegAlloc.build 122 machine | throwError "branching-call allocation failed"
  unless usesStack plan == false do throwError "branching calls should retain their values in registers"

run_cmd
  let ⟨_, machine⟩ ← BackendUtil.compile #[⟨_, Examples.Calls.sum24.ref⟩]
  let .ok plan := RegAlloc.build 122 machine | throwError "wide-parameter allocation failed"
  unless usesStack plan == false do throwError "the wide parameter list fits the ordinary register budget"
  let .ok limited := RegAlloc.build 2 machine | throwError "wide stack-parameter allocation failed"
  unless usesStack limited do throwError "the limited register budget requires stack parameters"

run_cmd
  let ⟨_, machine⟩ ← BackendUtil.compile #[⟨_, Examples.Calls.locals.ref⟩]
  let .ok plan := RegAlloc.build 122 machine | throwError "retained-local allocation failed"
  unless usesStack plan == false do throwError "the retained locals and wide call fit the ordinary register budget"
  for budget in [2, 0] do
    let .ok limited := RegAlloc.build budget machine | throwError "retained-local spill allocation failed"
    unless usesStack limited do throwError "the retained locals require stack locations at budget {budget}"

end Oria.Proofs.CallAllocation
