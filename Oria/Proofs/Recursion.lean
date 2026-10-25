module

import Oria.Proofs.Fixtures.RecursionRuntime
import Oria.Proofs.BackendUtil
import Oria.Compiler.RegAlloc
meta import Oria.Proofs.Fixtures.RecursionRuntime
meta import Oria.Proofs.BackendUtil
meta import Oria.Compiler.RegAlloc

namespace Oria.Proofs.Recursion

open Oria Oria.IR Oria.Proofs.Fixtures.RecursionRuntime Lean Lean.Elab.Command

@[mcfunction]
def keep {r : Region} : Val Int32 r → Prog .pure Int32 r :=
  Prog.fix fun _ value => Prog.pure value

example (value : Val Int32 .persistent) : Prog .pure Int32 .persistent := keep.call value

private meta def member (source : Program.ClosedProgram) (table : Representation.Table) (name : Lean.Name) :
    CommandElabM (Fin (Machine.signatures table source).length) := do
  let some position := source.position? name | throwError "missing recursive member {name}"
  pure (Machine.referenceAt table source position).index

private def selfCalls {functions : List Machine.Signature} {layout : List Nat} {r n : Nat}
    (self : Fin functions.length) : Machine.Body functions layout r n → Nat
  | .done _ => 0
  | .step (.call ref _) next => (if ref.index == self then 1 else 0) + selfCalls self next
  | .step _ next => selfCalls self next

private def backedge {functions : List Machine.Signature} {layout : List Nat} {r n : Nat}
    (entry : Fin layout.length) : Machine.Body functions layout r n → Bool
  | .done (.jump edge) => edge.target.index == entry
  | .done _ => false
  | .step _ next => backedge entry next

run_cmd do
  let ⟨source, machine⟩ ← BackendUtil.compile #[⟨_, fib.ref⟩]
  unless source.members.size == 2 do throwError "fix did not produce one shared recursive helper"
  let index ← member source machine.table (Lean.Name.num ``fib 0)
  let fn := machine.definitionAt index
  let calls := (List.finRange fn.layout.length).foldl
    (fun n b => n + selfCalls index (fn.blocks.get b)) 0
  unless calls == 2 do throwError "non-tail recursive calls were changed"
  let .ok plan := RegAlloc.build 0 machine | throwError "recursive spill allocation failed"
  unless (plan.functions.get index).slots > 0 do throwError "recursive values have no spill slots"

run_cmd do
  let ⟨source, machine⟩ ← BackendUtil.compile #[⟨_, countdown.ref⟩]
  let index ← member source machine.table (Lean.Name.num ``countdown 0)
  let fn := machine.definitionAt index
  unless (List.finRange fn.layout.length).all (fun b => selfCalls index (fn.blocks.get b) == 0) do
    throwError "self tail recursion still creates calls"
  unless (List.finRange fn.layout.length).any (fun b => backedge fn.entry.index (fn.blocks.get b)) do
    throwError "self tail recursion has no entry backedge"

end Oria.Proofs.Recursion
