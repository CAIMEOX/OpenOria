module

import Oria.Runtime.GC
import Oria.Meta.Collect
import Oria.Compiler
import Oria.Datapack
meta import Oria.Runtime.GC
meta import Oria.Meta.Collect
meta import Oria.Compiler
meta import Oria.Datapack

namespace Oria.Proofs.RuntimeGC

open Oria Oria.IR Lean Lean.Elab.Command

private def config : Runtime.Config :=
  ⟨"collector", "collector:persistent", "collector:runtime", "collector.vm"⟩

private def scanner : Representation.Persistent.Scanner :=
  ⟨2, ⟨.data ⟨`Node, []⟩, `Node.mk, 1, #v[.scalar, .pointer (.data ⟨`Node, []⟩)]⟩⟩

private def scannerCommands (n : Nat) : Nat :=
  let layout : Representation.Persistent.Scanner :=
    ⟨n, ⟨.data ⟨`Node, []⟩, `Node.mk, 1,
      Vector.replicate n (.pointer (.data ⟨`Node, []⟩))⟩⟩
  (Runtime.GC.generate config #[layout] #[]).definition.dependencies.commands.size

set_option maxRecDepth 8192 in
/-- Each pointer slot contributes four command occurrences throughout the supported width. -/
theorem scanner_linear : ∀ n : Fin 31, scannerCommands n.val = 32 + 4 * n.val := by
  native_decide

private def allocates {functions : List Machine.Signature} {layout : List Nat} {r n : Nat} :
    Machine.Body functions layout r n → Bool
  | .done _ => false
  | .step (.allocate _ _) _ | .step (.promote _ _) _ | .step (.refNew _ _) _ => true
  | .step _ rest => allocates rest

run_cmd do
  let .ok commands := Command.Catalog.build [] | throwError "empty catalogue failed"
  let .ok original := Oria.collect (← getEnv) #[] commands | throwError "collection failed"
  let .ok prepared := Lower.Machine.prepare original | throwError "layout preparation failed"
  let gc := Runtime.GC.generate config #[scanner] #[("collector:root", 0)]
  let .ok candidate := Oria.includeRuntime (← getEnv) original #[gc]
    | throwError "runtime inclusion failed"
  unless candidate.schemas.isEmpty && candidate.members.size > 1 do
    throwError "runtime generation added object schemas or lost recursive helpers"
  let .ok collected := candidate.checkClosure | throwError "runtime references are not closed"
  let .ok compiled := Program.compile collected | throwError "runtime compilation failed"
  let .ok machine := Lower.Machine.lowerProgram compiled.closed prepared
    | throwError "runtime Machine lowering failed"
  for i in List.finRange (Machine.signatures machine.table compiled.closed).length do
    let fn := machine.definitionAt i
    unless (List.finRange fn.layout.length).all (fun b => !allocates (fn.blocks.get b)) do
      throwError "the collector allocates managed objects"

@[datapack]
private def empty : Datapack.Spec := Datapack.build {
    ns := "empty_gc", commands := some [], registerBudget := 6 } do
  Datapack.collector "gc"

#guard empty.artifact.files.size > 2

end Oria.Proofs.RuntimeGC
