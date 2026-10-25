module
import Oria.IR.DP121.Pretty
import all Oria.IR.DP121.Syntax
meta import all Oria.IR.DP121.Pretty
public meta import Lean.Elab.Command
public meta import Oria.Datapack.Resource
public meta import Oria.Nbt.Basic
public meta import Oria.IR.DP121.Pretty
open Oria.Command (Objective ScoreOp)

namespace Oria.Proofs.DP121Pretty
open Oria Oria.Target.DP121 Lean Elab Command
private def rid : ResourceId := .ofString "oria:runtime"
private def p : StoragePath := ⟨rid, (Nbt.Path.key "root key").child (.index 1)⟩
private def holder : ScoreHolder := .ofToken (.ofString "#x")
private def objective : Objective := .ofToken (.ofString "oria.vm")
private def s : Score := ⟨holder, objective⟩
private meta def expect (a b : String) : CommandElabM Unit := unless a == b do throwError "DP121 snapshot changed:\n{a}"
run_cmd do
  let nbt : Nbt.Value .compound := .compound (.cons ⟨"a\"b"⟩ (.string "x\ny") (.cons ⟨"xs"⟩ (.list (.cons (.int 1) (.cons (.int 2) .nil))) .nil))
  expect (nbt.formatSnbt.pretty 80) "{\"a\\\"b\":\"x\\ny\",\"xs\":[1,2]}"
  expect (p.format.pretty 80) "oria:runtime \"root key\"[1]"
  let nested : Command .plain := .store .success (.score s) <| .store .result (.storageI32 p) <| .scoreboard (.get s)
  expect (nested.pretty 200) "execute store success score #x oria.vm run execute store result storage oria:runtime \"root key\"[1] int 1 run scoreboard players get #x oria.vm"
  let helper : Command .plain :=
    .returnRun (.function (FunctionRef.ofId (.ofParts (.ofString "oria") (.ofString "helper"))))
  expect (helper.pretty 80) "return run function oria:helper"
  let schema := MacroSchema.ofFields [{ ty := .i32, codec := .i32 }]
  let macroRef : FunctionRef (.macro schema) :=
    FunctionRef.ofId (.ofParts (.ofString "oria") (.ofString "macro_helper"))
  let source : MacroSource schema := ⟨rid, some (Nbt.Path.key "macro")⟩
  let macroCall : Command .plain := .functionWithStorage macroRef source
  expect (macroCall.pretty 80)
    "function oria:macro_helper with storage oria:runtime \"macro\""
  let parameter : Piece (.macro schema) := .parameter ⟨0, by simp [schema]⟩
  expect ((piece parameter).pretty 80) "$(p0)"
  let objectiveAdd : Command .plain := .scoreboard (.objectiveAdd objective)
  expect (objectiveAdd.pretty 80) "scoreboard objectives add oria.vm dummy"
end Oria.Proofs.DP121Pretty
