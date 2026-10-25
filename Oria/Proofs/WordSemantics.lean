module

import Oria
import Oria.Proofs.BackendUtil
import Oria.Compiler.Lower.DP121.Program
import all Oria.Proofs.DP121Semantics
meta import Oria
meta import Oria.Proofs.BackendUtil
meta import Oria.Compiler.Lower.DP121.Program
meta import all Oria.Proofs.DP121Semantics

namespace Oria.Proofs.WordSemantics

open Oria Oria.Datapack Oria.Target.DP121 Oria.Target.DP121.Semantics
open Lean Lean.Elab.Command

private def points : Oria.Command.Objective := .ofToken (.ofString "points")

@[mcfunction]
private def read : Prog (Std.Scoreboard.readGrade .self) Int32 :=
  Std.Scoreboard.get .self points

@[mcfunction]
private def run : Prog (Std.Scoreboard.readGrade .self).handled Int32 := do
  try
    let n ← read.call
    return n + 1
  catch _ =>
    return -1

@[mcfunction]
private def twice : Prog (Std.Scoreboard.readGrade .self) Int32 := do
  let first ← read.call
  let second ← read.call
  return first + second

private def config : Lower.DP121.Config := {
  resourceNamespace := .ofString "oria"
  objective := .ofToken (.ofString "oria.vm")
}

private def model (outcome : Outcome) : Model :=
  { DP121Semantics.countingModel with
    Scores := Score → Int32
    Storage := StoragePath → Int32
    Trace := Nat
    invoke := fun _ _ scores storage => ⟨scores, storage, outcome, #[99]⟩ }

private def code (program : Target.DP121.Program) : Code :=
  ⟨fun {kind} ref => match kind with
    | .plain => (program.functions.findSome? fun
        | ⟨.plain, definition⟩ =>
            if definition.ref.id.render == ref.id.render then some definition.body else none
        | ⟨.macro _, _⟩ => none).getD (.plain #[.returnFail])
    | .macro _ => .macro #[]⟩

private def score (holder : String) : Except Diagnostic Score := do
  let holder ← Oria.Command.SyntaxToken.parse holder
  pure ⟨.ofToken holder, config.objective⟩

run_cmd
  let ⟨source, machine⟩ ← BackendUtil.compile #[⟨_, run.ref⟩]
  let .ok commands := Std.Manifest.commandCatalog | throwError "command catalog failed"
  let .ok target := Lower.DP121.lower config machine commands | throwError "DP121 lowering failed"
  let some entry := source.roots[0]? | throwError "entry missing"
  let index := (IR.Machine.referenceAt machine.table source entry.position).index
  unless index.val == 0 do throwError "fixture root order changed"
  let .ok out := score "#ret0" | throwError "result slot failed"
  let .ok id := ResourcePath.parse s!"__oria/m0/b{(machine.definitionAt index).entry.index.val}"
    | throwError "entry path failed"
  let ref : FunctionRef .plain := .ofId (.ofParts config.resourceNamespace id)
  for (outcome, expected) in [(Outcome.succeeded 0, (1 : Int32)), (.succeeded 23, 24), (.failed, -1)] do
    let model := model outcome
    let initial : State model := ⟨fun _ => 0, fun _ => 0, #[]⟩
    let some result := evalCommand (mode := .plain) model (code target) 2000 () initial (.function ref)
      | throwError "target evaluation exhausted fuel"
    unless result.state.scores out == expected do
      throwError "component ABI returned {result.state.scores out}, expected {expected}"
    let events : List Nat := result.state.trace.toList
    unless (events.filter (· == 99)).length == 1 do
      throwError "command was not executed exactly once"

run_cmd
  let ⟨source, machine⟩ ← BackendUtil.compile #[⟨_, twice.ref⟩]
  let .ok commands := Std.Manifest.commandCatalog | throwError "command catalog failed"
  let .ok target := Lower.DP121.lower config machine commands | throwError "DP121 lowering failed"
  let some entry := source.roots[0]? | throwError "entry missing"
  let index := (IR.Machine.referenceAt machine.table source entry.position).index
  unless index.val == 0 do throwError "fixture root order changed"
  let .ok flag := score "#ret0" | throwError "flag slot failed"
  let .ok payload := score "#ret1" | throwError "payload slot failed"
  let .ok path := ResourcePath.parse s!"__oria/m0/b{(machine.definitionAt index).entry.index.val}"
    | throwError "entry path failed"
  let ref : FunctionRef .plain := .ofId (.ofParts config.resourceNamespace path)
  for (outcome, success, value, count) in [
      (Outcome.succeeded 9, (1 : Int32), (18 : Int32), 2), (.failed, 0, 0, 1)] do
    let model := model outcome
    let initial : State model := ⟨fun _ => 0, fun _ => 0, #[]⟩
    let some result := evalCommand (mode := .plain) model (code target) 3000 () initial (.function ref)
      | throwError "target evaluation exhausted fuel"
    unless result.state.scores flag == success && result.state.scores payload == value do
      throwError "fallible composition returned ({result.state.scores flag}, {result.state.scores payload}), expected ({success}, {value})"
    let events : List Nat := result.state.trace.toList
    unless (events.filter (· == 99)).length == count do
      throwError "fallible composition executed the wrong number of commands"

end Oria.Proofs.WordSemantics
