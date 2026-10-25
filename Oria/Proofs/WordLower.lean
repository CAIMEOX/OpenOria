module

import Oria
import Oria.Proofs.BackendUtil
import Oria.Compiler.Analysis.Demand
import Oria.Compiler.Lower.DP121.Program
import Oria.IR.DP121.Pretty
meta import Oria
meta import Oria.Proofs.BackendUtil
meta import Oria.Compiler.Analysis.Demand
meta import Oria.Compiler.Lower.DP121.Program
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.WordLower

open Oria Lean Lean.Elab.Command

private def points : Oria.Command.Objective := .ofToken (.ofString "points")

@[mcfunction]
private def native (value : Val Int32) : Prog (Std.Scoreboard.writeGrade .self) Int32 :=
  Std.Scoreboard.set .self points (.dynamic value)

@[mcfunction]
private def ignored (value : Val Int32) : Prog (Grade.handled (Std.Scoreboard.writeGrade .self)) Unit :=
  (native.call value).ignore

@[mcfunction]
private def succeeded (value : Val Int32) :
    Prog (Std.Scoreboard.writeGrade .self).handled Bool :=
  (native.call value).isSuccess

@[mcfunction]
private def observed (value : Val Int32) :
    Prog (Std.Scoreboard.writeGrade .self).handled Int32 :=
  ((native.call value).map (· + 1)).getD (-1)

private def config : Lower.DP121.Config := {
  resourceNamespace := .ofString "oria"
  objective := .ofToken (.ofString "oria.vm")
}

private def capture0 : String := include_str "../../tests/golden/word-capture-0.dp121"
private def capture1 : String := include_str "../../tests/golden/word-capture-1.dp121"
private def capture3 : String := include_str "../../tests/golden/word-capture-3.dp121"

run_cmd
  for (entry, expected) in [
      (⟨_, ignored.ref⟩, 0),
      (⟨_, succeeded.ref⟩, 1),
      (⟨_, observed.ref⟩, 3)] do
    let ⟨source, program⟩ ← BackendUtil.compile #[entry]
    let info := Analysis.Demand.analyze program
    let name := ``native
    let some position := source.members.findFinIdx? (fun member => member.source == name)
      | throwError "command callee was not collected"
    let index := (IR.Machine.referenceAt program.table source position).index
    let demand := Analysis.Demand.functionInfo program info index
    unless demand.result.toNat == expected do
      throwError "callee result mask: expected {expected}, got {demand.result.toNat}"
    let definition := program.definitionAt index
    let block := Analysis.Demand.blockInfo program info index definition.entry.index
    unless block.outputs == #[expected] do
      throwError "command result components were not pruned independently: {block.outputs}"
    let .ok commands := Std.Manifest.commandCatalog | throwError "command catalog failed"
    let .ok target := Lower.DP121.lower config program commands
      | throwError "word program did not lower to DP121"
    let path := s!"oria:__oria/m{index.val}/b{definition.entry.index.val}"
    let some rendered := target.functions.findSome? (fun ⟨_, function⟩ =>
        if function.ref.id.render == path then some (function.body.pretty 120) else none)
      | throwError "command function was not emitted"
    let golden := if expected == 0 then capture0 else if expected == 1 then capture1 else capture3
    unless rendered ++ "\n" == golden do throwError "capture code changed:\n{rendered}"

example : Analysis.Machine.uses #v[IR.Machine.Atom.var (n := 2) 0, .var 1] (2 : BitVec 2) = 2 := by
  native_decide

end Oria.Proofs.WordLower
