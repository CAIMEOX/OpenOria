module

public import Oria
public import Oria.Datapack
public import Oria.Std.Compute.Number
meta import Oria
meta import Oria.Datapack
meta import Oria.Std.Compute.Number

namespace Oria.Proofs.Fixtures.CommandArguments

open Oria.Std Oria.Std.Command.Arg Oria.Datapack

private def points : Command.Objective := "argtest.points"
private def store : DataTarget := .storage "argtest:data"
private def effects := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.failure

private def number {d : NumberProvider.Domain} (n : NumberProvider.Number d) : Calculation :=
  match Calculation.ofNumber n with
  | .ok calculation => calculation
  | .error _ => .integer (.scalar (.static 0))

private def arithmetic := number ((2 + 3 : NumberProvider.I32) * 4)
private def modulo := number (NumberProvider.Number.mod (-4 : NumberProvider.F32) 3)
private def zeroPower := number (NumberProvider.Number.pow (0 : NumberProvider.F32) 0)
@[simp] private theorem arithmetic_requirements : arithmetic.requirements = Req.none := by native_decide
@[simp] private theorem modulo_requirements : modulo.requirements = Req.none := by native_decide
@[simp] private theorem zeroPower_requirements : zeroPower.requirements = Req.none := by native_decide
private def requirements := (Compute.grade .default).req ||| arithmetic.requirements |||
  modulo.requirements ||| zeroPower.requirements

@[mcfunction]
private def setup : Prog (Grade.handled Scoreboard.objectiveGrade) Unit :=
  (Scoreboard.Objectives.add points .dummy).ignore

@[mcfunction]
private def reportPower (power : Val (Option Int32)) :
    Prog (Grade.handled (Scoreboard.writeGrade (.named "#power_failed"))) Unit := do
  match power with
  | .none => (Scoreboard.set (.named "#power_failed") points 1).ignore
  | .some _ => (Scoreboard.set (.named "#power_failed") points 0).ignore

@[mcfunction]
private def providers : Prog ⟨requirements, effects⟩ Int32 := do
  let result ← Compute.run .default arithmetic
  Scoreboard.set (.named "#arithmetic") points result
  let result ← Compute.run .default modulo
  Scoreboard.set (.named "#mod") points result
  let power : Val (Option Int32) ← Prog.attempt <| Compute.run .default zeroPower
  reportPower.call power
  Data.modify store (.key "power") .set (.compute .default zeroPower)
  return 0

@[mcfunction]
private def providerEntry : Prog (Grade.handled ⟨requirements, effects⟩) Unit := providers.call.ignore

@[mcfunction]
private def dynamic (n : Val Int32) : Prog ⟨(Compute.grade .default).req, effects⟩ Int32 := do
  let result ← Compute.run .default (.integer (.scalar n))
  Scoreboard.set (.named "#dynamic") points result

@[mcfunction]
private def dynamicEntry : Prog (Grade.handled ⟨(Compute.grade .default).req, effects⟩) Unit :=
  (dynamic.call (-7)).ignore

@[mcfunction]
private def filterPlayers : Prog (Grade.handled ⟨Req.none, effects⟩) Unit := do
  let selected : Command.Selector := .allPlayers {
    tags := [.include "argtest"]
    scores := [(points, .between 1 3)] }
  Execute.forEach [.as selected] do
    Scoreboard.set .self points 9

private def exact : Vec3 := .absolute 1.0 65.25 1.0
private def centered : Vec3 := .absolute 1 65.25 1

@[mcfunction]
private def decimalEntry : Prog (Grade.handled (Teleport.grade .self exact)) Unit :=
  (Teleport.to .self exact).ignore

@[mcfunction]
private def integerEntry : Prog (Grade.handled (Teleport.grade .self centered)) Unit :=
  (Teleport.to .self centered).ignore

@[mcfunction]
private def mixed (x : Val Int32) : Prog
    ⟨Req.executor ||| Req.position ||| Req.dimension,
      Eff.world ||| Eff.scoreboardRead ||| Eff.random⟩ Unit := do
  (Teleport.to .self (.world (.absolute (x + 1)) (.absolute 66.25) (.relative (-0.5)))).ignore

@[mcfunction]
private def mixedEntry : Prog
    ⟨Req.executor ||| Req.position ||| Req.dimension,
      Eff.world ||| Eff.scoreboardRead ||| Eff.random⟩ Unit := do
  mixed.call 2

@[datapack]
public def specimen : Spec := build { ns := "argtest", registerBudget := 6 } do
  onLoad setup.ref
  onLoad providerEntry.ref
  onLoad dynamicEntry.ref
  entry "filter" filterPlayers.ref
  entry "decimal" decimalEntry.ref
  entry "integer" integerEntry.ref
  entry "mixed" mixedEntry.ref

end Oria.Proofs.Fixtures.CommandArguments
