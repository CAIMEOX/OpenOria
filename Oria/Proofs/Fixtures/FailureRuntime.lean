module

public import Oria
public import Oria.Datapack
meta import Oria
meta import Oria.Datapack

namespace Oria.Proofs.Fixtures.FailureRuntime

open Oria Oria.Std Oria.Persistent

private def objective : Command.Objective := "failure.results"

@[mcfunction]
private def leaf (n : Val Int32) : Prog .failure Int32 := do
  if n < 0 then Prog.fail
  return n

@[mcfunction]
private def middle (n : Val Int32) : Prog .failure Int32 := do
  let old ← Prog.pure (n * 7)
  let value ← leaf.call (n - 10)
  return old + value

@[mcfunction]
private def shortCircuit := show Prog _ Unit from do
  Scoreboard.set (.named "#before") objective 1
  Scoreboard.get (.named "#missing") objective
  Scoreboard.set (.named "#skipped") objective 1

@[mcfunction]
private def unhandled := show Prog _ Unit from do
  shortCircuit.call

@[mcfunction]
private def run := show Prog _ Unit from do
  (Scoreboard.set (.named "#skipped") objective 0).ignore
  shortCircuit.call.ignore
  (Scoreboard.set (.named "#continued") objective 1).ignore
  let zero ← (Scoreboard.get (.named "#zero") objective).getD (-1)
  (Scoreboard.set (.named "#zero_result") objective zero).ignore
  let absent ← (Scoreboard.get (.named "#missing") objective).getD 42
  (Scoreboard.set (.named "#default") objective absent).ignore
  let captured ← Prog.attempt (leaf.call (-1))
  match captured with
  | .none => (Scoreboard.set (.named "#captured") objective 1).ignore
  | .some _ => (Scoreboard.set (.named "#captured") objective 0).ignore
  let x ← Scoreboard.get (.named "#input") objective
  try
    let n ← middle.call x
    (Scoreboard.set (.named "#nested") objective n).ignore
  catch _ =>
    (Scoreboard.set (.named "#nested") objective (x * 11)).ignore
  try
    (show Prog _ Int32 from do
      try
        leaf.call (-1)
      catch _ =>
        (Scoreboard.set (.named "#fallback") objective 1).ignore
        Prog.fail)
  catch _ =>
    (Scoreboard.set (.named "#outer") objective 1).ignore
  (Scoreboard.set (.named "#finished") objective 1).ignore

@[mcfunction]
private def prepare := (Scoreboard.Objectives.add objective .dummy).ignore

@[mcfunction]
private def interruptedHook := show Prog _ Unit from do
  leaf.call (-1)
  Scoreboard.set (.named "#hook_skipped") objective 1

@[mcfunction]
private def followingHook := (Scoreboard.set (.named "#hook_after") objective 1).ignore

@[root]
private def seed : Root Int32 := Root.init do
  let n ← leaf.call 3
  persist n

@[root]
private def unavailable : Root Int32 :=
  Root.init (Prog.fail (A := Int32) (r := .persistent))

@[datapack]
public def unready : Datapack.Spec := Datapack.build {ns := "failure_unready", registerBudget := 6} do
  Datapack.root "failure_unready:seed" unavailable
  Datapack.entry "run" unhandled.ref

private def entries (id : ResourceId) : Datapack.Builder Unit := do
  Datapack.onLoad prepare.ref
  Datapack.onLoad interruptedHook.ref
  Datapack.onLoad followingHook.ref
  Datapack.root id seed
  Datapack.entry "run" run.ref
  Datapack.entry "unhandled" unhandled.ref

@[datapack]
public def specimen : Datapack.Spec := Datapack.build {ns := "failure_test", registerBudget := 128} (entries "failure_test:seed")

@[datapack]
public def allStack : Datapack.Spec := Datapack.build {ns := "failure_zero", registerBudget := 6} (entries "failure_zero:seed")

end Oria.Proofs.Fixtures.FailureRuntime
