module

public import Oria
public import Oria.Datapack
meta import Oria
meta import Oria.Datapack

namespace Oria.Proofs.Fixtures.EntityCommands

open Oria.Std Oria.Std.Command.Arg Oria.Datapack

private def points : Command.Objective := "entitytest.points"
private def writeGrade := Scoreboard.writeGrade (.named "#status")
private def origin : Vec3 := .world (.relative (.static 0))
  (.relative (.static 0)) (.relative (.static 0))
private def targets : Target := .selector (.allEntities { tags := [.include "entitytest.effects"] })
private def temporary : Target := .selector (.allEntities { tags := [.include "entitytest.temporary"] })

private def report (result : Val (Option Int32)) : Prog (Grade.handled writeGrade) Unit := do
  match result with
  | .none =>
      (Scoreboard.set (.named "#status") points (.static 0)).ignore
      (Scoreboard.set (.named "#result") points (.static (-999))).ignore
  | .some n =>
      (Scoreboard.set (.named "#status") points (.static 1)).ignore
      (Scoreboard.set (.named "#result") points (.dynamic n)).ignore

private def capture {g : Grade} (action : Prog g Int32) :
    Prog (Grade.handled (g.seq writeGrade)) Unit := do
  let result : Val (Option Int32) ← Prog.attempt <| action
  report result

@[mcfunction]
private def setup : Prog (Grade.handled Scoreboard.objectiveGrade) Unit :=
  (Scoreboard.Objectives.add points .dummy).ignore

@[mcfunction]
private def here : Prog (Grade.handled Summon.grade) Unit := do capture (Summon.here "minecraft:marker")

@[mcfunction]
private def atPosition : Prog (Grade.handled (Summon.grade (some origin))) Unit := do
  capture (Summon.at "minecraft:pig" origin)

@[mcfunction]
private def explicitEmpty : Prog (Grade.handled (Summon.grade (some origin))) Unit := do
  capture (Summon.at "minecraft:pig" origin (some (.value (nbt% {}))))

@[mcfunction]
private def dynamic (x age : Val Int32) : Prog (Grade.handled (Summon.grade (some origin))) Unit := do
  let data : Compound := .fields [
    (⟨"Age"⟩, .hole .i32 age), (⟨"Tags"⟩, .nbt (nbt% ["entitytest.dynamic"]))]
  let position := Vec3.world (.relative (.dynamic x))
    (.relative (.decimal 0.25)) (.relative (.decimal (-0.5)))
  let result : Val (Option Int32) ← Prog.attempt <| Summon.at "minecraft:pig" position (some data)
  report result

@[mcfunction]
private def dynamicEntry : Prog (Grade.handled (Summon.grade (some origin))) Unit := do
  let x : Val (Option Int32) ← Prog.attempt <| Scoreboard.get (.named "#x") points
  let age : Val (Option Int32) ← Prog.attempt <| Scoreboard.get (.named "#age") points
  match x, age with
  | .some x, .some age => dynamic.call x age
  | .none, _ => report x
  | _, .none => report age

@[mcfunction]
private def snapshot : Prog (Grade.handled (Summon.grade (some origin))) Unit := do
  let data ← Nbt.literal (nbt% {
    Tags: ["entitytest.snapshot"], Age: -900,
    Passengers: [{id: "minecraft:marker", Tags: ["entitytest.passenger"]}]
  })
  let result : Val (Option Int32) ← Prog.attempt <| Summon.at "minecraft:pig" origin (some (.dynamic data))
  report result

@[mcfunction]
private def fixedUuid : Prog (Grade.handled (Summon.grade (some origin))) Unit := do
  capture (Summon.at "minecraft:marker" origin (some (.value (nbt% {
    UUID: [I; 1329744193, 1548427776, -2147479999, 1], Tags: ["entitytest.uuid"]
  }))))

@[mcfunction]
private def prepareEffects : Prog (Grade.handled (Summon.grade (some origin))) Unit := do
  (Summon.at "minecraft:pig" origin
    (some (.value (nbt% {Tags: ["entitytest.effects"], NoAI: true})))).ignore
  (Summon.at "minecraft:pig" origin
    (some (.value (nbt% {Tags: ["entitytest.effects"], NoAI: true})))).ignore
  (Summon.at "minecraft:marker" origin
    (some (.value (nbt% {Tags: ["entitytest.effects"]})))).ignore

@[mcfunction]
private def give : Prog (Grade.handled (Effect.grade targets)) Unit := do
  capture (Effect.give targets "minecraft:speed")

@[mcfunction]
private def giveInfinite : Prog (Grade.handled (Effect.grade targets)) Unit := do
  capture (Effect.giveFor targets "minecraft:night_vision" .infinite)

@[mcfunction]
private def giveInstant : Prog (Grade.handled (Effect.grade targets)) Unit := do
  capture (Effect.give targets "minecraft:instant_health")

@[mcfunction]
private def giveInstantFor : Prog (Grade.handled (Effect.grade targets)) Unit := do
  capture (Effect.giveFor targets "minecraft:instant_health" (.finite (.static 5)))

@[mcfunction]
private def giveDynamic (duration amplifier : Val Int32) : Prog (Grade.handled (Effect.grade targets)) Unit := do
  capture (Effect.giveFor targets "minecraft:weakness" (.finite (.dynamic duration))
    (.dynamic amplifier) true)

@[mcfunction]
private def giveEntry : Prog (Grade.handled (Effect.grade targets)) Unit := do
  let duration : Val (Option Int32) ← Prog.attempt <| Scoreboard.get (.named "#duration") points
  let amplifier : Val (Option Int32) ← Prog.attempt <| Scoreboard.get (.named "#amplifier") points
  match duration, amplifier with
  | .some duration, .some amplifier => giveDynamic.call duration amplifier
  | .none, _ => report duration
  | _, .none => report amplifier

@[mcfunction]
private def clearOne : Prog (Grade.handled (Effect.grade targets)) Unit := do
  capture (Effect.clear targets (some "minecraft:speed"))

@[mcfunction]
private def clearAll : Prog (Grade.handled (Effect.grade targets)) Unit := do capture (Effect.clear targets)

@[mcfunction]
private def selfEffect : Prog (Grade.handled (Effect.grade .self)) Unit := do capture (Effect.give .self "minecraft:speed")

@[mcfunction]
private def prepareKill : Prog (Grade.handled (Summon.grade (some origin))) Unit := do
  (Summon.at "minecraft:marker" origin
    (some (.value (nbt% {Tags: ["entitytest.temporary"]})))).ignore
  (Summon.at "minecraft:marker" origin
    (some (.value (nbt% {Tags: ["entitytest.temporary"]})))).ignore

@[mcfunction]
private def kill : Prog (Grade.handled (Kill.grade temporary)) Unit := do capture (Kill.run temporary)

@[mcfunction]
private def killSelf : Prog (Grade.handled Kill.grade) Unit := do capture Kill.run

@[mcfunction]
private def stopOnFailure : Prog (Kill.grade temporary) Int32 := do
  Kill.run temporary
  Scoreboard.set (.named "#continued") points (.static 1)

@[mcfunction]
private def stopping : Prog (Grade.handled (Kill.grade temporary)) Unit := stopOnFailure.call.ignore

@[mcfunction]
private def continuing : Prog (Grade.handled (Kill.grade temporary)) Unit := do
  (Kill.run temporary).ignore
  (Scoreboard.set (.named "#continued") points (.static 2)).ignore

@[datapack]
public def specimen : Spec := build { ns := "entitytest", registerBudget := 6 } do
  onLoad setup.ref
  entry "here" here.ref
  entry "at" atPosition.ref
  entry "empty" explicitEmpty.ref
  entry "dynamic" dynamicEntry.ref
  entry "snapshot" snapshot.ref
  entry "uuid" fixedUuid.ref
  entry "prepare-effects" prepareEffects.ref
  entry "give" give.ref
  entry "infinite" giveInfinite.ref
  entry "instant" giveInstant.ref
  entry "instant-for" giveInstantFor.ref
  entry "give-dynamic" giveEntry.ref
  entry "clear-one" clearOne.ref
  entry "clear-all" clearAll.ref
  entry "self-effect" selfEffect.ref
  entry "prepare-kill" prepareKill.ref
  entry "kill" kill.ref
  entry "kill-self" killSelf.ref
  entry "stopping" stopping.ref
  entry "continuing" continuing.ref

end Oria.Proofs.Fixtures.EntityCommands
