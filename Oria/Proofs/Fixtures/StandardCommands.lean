module

public import Oria
public import Oria.Datapack
meta import Oria
meta import Oria.Datapack

namespace Oria.Proofs.Fixtures.StandardCommands

open Oria.Std Oria.Std.Command.Arg Oria.Datapack

private def points : Command.Objective := "stdtest.oria"
private def sequence : ResourceId := "stdtest:sequence"
private def minHolder := ScoreHolder.named "#min"
private def maxHolder := ScoreHolder.named "#max"
private def outHolder := ScoreHolder.named "#out"
private def seedHolder := ScoreHolder.named "#seed"
private def chatHolder := ScoreHolder.named "#chat"
private def sampleGrade :=
  (Scoreboard.readGrade minHolder).seq
    ((Random.grade (some sequence)).seq (Scoreboard.writeGrade outHolder))
private def chatGrade :=
  (Tellraw.grade Players.all).seq (Scoreboard.writeGrade chatHolder)

@[mcfunction]
private def draw (lo hi : Val Int32) : Prog (Random.grade (some sequence)) Int32 :=
  Random.value (.between (.dynamic lo) (.dynamic hi)) (some sequence)

@[mcfunction]
private def sample : Prog sampleGrade Int32 := do
  let lo ← Scoreboard.get minHolder points
  let hi ← Scoreboard.get maxHolder points
  let n ← draw.call lo hi
  Scoreboard.set outHolder points (.dynamic n)
  return n

@[mcfunction]
private def sampleEntry : Prog (Grade.handled sampleGrade) Unit := sample.call.ignore

@[mcfunction]
private def seed : Prog ((Scoreboard.readGrade seedHolder).seq (Random.resetGrade (.one sequence))) Int32 := do
  let n ← Scoreboard.get seedHolder points
  Random.reset (.one sequence)
    (some {value := .dynamic n, includeWorldSeed := false, includeSequenceId := false})

@[mcfunction]
private def seedEntry : Prog (Grade.handled ((Scoreboard.readGrade seedHolder).seq (Random.resetGrade (.one sequence)))) Unit := seed.call.ignore

@[mcfunction]
private def resetDefaults : Prog (Grade.handled (Random.resetGrade .all)) Unit :=
  (Random.reset .all (some {value := .static 71, includeWorldSeed := false, includeSequenceId := false})).ignore

@[mcfunction]
private def resetOne : Prog (Grade.handled (Random.resetGrade (.one sequence))) Unit := (Random.reset (.one sequence)).ignore

@[mcfunction]
private def clearSequences : Prog (Grade.handled (Random.resetGrade .all)) Unit := (Random.reset .all).ignore

@[mcfunction]
private def roll : Prog ((Random.rollGrade none).seq
    ((Scoreboard.writeGrade (ScoreHolder.named "#roll")).seq Grade.pure)) Int32 := do
  let n ← Random.roll (.between (.static 1) (.static 6))
  Scoreboard.set (.named "#roll") points (.dynamic n)
  return n

@[mcfunction]
private def rollEntry : Prog (Grade.handled ((Random.rollGrade none).seq
    ((Scoreboard.writeGrade (ScoreHolder.named "#roll")).seq Grade.pure))) Unit := roll.call.ignore

@[mcfunction]
private def failStop : Prog ((Random.grade none).seq
    (Scoreboard.writeGrade (ScoreHolder.named "#continued"))) Int32 := do
  Random.value (.exact (.static 1))
  Scoreboard.set (.named "#continued") points (.static 1)

@[mcfunction]
private def failStopEntry : Prog (Grade.handled ((Random.grade none).seq
    (Scoreboard.writeGrade (ScoreHolder.named "#continued")))) Unit := failStop.call.ignore

@[mcfunction]
private def failDiscard : Prog (Grade.handled ((Random.grade none).seq
    (Scoreboard.writeGrade (ScoreHolder.named "#continued")))) Unit := do
  (Random.value (.exact (.static 1))).ignore
  (Scoreboard.set (.named "#continued") points (.static 2)).ignore

@[mcfunction]
private def chatStatus : Prog (Tellraw.grade Players.all).handled Int32 := do
  let result ← Prog.attempt (Tellraw.text .all "Plain \"text\" $(literal)")
  match result with
  | .none => return -1
  | .some n => return n

@[mcfunction]
private def chatEntry : Prog (Grade.handled chatGrade) Unit := do
  let n ← chatStatus.call
  (Scoreboard.set (.named "#chat") points (.dynamic n)).ignore

@[mcfunction]
private def number (n : Val Int32) : Prog (Grade.handled (Tellraw.grade Players.all)) Unit :=
  (Tellraw.number .all (.dynamic n)).ignore

@[mcfunction]
private def numberEntry : Prog ((Scoreboard.readGrade outHolder).seq (Tellraw.grade Players.all)) Int32 := do
  let n ← Scoreboard.get (.named "#out") points
  number.call n
  return n

@[mcfunction]
private def numberPublic : Prog (Grade.handled ((Scoreboard.readGrade outHolder).seq (Tellraw.grade Players.all))) Unit := numberEntry.call.ignore

private def hookGrade :=
  (Tellraw.grade Players.all).seq (Scoreboard.writeGrade (.named "#hook"))

@[mcfunction]
private def loaded : Prog (Grade.handled (hookGrade.seq (Dialog.grade Players.all))) Unit := do
  (Tellraw.text .all "Standard commands loaded").ignore
  (Dialog.notice .all "Loaded" "Standard command acceptance").ignore
  (Scoreboard.set (.named "#loaded") points (.static 1)).ignore

@[mcfunction]
private def ticked : Prog (Grade.handled hookGrade) Unit := do
  number.call 12
  (Scoreboard.set (.named "#ticked") points (.static 1)).ignore

private def richPlayers : Players := Players.ofString "@a[name=\"round one\"]"
private def richHolder : ScoreHolder := ScoreHolder.named "#rich"
private def richGrade : Grade :=
  (Tellraw.grade Players.all Req.all).seq (Scoreboard.writeGrade richHolder)

@[mcfunction]
private def rich : Prog (Grade.handled richGrade) Unit := do
    (Tellraw.send .all (nbt% [
      {text: "Styled", color: "gold", bold: true, italic: false,
        click_event: {action: "copy_to_clipboard", value: "copied $(literal)"},
        hover_event: {action: "show_text", value: {text: "Details", color: "gray"}}},
      {translate: "chat.type.text", "with": ["Server", "Message"]},
      {score: {name: "#out", objective: "stdtest.oria"}},
      {selector: "@a"},
      {nbt: "message", storage: "stdtest:messages", interpret: true}
    ])).ignore
    (Tellraw.translate .all "demo.key" [Nbt.ToNbt.toNbt (3 : Int32)] (some "value %s")).ignore
    (Tellraw.score .all "#out" points).ignore
    (Tellraw.selector .all "@a").ignore
    (Tellraw.fromStorage .all "stdtest:messages" (.key "message") true).ignore
    (Tellraw.fromEntity .all "@s" (.key "CustomName")).ignore
    (Tellraw.fromBlock .all "~ ~ ~" (.key "CustomName")).ignore
    (Tellraw.text richPlayers "Selected").ignore
    (Scoreboard.set richHolder points (.static 1)).ignore

@[mcfunction]
private def dialog (n : Val Int32) : Prog (Grade.handled (Dialog.grade Players.all Req.all)) Unit := do
  (Dialog.show .all <| .inline <| .nbtCompound [
    (⟨"type"⟩, .nbt (.string "minecraft:notice")),
    (⟨"title"⟩, .nbt (.string "Round")),
    (⟨"body"⟩, .nbtCompound [
      (⟨"type"⟩, .nbt (.string "minecraft:plain_message")),
      (⟨"contents"⟩, .nbtCompound [
        (⟨"translate"⟩, .nbt (.string "%s")),
        (⟨"with"⟩, .nbtList [.hole .i32 n])])])]).ignore

private def dialogWriteGrade :=
  Scoreboard.writeGrade (ScoreHolder.named "#dialog")

private def confirmationContent : DialogContent := .ofNbt (nbt% {
  type: "minecraft:confirmation", title: "Continue?",
  yes: {label: "Yes"}, no: {label: "No"}
})

private def settingsContent : DialogContent := .ofNbt (nbt% {
  type: "minecraft:multi_action", title: "Settings",
  inputs: [{type: "minecraft:text", key: "name", label: "Name"}],
  actions: [{label: "Done"}], columns: 1
})

private def dialogGrade :=
  (Dialog.grade Players.all Req.all).seq dialogWriteGrade

@[mcfunction]
private def dialogEntry : Prog (Grade.handled dialogGrade) Unit := do
  (Dialog.show .all (.named "minecraft:server_links")).ignore
  (Dialog.show .all confirmationContent).ignore
  (Dialog.show .all settingsContent).ignore
  dialog.call 12
  (Dialog.clear .all).ignore
  let result ← Prog.attempt (Dialog.notice .all "Notice" "Hello $(literal)")
  Oria.Option.elim result
    ((Scoreboard.set (.named "#dialog") points (.static (-1))).ignore)
    (fun n => (Scoreboard.set (.named "#dialog") points (.dynamic n)).ignore)

@[datapack]
public def specimen : Spec := build {
    ns := "stdtest"
    description := "Standard command acceptance"
    registerBudget := 6
  } do
    onLoad loaded.ref
    onTick ticked.ref
    entry "sample" sampleEntry.ref
    entry "seed" seedEntry.ref
    entry "defaults" resetDefaults.ref
    entry "reset" resetOne.ref
    entry "clear" clearSequences.ref
    entry "roll" rollEntry.ref
    entry "stop" failStopEntry.ref
    entry "discard" failDiscard.ref
    entry "chat" chatEntry.ref
    entry "number" numberPublic.ref
    entry "rich" rich.ref
    entry "dialog" dialogEntry.ref

end Oria.Proofs.Fixtures.StandardCommands
