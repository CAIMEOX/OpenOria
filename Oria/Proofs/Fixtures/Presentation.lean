module

public import Oria
public import Oria.Datapack
meta import Oria
meta import Oria.Datapack

namespace Oria.Proofs.Fixtures.Presentation

open Oria.Std Oria.Std.Command.Arg Oria.Datapack

private def points : Command.Objective := "feedback.points"
private def writeGrade := Scoreboard.writeGrade (.named "#status")
private def readGrade := Scoreboard.readGrade (.named "#input")
private def everyone : Target := .selector .allPlayers
private def nobody : Players := .selector (.allPlayers {tags := [.include "feedback.absent"]})

private def report (status : Int32) (value : Val Int32) : Prog writeGrade.handled Unit := do
  (Scoreboard.set (.named "#status") points (.static status)).ignore
  (Scoreboard.set (.named "#result") points value).ignore

private def capture {g : Grade} (action : Prog g Int32) : Prog (Grade.handled (g.seq writeGrade)) Unit := by
  simpa only [Grade.handled_seq, Grade.handled_idem, Grade.seq_assoc, Grade.seq_idem] using
    Prog.catchFailure (Prog.bind action (report 1)) (report 0 (-999))

private def input {g : Grade} (action : Val Int32 → Prog g Int32) :
    Prog (Grade.handled ((readGrade.seq g).seq writeGrade)) Unit :=
  capture (g := readGrade.seq g) do
    let n ← Scoreboard.get (.named "#input") points
    action n

@[mcfunction]
private def setup : Prog (Grade.handled Scoreboard.objectiveGrade) Unit :=
  (Scoreboard.Objectives.add points .dummy).ignore

@[mcfunction]
private def loaded : Prog (Grade.handled (Title.grade .all)) Unit := (Title.show .all (.literal "Ready")).ignore

@[mcfunction]
private def tagSelf : Prog (Grade.handled ((Tag.grade .self).seq writeGrade)) Unit :=
  capture (Tag.add .self "round.active")

@[mcfunction]
private def tagAll : Prog (Grade.handled ((Tag.grade everyone).seq writeGrade)) Unit :=
  capture (Tag.add everyone "round.active")

@[mcfunction]
private def tagWinner : Prog (Grade.handled ((Tag.grade .self).seq writeGrade)) Unit :=
  capture (Tag.add .self "round.winner")

@[mcfunction]
private def untag : Prog (Grade.handled ((Tag.grade everyone).seq writeGrade)) Unit :=
  capture (Tag.remove everyone "round.active")

@[mcfunction]
private def tagList : Prog (Grade.handled ((Tag.grade everyone).seq writeGrade)) Unit := capture (Tag.list everyone)

@[mcfunction]
private def missingTag : Prog (Grade.handled ((Tag.grade (.selector (.allPlayers {tags := [.include "feedback.absent"]}))).seq writeGrade)) Unit :=
  capture (Tag.add (.selector (.allPlayers {tags := [.include "feedback.absent"]})) "round.active")

@[mcfunction]
private def title : Prog (Grade.handled ((Title.grade .all).seq writeGrade)) Unit :=
  capture (Title.show .all (.literal "Round one"))

@[mcfunction]
private def subtitle : Prog (Grade.handled ((Title.grade .all).seq writeGrade)) Unit :=
  capture (Title.show .all (.literal "Choose a move") .subtitle)

@[mcfunction]
private def actionbar : Prog (Grade.handled ((Title.grade .all).seq writeGrade)) Unit := do
  input (g := Title.grade .all) (fun n => do Title.show .all (.number (.dynamic n)) .actionbar)

@[mcfunction]
private def rich : Prog (Grade.handled ((Title.grade .self Req.all).seq writeGrade)) Unit :=
  capture (Title.show .self (.ofNbt (nbt% {text: "Ready", color: "gold", bold: true})))

@[mcfunction]
private def times : Prog (Grade.handled ((Title.grade .all).seq writeGrade)) Unit := do
  input (fun n => Title.times .all (.seconds (.decimal 0.25)) (.ticks (.dynamic n))
    (.days (.decimal 0.001)))

@[mcfunction]
private def clearTitle : Prog (Grade.handled ((Title.grade .all).seq writeGrade)) Unit := capture (Title.clear .all)

@[mcfunction]
private def resetTitle : Prog (Grade.handled ((Title.grade .all).seq writeGrade)) Unit := capture (Title.clear .all true)

@[mcfunction]
private def missingTitle : Prog (Grade.handled ((Title.grade nobody).seq writeGrade)) Unit :=
  capture (Title.show nobody (.literal "Absent"))

@[mcfunction]
private def sound : Prog (Grade.handled ((Sound.grade .all).seq writeGrade)) Unit :=
  capture (Sound.play .all "feedback:cue" .ui)

@[mcfunction]
private def minimum : Prog (Grade.handled ((Sound.grade .all).seq writeGrade)) Unit := do
  capture (Sound.play .all "feedback:cue" .ui {minVolume := .decimal 0.25})

@[mcfunction]
private def pitch : Prog (Grade.handled ((Sound.grade .all).seq writeGrade)) Unit := do
  input (g := Sound.grade .all) (fun n => do Sound.play .all "feedback:cue" .ui {pitch := .dynamic n})

@[mcfunction]
private def positioned : Prog (Grade.handled ((Sound.grade .all).seq writeGrade)) Unit := do
  input (g := Sound.grade .all) (fun n => do Sound.play .all "feedback:cue" .ui {
    position := .world (.relative (.dynamic n)) (.relative (.decimal 0.25)) (.relative (.static 0))})

@[mcfunction]
private def missingSound : Prog (Grade.handled ((Sound.grade nobody).seq writeGrade)) Unit :=
  capture (Sound.play nobody "feedback:cue")

@[mcfunction]
private def stopAll : Prog (Grade.handled ((Sound.stopGrade .all).seq writeGrade)) Unit := capture (Sound.stop .all)

@[mcfunction]
private def stopChannel : Prog (Grade.handled ((Sound.stopGrade .all).seq writeGrade)) Unit :=
  capture (Sound.stop .all (some .ui))

@[mcfunction]
private def stopId : Prog (Grade.handled ((Sound.stopGrade .all).seq writeGrade)) Unit :=
  capture (Sound.stop .all (sound := some "feedback:cue"))

@[mcfunction]
private def stopOne : Prog (Grade.handled ((Sound.stopGrade .all).seq writeGrade)) Unit :=
  capture (Sound.stop .all (some .ui) (some "feedback:cue"))

@[mcfunction]
private def stopping : Prog (Grade.handled ((Tag.grade everyone).seq writeGrade)) Unit :=
  (do
    Tag.add everyone "round.active"
    Scoreboard.set (.named "#continued") points (.static 1)
    : Prog ((Tag.grade everyone).seq writeGrade) Int32).ignore

@[mcfunction]
private def continuing : Prog (Grade.handled ((Tag.grade everyone).seq writeGrade)) Unit := do
  (Tag.add everyone "round.active").ignore
  (Scoreboard.set (.named "#continued") points (.static 2)).ignore

@[datapack]
public def specimen : Spec := build {ns := "feedback", registerBudget := 6} do
  onLoad setup.ref
  onLoad loaded.ref
  entry "tag-self" tagSelf.ref
  entry "tag-all" tagAll.ref
  entry "tag-winner" tagWinner.ref
  entry "tag-remove" untag.ref
  entry "tag-list" tagList.ref
  entry "tag-missing" missingTag.ref
  entry "title" title.ref
  entry "subtitle" subtitle.ref
  entry "actionbar" actionbar.ref
  entry "rich" rich.ref
  entry "times" times.ref
  entry "clear" clearTitle.ref
  entry "reset" resetTitle.ref
  entry "title-missing" missingTitle.ref
  entry "sound" sound.ref
  entry "minimum" minimum.ref
  entry "pitch" pitch.ref
  entry "positioned" positioned.ref
  entry "sound-missing" missingSound.ref
  entry "stop-all" stopAll.ref
  entry "stop-channel" stopChannel.ref
  entry "stop-id" stopId.ref
  entry "stop-one" stopOne.ref
  entry "stopping" stopping.ref
  entry "continuing" continuing.ref

end Oria.Proofs.Fixtures.Presentation
