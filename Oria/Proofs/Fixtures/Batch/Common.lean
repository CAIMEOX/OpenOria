module
public import Oria
public meta import Oria

namespace Oria.Proofs.Fixtures.Batch
open Oria.Std Oria.Std.Command.Arg

public def points : Command.Objective := "batch.points"
public def writeGrade := Scoreboard.writeGrade (.named "#status")
public def readGrade := Scoreboard.readGrade (.named "#input")
public def origin : Vec3 := .world (.relative (.static 0)) (.relative (.static 0)) (.relative (.static 0))
public def victim : Target := .selector (.allEntities {tags := [.include "batch.victim"], limit := some 1})

private def report (status : Int32) (value : Val Int32) : Prog writeGrade.handled Unit := do
  (Scoreboard.set (.named "#status") points (.static status)).ignore
  (Scoreboard.set (.named "#result") points value).ignore

public def capture {g : Grade} (action : Prog g Int32) : Prog (Grade.handled (g.seq writeGrade)) Unit := by
  simpa only [Grade.handled_seq, Grade.handled_idem, Grade.seq_assoc, Grade.seq_idem] using
    Prog.catchFailure (Prog.bind action (report 1)) (report 0 (-999))

public def input {g : Grade} (action : Val Int32 → Prog g Int32) :
    Prog (Grade.handled ((readGrade.seq g).seq writeGrade)) Unit :=
  capture (g := readGrade.seq g) do
    let n ← Scoreboard.get (.named "#input") points
    action n

@[mcfunction]
public def setup := (Scoreboard.Objectives.add points .dummy).ignore

end Oria.Proofs.Fixtures.Batch
