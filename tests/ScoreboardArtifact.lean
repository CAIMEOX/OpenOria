module

import Oria.Datapack
import Oria.Proofs.Fixtures.ScoreboardRuntime

private def snapshot (artifact : Oria.Datapack.Artifact) : String :=
  let docs := artifact.files.toList.filterMap fun file =>
    let lines := file.contents.splitOn "\n" |>.filter fun line =>
      ["scoreboard objectives ", "scoreboard players enable ", "scoreboard players reset ",
        "trigger ", "\"macro\".\"p"].any (fun text => line.contains text)
    if file.path.extension != some "mcfunction" || lines.isEmpty then none
    else some (Std.Format.text file.path.toString ++ Std.Format.line ++
      Std.Format.joinSep (lines.map Std.Format.text) Std.Format.line ++ Std.Format.line)
  (Std.Format.joinSep docs Std.Format.line).pretty 120

public def main (args : List String) : IO Unit := do
  let artifact := Oria.Proofs.Fixtures.ScoreboardRuntime.specimen.artifact
  match args with
  | ["--snapshot"] => (← IO.getStdout).putStr (snapshot artifact)
  | [destination] => artifact.writeTo destination
  | [] =>
      let expected ← IO.FS.readFile "tests/golden/scoreboard.dp121"
      unless snapshot artifact == expected do
        throw (.userError "scoreboard command golden differs")
  | _ => throw (.userError "usage: lake exe scoreboard-artifact-test [empty-directory|--snapshot]")
