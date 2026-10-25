module
import Oria.Proofs.Fixtures.Utility

private def snapshot (artifact : Oria.Datapack.Artifact) : String :=
  let docs := artifact.files.toList.filterMap fun file =>
    let lines := file.contents.splitOn "\n"
      |>.map (fun line => line.trimAsciiEnd.toString)
      |>.filter fun line =>
        ["say ", "me ", "msg ", "teammsg ", "locate ", "list", "seed", "version",
          "scoreboard players add", "scoreboard players remove"].any
          (fun text => line.startsWith text || line.contains ("run " ++ text)) ||
        line.contains "\"macro\".\"p"
    if file.path.extension != some "mcfunction" || lines.isEmpty then none
    else some (Std.Format.text file.path.toString ++ Std.Format.line ++
      Std.Format.joinSep (lines.map Std.Format.text) Std.Format.line ++ Std.Format.line)
  (Std.Format.joinSep docs Std.Format.line).pretty 120

public def main (args : List String) : IO Unit := do
  let artifact := Oria.Proofs.Fixtures.Utility.specimen.artifact
  match args with
  | ["--snapshot"] => (← IO.getStdout).putStr (snapshot artifact)
  | [destination] => artifact.writeTo destination
  | [] =>
      let expected ← IO.FS.readFile "tests/golden/utility.dp121"
      unless snapshot artifact == expected do throw (.userError "utility command golden differs")
  | _ => throw (.userError "usage: lake exe utility-artifact-test [empty-directory|--snapshot]")
