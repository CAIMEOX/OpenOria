module
import Oria.Proofs.Fixtures.Generation

private def snapshot (artifact : Oria.Datapack.Artifact) : String :=
  let docs := artifact.files.toList.filterMap fun file =>
    let lines := file.contents.splitOn "\n"
      |>.map (fun line => line.trimAsciiEnd.toString)
      |>.filter fun line =>
        ["fillbiome ", "place ", "waypoint ", "stopwatch "].any
          (fun text => line.startsWith text || line.contains ("run " ++ text)) ||
        line.contains "\"macro\".\"p"
    if file.path.extension != some "mcfunction" || lines.isEmpty then none
    else some (Std.Format.text file.path.toString ++ Std.Format.line ++
      Std.Format.joinSep (lines.map Std.Format.text) Std.Format.line ++ Std.Format.line)
  (Std.Format.joinSep docs Std.Format.line).pretty 120

public def main (args : List String) : IO Unit := do
  let artifact := Oria.Proofs.Fixtures.Generation.specimen.artifact
  match args with
  | ["--snapshot"] => (← IO.getStdout).putStr (snapshot artifact)
  | [destination] => artifact.writeTo destination
  | [] =>
      let expected ← IO.FS.readFile "tests/golden/generation.dp121"
      unless snapshot artifact == expected do throw (.userError "generation command golden differs")
  | _ => throw (.userError "usage: lake exe generation-artifact-test [empty-directory|--snapshot]")
