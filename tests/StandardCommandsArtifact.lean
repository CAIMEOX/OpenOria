module

import Oria.Datapack
import Oria.Proofs.Fixtures.StandardCommands

private def snapshot (artifact : Oria.Datapack.Artifact) : String :=
  let files := artifact.files.toList.filter fun file =>
    file.contents.contains "random " || file.contents.contains "tellraw " || file.contents.contains "dialog " ||
      file.contents.contains "\"macro\".\"p"
  let docs := files.map fun file =>
    Std.Format.text file.path.toString ++ Std.Format.line ++ Std.Format.text file.contents
  (Std.Format.joinSep docs Std.Format.line).pretty 120

public def main (args : List String) : IO Unit := do
  let artifact := Oria.Proofs.Fixtures.StandardCommands.specimen.artifact
  match args with
  | ["--snapshot"] => (← IO.getStdout).putStr (snapshot artifact)
  | [destination] => artifact.writeTo destination
  | [] =>
      let expected ← IO.FS.readFile "tests/golden/standard-commands.dp121"
      unless snapshot artifact == expected do
        throw (.userError "standard command golden differs")
  | _ => throw (.userError "usage: lake exe standard-command-artifact-test [empty-directory|--snapshot]")
