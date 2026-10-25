module

import Oria.Datapack
import Oria.Proofs.Fixtures.ExecuteRuntime

private def snapshot (artifact : Oria.Datapack.Artifact) : String :=
  let docs := artifact.files.toList.map fun file =>
    Std.Format.text file.path.toString ++ Std.Format.line ++ Std.Format.text file.contents
  (Std.Format.joinSep docs Std.Format.line).pretty 120

public def main (args : List String) : IO Unit := do
  let artifact := Oria.Proofs.Fixtures.ExecuteRuntime.specimen.artifact
  match args with
  | ["--snapshot"] => (← IO.getStdout).putStr (snapshot artifact)
  | [destination] => artifact.writeTo destination
  | [destination, "zero"] => Oria.Proofs.Fixtures.ExecuteRuntime.allStack.artifact.writeTo destination
  | [] =>
      let expected ← IO.FS.readFile "tests/golden/execute.dp121"
      unless snapshot artifact == expected do throw (.userError "execute golden differs")
  | _ => throw (.userError "usage: lake exe execute-artifact-test [empty-directory [zero]|--snapshot]")
