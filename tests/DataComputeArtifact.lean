module

import Oria.Datapack
import Oria.Proofs.Fixtures.DataCompute

private def snapshot (artifact : Oria.Datapack.Artifact) : String :=
  let docs := artifact.files.toList.filterMap fun file =>
    let lines := file.contents.splitOn "\n" |>.filter fun line =>
      ["compute ", "data get storage dctest:data", "data get entity ", "data merge ",
        "data modify storage dctest:data", "data modify block ", "data remove storage dctest:data",
        "\"macro\".\"p"].any (fun text => line.contains text)
    if lines.isEmpty then none
    else some (Std.Format.text file.path.toString ++ Std.Format.line ++
      Std.Format.joinSep (lines.map Std.Format.text) Std.Format.line ++ Std.Format.line)
  (Std.Format.joinSep docs Std.Format.line).pretty 120

public def main (args : List String) : IO Unit := do
  let artifact := Oria.Proofs.Fixtures.DataCompute.specimen.artifact
  match args with
  | ["--snapshot"] => (← IO.getStdout).putStr (snapshot artifact)
  | [destination] => artifact.writeTo destination
  | [] =>
      let expected ← IO.FS.readFile "tests/golden/data-compute.dp121"
      unless snapshot artifact == expected do
        throw (.userError "data and compute golden differs")
  | _ => throw (.userError "usage: lake exe data-compute-artifact-test [empty-directory|--snapshot]")
