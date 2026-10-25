module

import Oria.Datapack
import Oria.Proofs.Fixtures.RuntimeNbt

private def snapshot (artifact : Oria.Datapack.Artifact) : String :=
  let docs := artifact.files.toList.filterMap fun file =>
    if file.path.toString.contains "/nbt" || file.path.toString.contains "/arg" then
      some (Std.Format.text file.path.toString ++ Std.Format.line ++
        Std.Format.text file.contents)
    else none
  (Std.Format.joinSep docs Std.Format.line).pretty 120

public def main (args : List String) : IO Unit := do
  let artifact := Oria.Proofs.Fixtures.RuntimeNbt.specimen.artifact
  match args with
  | [destination, "registers"] => Oria.Proofs.Fixtures.RuntimeNbt.registers.artifact.writeTo destination
  | ["--snapshot"] => (← IO.getStdout).putStr (snapshot artifact)
  | [destination] => artifact.writeTo destination
  | [] =>
      let expected ← IO.FS.readFile "tests/golden/runtime-nbt.dp121"
      unless snapshot artifact == expected do
        throw (.userError "runtime NBT golden differs")
  | _ => throw (.userError "usage: lake exe runtime-nbt-artifact-test [empty-directory|--snapshot]")
