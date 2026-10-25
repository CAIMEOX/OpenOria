module

import Oria.Proofs.Fixtures.GlobalNbt

open Oria.Proofs.Fixtures.GlobalNbt

private def snapshot : String :=
  (Std.Format.joinSep (scalar.artifact.files.toList.map fun file =>
    Std.Format.text file.path.toString ++ Std.Format.line ++ Std.Format.text file.contents)
    Std.Format.line).pretty 120

public def main (args : List String) : IO Unit := do
  match args with
  | ["--snapshot"] => (← IO.getStdout).putStr snapshot
  | [directory] => specimen.artifact.writeTo directory
  | [directory, "stack"] => allStack.artifact.writeTo directory
  | [directory, "managed"] => managed.artifact.writeTo directory
  | [directory, "relocated"] => relocated.artifact.writeTo directory
  | [] =>
      unless snapshot == (← IO.FS.readFile "tests/golden/global-nbt.dp121") do
        throw (.userError "global NBT golden differs")
      for file in scalar.artifact.files do
        if file.contents.contains "\"arena\"" || file.contents.contains "#nbt_addr" ||
            file.path.toString.contains "__oria/persistent/" then
          throw (.userError "scalar global access uses the managed heap")
        if (file.contents.splitOn "\n").any (·.startsWith "$") then
          throw (.userError "static global access uses a function macro")
      for file in relocated.artifact.files do
        if file.contents.contains "global_test:" then
          throw (.userError "relocated globals retain another pack's namespace")
      for artifact in [specimen.artifact, allStack.artifact, managed.artifact, relocated.artifact] do
        IO.FS.withTempDir fun directory => artifact.writeTo (directory / "pack")
  | _ => throw (.userError "usage: lake exe global-nbt-artifact-test [directory [stack|managed|relocated]|--snapshot]")
