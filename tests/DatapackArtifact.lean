module

import Oria.Datapack
import Oria.Proofs.Fixtures.Datapack
import Oria.Proofs.Fixtures.DatapackRuntime

open Oria.Proofs.Fixtures.Datapack

private def checkWrite : IO Unit := IO.FS.withTempDir fun root => do
  let destination := root / "pack"
  imported.artifact.writeTo destination
  for file in imported.artifact.files do
    unless (← IO.FS.readFile (destination / file.path)) == file.contents do
      throw (.userError s!"artifact file differs: {file.path}")
  let blocked ← try
    imported.artifact.writeTo destination
    pure false
  catch _ => pure true
  unless blocked do throw (.userError "nonempty destination was accepted")
  for file in imported.artifact.files do
    unless (← IO.FS.readFile (destination / file.path)) == file.contents do
      throw (.userError s!"existing artifact was modified: {file.path}")
  IO.FS.createDir (root / "empty")
  imported.artifact.writeTo (root / "empty")
  let specimen := Oria.Proofs.Fixtures.DatapackRuntime.specimen.artifact
  let output := root / "runtime"
  specimen.writeTo output
  let golden : System.FilePath := "tests/golden/datapack"
  let expected ← (← golden.walkDir).filterM fun path => return !(← path.isDir)
  unless expected.size == specimen.files.size do
    throw (.userError "datapack golden file set differs")
  for file in specimen.files do
    let actual ← IO.FS.readFile (output / file.path)
    let expected ← IO.FS.readFile (golden / file.path)
    unless actual == expected do
      throw (.userError s!"datapack golden differs: {file.path}\n{actual}")

public def main (args : List String) : IO Unit := do
  match args with
  | [] => checkWrite
  | [destination] =>
      Oria.Proofs.Fixtures.DatapackRuntime.specimen.artifact.writeTo destination
  | _ => throw (.userError "usage: lake exe datapack-artifact-test [empty-directory]")
