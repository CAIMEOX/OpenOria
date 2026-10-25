module

import Oria.Datapack
import Oria.Proofs.Fixtures.PersistentRuntime

private def goldenFiles : List String := [
  "allocate.mcfunction", "allocate/append.mcfunction", "copy/5/0.mcfunction",
  "copy/5/lookup.mcfunction", "stamp.mcfunction"]

public def main (args : List String) : IO Unit := do
  let artifact := Oria.Proofs.Fixtures.PersistentRuntime.specimen.artifact
  match args with
  | [destination] => artifact.writeTo destination
  | [] =>
      IO.FS.withTempDir fun root => do
        let output := root / "persistent"
        artifact.writeTo output
        for file in artifact.files do
          unless (← IO.FS.readFile (output / file.path)) == file.contents do
            throw (.userError s!"persistent artifact differs: {file.path}")
        for name in goldenFiles do
          let actual ← IO.FS.readFile (output / "data/memory/function/__oria/persistent" / name)
          let expected ← IO.FS.readFile ("tests/golden/persistent" / (name : System.FilePath))
          unless actual == expected do
            throw (.userError s!"persistent runtime golden differs: {name}")
        let actual ← IO.FS.readFile (output / "data/memory/function/gc.mcfunction")
        let expected ← IO.FS.readFile "tests/golden/persistent/gc.mcfunction"
        unless actual == expected do throw (.userError "collector entry golden differs")
  | _ => throw (.userError "usage: lake exe persistent-artifact-test [empty-directory]")
