import Lean

open System Lean

private def build (dir : FilePath) (args : Array String) : IO Unit := do
  let result ← IO.Process.output {cmd := "lake", args, cwd := dir}
  unless result.exitCode == 0 do
    throw (.userError (result.stdout ++ result.stderr))

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (.userError message)

private def contents (dir : FilePath) : IO (Array String) := do
  let paths : Array FilePath ← IO.ofExcept <|
    Json.parse (← IO.FS.readFile (dir / "manifest.json")) >>= fromJson?
  paths.mapM (fun path => IO.FS.readFile (dir / path))

public def main (args : List String) : IO Unit := do
  let [dir] := args | throw (.userError "usage: LakeBuild.lean <consumer-project>")
  let dir : FilePath := dir
  let output := dir / ".lake/build/datapacks/Game.Pack"
  let pack := output / "Game.game"
  let home := pack / "data/consumer/function/home.mcfunction"
  let away := pack / "data/consumer/function/away.mcfunction"
  let metadata := pack / "pack.mcmeta"
  build dir #["update"]
  build dir #["build"]
  check (← home.pathExists) "default library facet exports the private pack declaration"
  let files ← contents output
  check (files.size >= 6) "the pack includes its imported named-call dependency and callback files"
  let time := (← metadata.metadata).modified
  build dir #["build"]
  check ((← metadata.metadata).modified == time) "an unchanged build preserves generated files"

  IO.FS.removeFile home
  build dir #["build", "+Game.Pack:datapack"]
  check (← home.pathExists) "a missing generated file is restored"

  let shared := dir / "Game/Shared.lean"
  IO.FS.writeFile shared ((← IO.FS.readFile shared).replace "n + 1" "n + 2")
  build dir #["build", "+Game.Pack:datapack"]
  check ((← contents output) != files) "an imported definition change updates the compiled pack"

  let source := dir / "Game/Pack.lean"
  let original ← IO.FS.readFile source
  IO.FS.writeFile source (original.replace "entry \"home\"" "entry \"away\"")
  let extra := pack / "notes.txt"
  IO.FS.writeFile extra "application-owned file\n"
  build dir #["build"]
  check (← away.pathExists) "a changed entry is exported"
  check (!(← home.pathExists)) "the previous generated entry is removed"
  check ((← IO.FS.readFile extra) == "application-owned file\n") "other output files are preserved"

  IO.FS.writeFile source (original.replace "@[datapack]\n" "")
  build dir #["build", ":datapack"]
  check (!(← metadata.pathExists)) "removing a pack declaration removes its generated metadata"
  check ((← contents output).isEmpty) "the module's output inventory follows its current declarations"
  check (← extra.pathExists) "other files survive removal of a pack declaration"
  IO.println "Lake consumer acceptance passed"
