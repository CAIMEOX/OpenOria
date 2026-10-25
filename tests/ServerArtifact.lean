module
import Oria.Proofs.Fixtures.Server

private def snapshot (artifact : Oria.Datapack.Artifact) : String :=
  let docs := artifact.files.toList.filterMap fun file =>
    let lines := file.contents.splitOn "\n"
      |>.map (fun line => line.trimAsciiEnd.toString)
      |>.filter fun line =>
        ["datapack ", "tick ", "kick ", "transfer ", "whitelist ",
          "ban ", "ban-ip ", "banlist", "pardon ", "pardon-ip ", "op ", "deop ",
          "setidletimeout ", "scoreboard objectives list", "scoreboard players list",
          "scoreboard players set @a", "scoreboard players reset @a",
          "scoreboard players enable @a", "scoreboard players operation @a"].any
          (fun text => line.startsWith text || line.contains ("run " ++ text)) ||
        line.contains "\"macro\".\"p" ||
        (line.contains "operation #left" && line.contains "server.scores")
    if file.path.extension != some "mcfunction" || lines.isEmpty then none
    else some (Std.Format.text file.path.toString ++ Std.Format.line ++
      Std.Format.joinSep (lines.map Std.Format.text) Std.Format.line ++ Std.Format.line)
  (Std.Format.joinSep docs Std.Format.line).pretty 120

public def main (args : List String) : IO Unit := do
  let artifact := Oria.Proofs.Fixtures.Server.specimen.artifact
  match args with
  | ["--snapshot"] => (← IO.getStdout).putStr (snapshot artifact)
  | [destination] => artifact.writeTo destination
  | [] =>
      let expected ← IO.FS.readFile "tests/golden/server.dp121"
      unless snapshot artifact == expected do throw (.userError "server command golden differs")
  | _ => throw (.userError "usage: lake exe server-artifact-test [empty-directory|--snapshot]")
