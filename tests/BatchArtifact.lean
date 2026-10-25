module
import Oria.Proofs.Fixtures.Batch

private def snapshot (artifact : Oria.Datapack.Artifact) : String :=
  let docs := artifact.files.toList.filterMap fun file =>
    -- Native function loading trims trailing spaces, including omitted optional arguments.
    let lines := file.contents.splitOn "\n"
      |>.map (fun line => line.trimAsciiEnd.toString)
      |>.filter fun line =>
      if line.startsWith "execute if score #phase " then false else
      ["weather ", "time ", "difficulty", "gamemode ", "defaultgamemode ", "experience ", "recipe ", "enchant ",
        "damage ", "advancement ", "worldborder ", "bossbar ", "team ", "gamerule ", "attribute ",
        "forceload ", "spawnpoint ", "setworldspawn", "spectate", "ride ", "rotate ", "spreadplayers ",
        "particle ", "swing ", "posteffect ", "scoreboard objectives modify",
        "scoreboard objectives setdisplay", "scoreboard players display", "tellraw @a[team=",
        "give ", "clear ", "item ", "loot ", "setblock ", "fill ", "clone ", "teleport ",
        "execute as ", "execute on ", "execute summon ", "execute positioned over ",
        "execute if ", "execute unless ", "execute store result storage batch:execute",
        "execute store success storage batch:execute", "execute store result entity ",
        "execute store result block "].any
          (fun text => line.startsWith text || line.contains ("run " ++ text)) ||
        line.contains "\"macro\".\"p"
    if file.path.extension != some "mcfunction" || lines.isEmpty then none
    else some (Std.Format.text file.path.toString ++ Std.Format.line ++
      Std.Format.joinSep (lines.map Std.Format.text) Std.Format.line ++ Std.Format.line)
  (Std.Format.joinSep docs Std.Format.line).pretty 120

public def main (args : List String) : IO Unit := do
  let artifact := Oria.Proofs.Fixtures.Batch.specimen.artifact
  match args with
  | ["--snapshot"] => (← IO.getStdout).putStr (snapshot artifact)
  | [destination] => artifact.writeTo destination
  | [] =>
      let expected ← IO.FS.readFile "tests/golden/batch.dp121"
      unless snapshot artifact == expected do throw (.userError "bulk command golden differs")
  | _ => throw (.userError "usage: lake exe batch-artifact-test [empty-directory|--snapshot]")
