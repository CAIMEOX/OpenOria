module

import Oria.Datapack
import Oria.Proofs.Fixtures.Optimization
import Std.Data.HashSet.Basic

open Oria.Proofs.Fixtures.Optimization

private def check (artifact : Oria.Datapack.Artifact) (ns : String) : IO Unit := do
  let commands := artifact.files.toList.filter (·.path.extension == some "mcfunction")
  let text := String.intercalate "\n" (commands.map (·.contents))
  for name in ["empty-a", "empty-b", "__oria/load"] do
    unless commands.any (·.path.toString == s!"data/{ns}/function/{name}.mcfunction") do
      throw (.userError s!"missing stable entry {name}")
  for name in ["empty-a", "empty-b"] do
    let some entry := commands.find? (·.path.toString == s!"data/{ns}/function/{name}.mcfunction")
      | throw (.userError s!"missing {name}")
    if entry.contents.contains "storage" then
      throw (.userError s!"scalar entry initializes invocation storage: {name}")
  for value in ["set #negative opt.results -999", "set #division opt.results -4",
      "set #zero_failure opt.results 1", "set #overflow opt.results -2147483648"] do
    unless text.contains value do throw (.userError s!"constant not encoded literally: {value}")
  if ["#dead_branch", "#dead_join", "#dead_divisor", "#dead_zero", " *= "].any (fun value => text.contains value) then
    throw (.userError "unreachable effect or unused multiplication was retained")
  if text.contains "\"stack_draft\" set value {\"locals\":[],\"saved\":[],\"result\":[]}" then
    throw (.userError "capture-free Execute allocated an empty frame")
  if text.contains "].\"tag\"" then
    throw (.userError "single-constructor record projection reads a tag")
  let fields := commands.filter fun f => f.contents.contains "].\"payload\"[0]"
  unless fields.length == 1 && fields.all (·.contents.contains "].\"payload\"[1]") do
    throw (.userError "record fields did not share one address macro")
  unless text.contains s!"scoreboard players add #r" || text.contains s!"scoreboard players add #s" do
    throw (.userError "constant addition was not selected as an immediate instruction")
  let macros := commands.filter (·.contents.contains "$return run scoreboard players add #count opt.results $(p0)")
  unless macros.length == 1 do
    throw (.userError s!"expected one shared count macro, got {macros.length}")
  let mut seen : Std.HashSet String := {}
  for file in commands do
    if file.path.toString.contains "/__oria/" then
      if seen.contains file.contents then
        throw (.userError s!"duplicate private function body: {file.path}")
      seen := seen.insert file.contents

public def main (args : List String) : IO Unit := do
  match args with
  | [destination] => specimen.artifact.writeTo destination
  | [destination, "zero"] => allStack.artifact.writeTo destination
  | [] =>
      for file in identities.artifact.files do
        if file.contents.contains " /= " || file.contents.contains " -= " then
          throw (.userError "neutral arithmetic retained division or self-subtraction")
      check specimen.artifact "opt_test"
      check allStack.artifact "opt_zero"
      for file in predicates.artifact.files ++ crossPredicates.artifact.files do
        if file.path.toString.contains "/__oria/m" then
          if (file.contents.splitOn "\n").any (fun line =>
              line.startsWith "execute if " && line.contains "run scoreboard players set" && line.endsWith " 1") then
            throw (.userError "a branch-only negated comparison materialized a Boolean")
      let preparations := macros.artifact.files.toList.flatMap (fun file => file.contents.splitOn "\n")
        |>.filter (fun line => line.startsWith "execute store result storage reuse_test:runtime \"macro\".\"p0\"")
      unless preparations.length <= 2 do
        throw (.userError s!"a stable argument was prepared repeatedly: {preparations.length} stores")
  | _ => throw (.userError "usage: lake exe optimization-artifact-test [empty-directory [zero]]")
