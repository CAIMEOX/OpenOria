module

import Oria.Datapack
import Oria.Proofs.Fixtures.RecursionRuntime
import Oria.Proofs.Fixtures.DynamicPaths

open Oria.Proofs.Fixtures

public def main (args : List String) : IO Unit := do
  match args with
  | [destination, "recursion"] => RecursionRuntime.specimen.artifact.writeTo destination
  | [destination, "stack"] => RecursionRuntime.allStack.artifact.writeTo destination
  | [destination, "paths"] => DynamicPaths.specimen.artifact.writeTo destination
  | [] =>
      let shared := RecursionRuntime.sharedArtifact.artifact.files.map fun f => (f.path, f.contents)
      let explicit := RecursionRuntime.boundArtifact.artifact.files.map fun f => (f.path, f.contents)
      unless shared == explicit do
        throw (.userError "pure object let differs from explicit binding in the final datapack")
      for artifact in [RecursionRuntime.specimen.artifact, RecursionRuntime.allStack.artifact,
          DynamicPaths.specimen.artifact] do
        if artifact.files.any (·.contents.contains "nbt_args") then
          throw (.userError "native arguments use an intermediate operand array")
        if artifact.files.any (·.contents.contains "\"macro\".\"write\" set value $(p") then
          throw (.userError "native I32 assignment serializes its value through a macro")
        if artifact.files.any (fun f => f.contents.splitOn "\n" |>.any fun line =>
            line.contains "data get storage" && line.contains "\"values\"[$(p1)][$(p2)]" &&
            !line.endsWith " 1") then
          throw (.userError "dominated typed NBT assignment retains its existence precheck")
        IO.FS.withTempDir fun dir => artifact.writeTo (dir / "pack")
      unless RecursionRuntime.specimen.artifact.files.any (fun file =>
          file.contents.contains "set value \"edited\"" &&
          file.contents.contains "$(p0)") do
        throw (.userError "typed native string assignment lost its dynamic document path")
  | _ => throw (.userError "usage: lake exe flow-artifact-test [directory recursion|stack|paths]")
