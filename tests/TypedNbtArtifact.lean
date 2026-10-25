module

import Oria.Proofs.TypedNbt

example : Oria.Nbt.Access (Oria.Val Int32) Oria.Proofs.TypedNbt.State (Array Int32) :=
  Oria.Proofs.TypedNbt.State.Nbt.input

example (s : Oria.Proofs.TypedNbt.State) :
    Oria.Nbt.FromNbt.fromNbt (Oria.Nbt.ToNbt.toNbt s) = Except.ok s :=
  Oria.Nbt.Repr.roundTrip s

public def main (args : List String) : IO Unit := do
  match args with
  | [destination] => Oria.Proofs.TypedNbt.specimen.artifact.writeTo destination
  | [destination, "stack"] => Oria.Proofs.TypedNbt.allStack.artifact.writeTo destination
  | [] =>
      let artifact := Oria.Proofs.Fixtures.Memory.forwardArtifact.artifact
      if artifact.files.any (fun f => f.contents.splitOn "\n" |>.any fun line =>
          line.contains "data get storage" && line.contains "\"values\"[" && line.endsWith " 1") then
        throw (.userError "forwarded typed NBT read remains in the final datapack")
      unless artifact.files.any (·.contents.contains "set compute default integer") do
        throw (.userError "register-backed I32 writes must use native score providers")
      for artifact in [Oria.Proofs.TypedNbt.specimen.artifact, Oria.Proofs.TypedNbt.allStack.artifact] do
        IO.FS.withTempDir fun dir => artifact.writeTo (dir / "pack")
  | _ => throw (.userError "usage: lake exe typed-nbt-artifact-test [directory [stack]]")
