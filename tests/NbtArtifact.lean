module

import Oria.Nbt
import Oria.IR.DP121.Pretty

open Oria.Target.DP121

private structure Note where
  text : String
  counters : Array Int32
  deriving BEq, Oria.Nbt.ToNbt, Oria.Nbt.FromNbt

private def note : Note := ⟨"typed", #[1, 2, 3]⟩

private def value : Oria.Nbt.Value .compound := nbt% {
  small: -128b, medium: 32767s, integer: -2147483648, large: 9223372036854775807L,
  float32: 1e-8f, float64: 1.2345678901234567d, zero: -0.0d,
  tiny: $(Float.ofBits 1), huge: $(Float.ofBits 0x7fefffffffffffff),
  text: "line\n\"quoted\"\\$(literal)",
  bytes: [B; -128, 127], ints: [I; -2147483648, 2147483647], longs: [L; 1, -3],
  mixed: [1, "two", {ready: true}], note: $(note)
}

private def path (key : String) : StoragePath := ⟨.ofString "oria_nbt:test", .key key⟩

private def body : FunctionBody .plain := .plain #[
  .data (.setValue (path "value") value),
  .data (.setValue (path "price$") (nbt% 7)),
  .returnValue 0]

public def main (args : List String) : IO Unit := do
  let [destination] := args
    | throw (.userError "usage: lake exe nbt-artifact-test <function-file>")
  let decoded ← IO.ofExcept ((Oria.Nbt.FromNbt.fromNbt (Oria.Nbt.ToNbt.toNbt note)).mapError (·.pretty 100))
  unless decoded == note do throw (.userError "derived NBT value did not round-trip")
  match value.renderSnbt with
  | .error error => throw (.userError s!"invalid SNBT fixture: {repr error}")
  | .ok _ => IO.FS.writeFile destination (body.pretty 120 ++ "\n")
