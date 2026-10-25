module

public import Oria
public import Oria.Datapack
meta import Oria
meta import Oria.Datapack

namespace Oria.Proofs.Fixtures.Memory

open Oria

private structure Buffer where
  values : Array Int32
  label : String
  deriving Nbt.Repr

@[mcfunction]
private def forwarded (s : Val (Nbt.Ref Buffer)) (i n : Val Int32) := show Prog _ Int32 from do
  s.values[i + 0] := n
  s.label := "written"
  let y ← s.values[i]
  return y

@[mcfunction]
private def forward := show Prog _ Unit from do
  let s ← Nbt.alloc (Buffer.mk #[4] "initial")
  let n ← forwarded.call s 0 9
  if n != 9 then Prog.fail

@[mcfunction]
private def aliases (a b : Val (Nbt.Ref Buffer)) (i j : Val Int32) := show Prog _ Int32 from do
  let old ← a.values[i]
  b.values[j] := old + 1
  let new ← a.values[i]
  return new

@[mcfunction]
private def aliasing := show Prog _ Unit from do
  let a ← Nbt.alloc (Buffer.mk #[10, 20] "a")
  let b ← Nbt.alloc (Buffer.mk #[30, 40] "b")
  let n ← aliases.call a a 0 0
  if n != 11 then Prog.fail
  let n ← aliases.call a b 0 0
  if n != 11 then Prog.fail
  let n ← aliases.call a a 0 1
  if n != 11 then Prog.fail
  let n ← b.values[0]
  if n != 12 then Prog.fail

@[mcfunction]
private def signed (s : Val (Nbt.Ref Buffer)) := show Prog _ Int32 from do
  let _old ← s.values[0]
  s.values[-1] := 23
  let new ← s.values[0]
  return new

@[mcfunction]
private def signedIndices := show Prog _ Unit from do
  let s ← Nbt.alloc (Buffer.mk #[7] "single")
  let n ← signed.call s
  if n != 23 then Prog.fail
  let s ← Nbt.alloc (Buffer.mk #[7, 8] "pair")
  let n ← signed.call s
  if n != 7 then Prog.fail
  let first ← s.values[-2]
  s.values[-1] := 24
  let same ← s.values[-2]
  if same != first then Prog.fail

@[mcfunction]
private def resizing := show Prog _ Unit from do
  let s ← Nbt.alloc (Buffer.mk #[7] "single")
  let old ← s.values[-1]
  Nbt.append s Buffer.Nbt.values (.i32 (old + 1))
  let new ← s.values[-1]
  if new != 8 then Prog.fail
  Nbt.clear s Buffer.Nbt.values
  let size ← Nbt.length s Buffer.Nbt.values
  if size != 0 then Prog.fail
  let present ← (Nbt.readI32 s (Buffer.Nbt.values.at (0 : Val Int32))).isSuccess
  if present then Prog.fail
  Nbt.set s Buffer.Nbt.values (.literal #[31])
  let _before ← s.values[0]
  Nbt.set s Nbt.Access.root (.literal (Buffer.mk #[41] "replaced"))
  let after ← s.values[0]
  if after != 41 then Prog.fail

@[mcfunction]
private def mutate (s : Val (Nbt.Ref Buffer)) := show Prog _ Unit from do
  s.values[0] := 61

@[mcfunction]
private def calls := show Prog _ Unit from do
  let s ← Nbt.alloc (Buffer.mk #[51] "calls")
  let _before ← s.values[0]
  mutate.call s
  let after ← s.values[0]
  if after != 61 then Prog.fail

@[mcfunction]
private def failedWrite (s : Val (Nbt.Ref Buffer)) (i : Val Int32) := show Prog _ Int32 from do
  let _before ← s.values[0]
  let changed ← (Nbt.set s (Buffer.Nbt.values.at i) (.i32 99)).isSuccess
  if changed then Prog.fail
  let after ← s.values[0]
  return after

@[mcfunction]
private def failure := show Prog _ Unit from do
  let s ← Nbt.alloc (Buffer.mk #[71] "failure")
  let n ← failedWrite.call s 99
  if n != 71 then Prog.fail
  Nbt.clear s Buffer.Nbt.values
  let read ← (forwarded.call s 0 91).isSuccess
  if read then Prog.fail

@[mcfunction]
private def joined (s : Val (Nbt.Ref Buffer)) (b : Val Bool) := show Prog _ Int32 from do
  let _before ← s.values[0]
  if b then
    s.values[0] := 81
  else
    s.values[0] := 82
  let after ← s.values[0]
  return after

@[mcfunction]
private def conditional (s : Val (Nbt.Ref Buffer)) (b : Val Bool) (i : Val Int32) := show Prog _ Int32 from do
  if b then
    s.values[i] := 5
  let n ← s.values[0]
  s.values[0] := n + 1
  return n

@[mcfunction]
private def controlled (s : Val (Nbt.Ref Buffer)) (b : Val Bool) (i : Val Int32) := show Prog _ Int32 from do
  if b then
    s.values[i] := 7
    return 70
  else
    for j in [0, 1] do
      s.values[j] := j + 30
  let n ← s.values[0]
  s.values[0] := n + 1
  return n

@[mcfunction]
private def joins := show Prog _ Unit from do
  let s ← Nbt.alloc (Buffer.mk #[0, 0] "joins")
  let yes ← joined.call s (Bool.lit true)
  if yes != 81 then Prog.fail
  let no ← joined.call s (Bool.lit false)
  if no != 82 then Prog.fail
  let skipped ← conditional.call s (Bool.lit false) 99
  if skipped != 82 then Prog.fail
  let n ← s.values[0]
  if n != 83 then Prog.fail
  let failed ← (conditional.call s (Bool.lit true) 99).isSuccess
  if failed then Prog.fail
  let n ← s.values[0]
  if n != 83 then Prog.fail
  let set ← conditional.call s (Bool.lit true) 0
  if set != 5 then Prog.fail
  let n ← s.values[0]
  if n != 6 then Prog.fail
  let early ← controlled.call s (Bool.lit true) 0
  if early != 70 then Prog.fail
  let n ← s.values[0]
  if n != 7 then Prog.fail
  let loop ← controlled.call s (Bool.lit false) 99
  if loop != 30 then Prog.fail
  let a ← s.values[0]
  let b ← s.values[1]
  if a != 31 || b != 31 then Prog.fail

public def entries : Datapack.Builder Unit := do
  Datapack.entry "memory/forward" forward.ref
  Datapack.entry "memory/alias" aliasing.ref
  Datapack.entry "memory/indices" signedIndices.ref
  Datapack.entry "memory/resize" resizing.ref
  Datapack.entry "memory/call" calls.ref
  Datapack.entry "memory/failure" failure.ref
  Datapack.entry "memory/join" joins.ref

@[datapack]
public def forwardArtifact : Datapack.Spec := Datapack.build {ns := "memory_forward"} do
  Datapack.entry "run" forward.ref

end Oria.Proofs.Fixtures.Memory
