module

public import Oria
public import Oria.Datapack
meta import Oria
meta import Oria.Datapack

namespace Oria.Proofs.Fixtures.DynamicPaths

open Oria Oria.Std Oria.Std.Command.Arg Oria.Datapack

@[expose] public def store : DataTarget := .storage "path_test:data"
private def objective : Command.Objective := "path_test.oria"
private def grade : Grade := ⟨Req.none,
  Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.failure⟩

@[mcfunction]
public def read (i j : Val Int32) : Prog (Data.grade store) Int32 :=
  let path : Nbt.Path Scalar (Nbt.Value .compound) := ((Nbt.Path.key "matrix").at (.dynamic i)).at (.dynamic j)
  Data.get store (some path)

@[mcfunction]
public def copy (src dst : Val Int32) : Prog (Data.grade store) Int32 := do
  let source : Nbt.Path Scalar (Nbt.Value .compound) := (Nbt.Path.key "slots").at (.dynamic src)
  let into : Nbt.Path Scalar (Nbt.Value .compound) := (Nbt.Path.key "slots").at (.dynamic dst)
  Data.modify store into .set (.from store (some source))

@[mcfunction]
public def write (i value : Val Int32) : Prog (Data.grade store) Int32 := do
  let path : Nbt.Path Scalar (Nbt.Value .compound) := ((Nbt.Path.key "slots").at (.dynamic i)).field "two words"
  Data.modify store path .set (.value (.hole .i32 value))

@[mcfunction]
public def constant : Prog (Data.grade store) Int32 :=
  let path : Nbt.Path Scalar (Nbt.Value .compound) :=
    ((Nbt.Path.key "matrix").at (.dynamic (1 : Val Int32))).at (.static 1)
  Data.get store (some path)

@[mcfunction]
private def missing : Prog grade Int32 := do
  read.call 99 0
  Scoreboard.set (.named "#continued") objective (.static 1)
  return 0

@[mcfunction]
private def logic : Prog grade Int32 := do
  Data.merge store (nbt% {matrix: [[10, 11], [20, 21]], slots: [{x: 5}, {x: 9}]})
  let i ← Scoreboard.get (.named "#i") objective
  let j ← Scoreboard.get (.named "#j") objective
  let value ← read.call i j
  Scoreboard.set (.named "#read") objective (.dynamic value)
  let last ← read.call i (-1)
  Scoreboard.set (.named "#last") objective (.dynamic last)
  let value ← constant.call
  Scoreboard.set (.named "#constant") objective (.dynamic value)
  copy.call i j
  write.call j (42 : Val Int32)
  Scoreboard.set (.named "#continued") objective (.static 0)
  missing.call.ignore
  let path : Nbt.Path Scalar (Nbt.Value .compound) := ((Nbt.Path.key "slots").at (.dynamic j)).field "two words"
  Execute.forEach [.when (.data store path)]
    (Scoreboard.set (.named "#exists") objective (.static 1))
  return 0

@[mcfunction]
private def run : Prog (Grade.handled grade) Unit := logic.call.ignore

@[datapack]
public def specimen : Spec := build { ns := "path_test", registerBudget := 8 } do
  entry "run" run.ref

end Oria.Proofs.Fixtures.DynamicPaths
