module

public import Oria
public import Oria.Datapack
meta import Oria
meta import Oria.Datapack

namespace Oria.Proofs.Fixtures.RuntimeNbt

open Oria Oria.Std Oria.Std.Command.Arg Oria.Persistent

public structure Packet where
  document : Nbt.Data
  count : Int32
  deriving Oria.Object

private def db : DataTarget := .storage "native_test:data"
private def objective : Command.Objective := "native_test.vm"
private def queryGrade : Grade := ⟨Req.none,
  Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.failure⟩
private def grade : Grade := (queryGrade.seq allocGrade).seq writeGrade

@[root]
private def saved : Root Nbt.Data := Root.init do
  let initial ← Nbt.literal (nbt% {message: "initial"})
  let value ← Nbt.forget initial
  persist value

@[mcfunction]
private def identity (value : Val Nbt.Data) : Prog .pure Nbt.Data := do
  return value

@[mcfunction]
private def unpack (value : Val Packet) : Prog .pure Nbt.Data := do
  match value with
  | .mk document _ => return document

@[mcfunction]
private def ambiguous : Prog queryGrade Int32 := do
  Data.readOne db (some ((Nbt.Path.key "tasks").all))
  Scoreboard.set (.named "#ambiguous_continued") objective (.static 1)
  return 0

@[mcfunction]
private def missing : Prog queryGrade Int32 := do
  Data.readOne db (some (.key "missing"))
  Scoreboard.set (.named "#missing_continued") objective (.static 1)
  return 0

@[mcfunction]
private def stringNumber : Prog queryGrade Int32 := do
  let value ← Data.readOne db (some ((Nbt.Path.key "exact").field "text"))
  Nbt.toI32 value
  Scoreboard.set (.named "#string_continued") objective (.static 1)
  return 0

@[mcfunction]
private def logic : Prog grade Int32 := do
  (Data.merge db (nbt% {
    tasks: [{owner: "Ada", n: 1}, {owner: "Bob", n: 2}, {owner: "Ada", n: 3}],
    exact: {long: 9223372036854775807L, tiny: 0.0000000000000001d,
      text: "hello \"world\"", bytes: [B; -1, 2], longs: [L; 1, 3],
      byte: -5b, short: -8s, integer: -2147483648, float: 3.5f, ints: [I; 1, -2]}})).ignore
  let all ← Data.readAll db (some (((Nbt.Path.key "tasks").matching (nbt% {owner: "Ada"})).field "n"))
  Data.write db (.key "selected") all
  let empty ← Data.readAll db (some (.key "missing"))
  Data.write db (.key "empty") empty
  let nested ← Data.readAll db (some (.key "tasks"))
  Data.write db (.key "nested") nested
  let whole ← Data.readOne db (some (.key "tasks"))
  let i ← Scoreboard.get (.named "#index") objective
  let item ← Nbt.readOne whole (some ⟨.index (.dynamic i), []⟩)
  let number ← Nbt.readOne item (some (.key "n"))
  let n ← Nbt.toI32 number
  Scoreboard.set (.named "#selected") objective (.dynamic n)
  let computed ← Nbt.ofI32 (n + 40)
  Data.write db (.key "computed") computed
  let document ← Data.readOne db (some (.key "exact"))
  let document ← identity.call document
  let packet ← Packet.Obj.Ctor.mk document 7
  let document ← unpack.call packet
  Data.write db (.key "copied") document
  Data.modify db (.key "macro_copy") .set (.value (Nbt.native document))
  let value ← persist document
  saved := value
  let a ← Nbt.literal (.string "same")
  let b ← Nbt.literal (.string "same")
  Data.write db (.key "literal_a") a
  Data.write db (.key "literal_b") b
  Scoreboard.set (.named "#ambiguous_continued") objective (.static 0)
  Scoreboard.set (.named "#missing_continued") objective (.static 0)
  Scoreboard.set (.named "#string_continued") objective (.static 0)
  ambiguous.call.ignore
  missing.call.ignore
  stringNumber.call.ignore
  return 0

@[mcfunction]
private def run : Prog (Grade.handled grade) Unit := logic.call.ignore

@[mcfunction]
private def restore : Prog (Grade.handled (readGrade.seq (Data.grade db))) Unit := do
  let value ← saved
  (Data.write db (.key "restored") value).ignore

@[datapack]
public def specimen : Datapack.Spec := Datapack.build { ns := "native_test", registerBudget := 6 } do
  Datapack.root "native_test:saved" saved
  Datapack.entry "run" run.ref
  Datapack.entry "restore" restore.ref
  Datapack.collector "gc"

@[datapack]
public def registers : Datapack.Spec := {
  specimen with
  settings := { specimen.settings with ns := "native_reg", registerBudget := 12 }
  persistentRoots := specimen.persistentRoots.map fun (_, root) => ("native_reg:saved", root) }

end Oria.Proofs.Fixtures.RuntimeNbt
