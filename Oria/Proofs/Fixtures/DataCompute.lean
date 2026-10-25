module

public import Oria
public import Oria.Datapack
public import Oria.Std.Compute.Number
meta import Oria
meta import Oria.Datapack
meta import Oria.Std.Compute.Number

namespace Oria.Proofs.Fixtures.DataCompute

open Oria.Std Oria.Std.Command.Arg Oria.Datapack
open Oria.NumberProvider (Number)

private def store : DataTarget := .storage "dctest:data"
private def path (key : String) : Nbt.Path Scalar (Nbt.Value .compound) := (Nbt.Path.key "root").field key
private def points : Command.Objective := "dctest.oria"
private def dataGrade : Grade := ⟨Req.none, Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩
private def storageGrade := dataGrade.seq ⟨Req.none, Eff.scoreboardWrite⟩
private def worldGrade : Grade := ⟨Req.all, storageGrade.eff⟩
private def dynamicGrade : Grade := storageGrade.seq (Compute.grade .default)

@[mcfunction]
private def storage : Prog storageGrade Int32 := do
  Data.merge store (nbt% {root: {n: -3.5d, text: "abcdef", xs: [2, 3], obj: {x: 1}, drop: true}})
  let root ← Data.get store
  Scoreboard.set (.named "#root") points (.dynamic root)
  let n ← Data.get store (some (path "n"))
  Scoreboard.set (.named "#floor") points (.dynamic n)
  let scaled ← Data.getScaled store (path "n") 2
  Scoreboard.set (.named "#scaled") points (.dynamic scaled)
  let size ← Data.get store (some (path "text"))
  Scoreboard.set (.named "#length") points (.dynamic size)
  Data.modify store (path "copied") .set (.from store (some (path "obj")))
  Data.modify store (path "slice") .set (.string store (path "text") (.between (.static 1) (.static (-1))))
  Data.modify store (path "suffix") .set (.string store (path "text") (.from (.static (-2))))
  Data.modify store (path "as_text") .set (.string store (path "n") .all)
  Data.modify store (path "xs") .prepend (.ofNbt (1 : Int32))
  Data.modify store (path "xs") .append (.ofNbt (4 : Int32))
  Data.modify store (path "xs") (.insert (.static 2)) (.ofNbt (9 : Int32))
  Data.modify store (path "ys") .set (.ofNbt (nbt% []))
  Data.modify store (path "ys") .append (.from store (some ((path "xs").child .all)))
  Data.modify store (path "copied") .merge (.ofNbt (nbt% {y: 2}))
  Data.remove store (path "drop")
  let count ← Data.get store (some (path "xs"))
  Scoreboard.set (.named "#count") points (.dynamic count)
  return 0

@[mcfunction]
private def storageEntry : Prog (Grade.handled storageGrade) Unit := storage.call.ignore

@[mcfunction]
private def write (n : Val Int32) : Prog dataGrade Int32 := do
  Data.modify store (path "mixed") .set <| .value <| .nbtCompound [
    (⟨"text"⟩, .nbt (.string "$(literal)")), (⟨"n"⟩, .hole .i32 n)]

@[mcfunction]
private def dynamic : Prog dynamicGrade Int32 := do
  let n ← Scoreboard.get (.named "#input") points
  write.call n
  let result ← Compute.runInputs .default (Number.input n + 10)
  Scoreboard.set (.named "#dynamic") points (.dynamic result)
  let zero ← (Compute.runInputs .default (Number.input n / 0)).isSuccess
  if zero then Prog.fail
  let overflow ← (Compute.runInputs .default (Number.input n + 2147483647)).isSuccess
  if overflow then Prog.fail
  let root ← Compute.runInputs .default (Number.sqrt (Number.fromInt (Number.input n)))
  Scoreboard.set (.named "#dynamic_root") points (.dynamic root)
  Data.modify store (path "xs") (.insert (.dynamic n)) (.ofNbt (7 : Int32))
  return 0

@[mcfunction]
private def dynamicEntry : Prog (Grade.handled dynamicGrade) Unit := dynamic.call.ignore

@[mcfunction]
private def compute : Prog worldGrade Int32 := do
  let sum ← Compute.run .default (.integer (.ofNbt (nbt% {type: "minecraft:add", inputs: [2, 3, 4]})))
  Scoreboard.set (.named "#sum") points (.dynamic sum)
  let quotient ← Compute.run .default (.integer (.ofNbt (nbt% {type: "minecraft:div", left: -7, right: 2})))
  Scoreboard.set (.named "#quotient") points (.dynamic quotient)
  let floor ← Compute.run .default (.float (.ofNbt (-3.5 : Float)))
  Scoreboard.set (.named "#float") points (.dynamic floor)
  let scaled ← Compute.scaled .default (.ofNbt (-3.5 : Float)) 2
  Scoreboard.set (.named "#float_scaled") points (.dynamic scaled)
  let named ← Compute.run .default (.integer (.named "oria_test:nine"))
  Scoreboard.set (.named "#named") points (.dynamic named)
  Data.modify store (path "integer") .set (.compute .default (.integer (.ofNbt (12 : Int32))))
  Data.modify store (path "float") .set (.compute .default (.float (.ofNbt (3.5 : Float))))
  return 0

@[mcfunction]
private def computeEntry : Prog (Grade.handled worldGrade) Unit := compute.call.ignore

private abbrev bad : Provider := .ofNbt (nbt% {type: "minecraft:div", left: 1, right: 0})

@[mcfunction]
private def failStop : Prog worldGrade Int32 := do
  Compute.run .default (.integer bad)
  Scoreboard.set (.named "#stop") points (.static 1)

@[mcfunction]
private def failStopEntry : Prog (Grade.handled worldGrade) Unit := failStop.call.ignore

@[mcfunction]
private def failures : Prog (Grade.handled worldGrade) Unit := do
  failStop.call.ignore
  (Compute.run .default (.integer bad)).ignore
  (Data.modify store (path "computed_default") .set (.compute .default (.integer bad))).ignore
  (Data.remove store (path "absent")).ignore
  (Scoreboard.set (.named "#discard") points (.static 1)).ignore
  let result ← Prog.attempt (Data.modify store (path "integer") .set (.ofNbt (12 : Int32)))
  match result with
  | .none => (Scoreboard.set (.named "#unchanged") points (.static 1)).ignore
  | .some _ => (Scoreboard.set (.named "#unchanged") points (.static 0)).ignore

private def entity : Target := Target.ofString "@n[type=minecraft:armor_stand,tag=dctest]"
private def pos : Vec3 := .world (.relative (.static 4)) (.relative (.static 1)) (.relative (.static 0))

@[mcfunction]
private def world : Prog worldGrade Int32 := do
  Data.merge (.entity entity) (nbt% {Invisible: true})
  Data.modify store (path "entity") .set (.from (.entity entity) none)
  let flag ← Data.get (.entity entity) (some (.key "Invisible"))
  Scoreboard.set (.named "#entity") points (.dynamic flag)
  Data.modify (.block pos) (.key "CustomName") .set (.ofNbt (nbt% {text: "Oria"}))
  Data.modify store (path "block") .set (.from (.block pos) (some (.key "CustomName")))
  let score ← Compute.run (.entity entity) (.integer (.ofNbt (nbt% {
    type: "minecraft:score", target: {type: "minecraft:context", target: "target_entity"}, score: "dctest.oria"})))
  Scoreboard.set (.named "#context") points (.dynamic score)
  let block ← Compute.run (.block pos) (.integer (.ofNbt (6 : Int32)))
  Scoreboard.set (.named "#block") points (.dynamic block)
  return 0

@[mcfunction]
private def worldEntry : Prog (Grade.handled worldGrade) Unit := world.call.ignore

@[datapack]
public def specimen : Spec := build {
    ns := "dctest"
    description := "Data and Compute acceptance"
    registerBudget := 6
  } do
    entry "storage" storageEntry.ref
    entry "dynamic" dynamicEntry.ref
    entry "compute" computeEntry.ref
    entry "failures" failures.ref
    entry "world" worldEntry.ref

end Oria.Proofs.Fixtures.DataCompute
