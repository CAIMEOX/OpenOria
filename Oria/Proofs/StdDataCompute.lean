module

public import Oria
import Oria.Std.Data
import Oria.Std.Compute
public import Oria.Std.Compute.Number
import Oria.Std.Command.Declarations
import Oria.Std.DP121
import Oria.IR.DP121.Pretty
meta import Oria
meta import Oria.Std.Data
meta import Oria.Std.Compute
meta import Oria.Std.Compute.Number
meta import Oria.Std.DP121
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.StdDataCompute

open Oria.Std Oria.Std.Command.Arg

private def store : DataTarget := .storage (.ofString "demo:data")
private def path : Nbt.Path Scalar (Nbt.Value .compound) := (Nbt.Path.key "two words").at (.static (-1))

private def calculation : Calculation :=
  .integer (.ofNbt (nbt% {type: "minecraft:add", inputs: [2, 3]}))

@[mcfunction]
private def calculate : Prog (Compute.grade .default Req.all) Int32 := do
  Compute.run .default calculation

@[mcfunction]
private def write (n : Val Int32) : Prog (Data.grade store) Int32 :=
  do
    Data.modify store (.key "record") .set <| .value <| .nbtCompound [
      (⟨"fixed"⟩, .nbt (.string "$(literal)")), (⟨"n"⟩, .hole .i32 n)]

example : calculate.signature.grade = Compute.grade .default Req.all := rfl
example : write.signature.grade = Data.grade store := rfl
example : Grade.Below ⟨Req.none, Eff.random ||| Eff.scoreboardRead⟩ (Data.grade store) := by decide
example : Grade.Below ⟨Req.none, Eff.random ||| Eff.scoreboardRead⟩
    (Teleport.grade .self (.world (.absolute (.static 0)) (.absolute (.static 0)) (.absolute (.static 0)))) := by decide
example : Prog (Data.grade store) Int32 := Data.get store
example : Prog (Data.grade store) Int32 := Data.get store (some path)
example : Prog (Data.grade store) Int32 := Data.getScaled store path 0.5
example : Prog (Data.grade store) Int32 := Data.merge store (nbt% {ready: true})
example : Prog (Data.grade store) Int32 := Data.remove store path
example : Prog (Data.grade store) Int32 := do
  Data.modify store path (.insert (.static (-1))) (.ofNbt (nbt% [1, 2]))
example : Prog (Data.grade store Req.all) Int32 := do
  Data.modify store path .set (.from (.entity (Target.ofString "@n[type=minecraft:pig]")) none)
example : Prog (Data.grade store) Int32 := do
  Data.modify store path .set (.string store (.key "text") (.between (.static 1) (.static 4)))
example : Prog (Data.grade store (Req.position ||| Req.dimension)) Int32 := do
  Data.modify store path .set (.compute .default (.float (.ofNbt (1.5 : Float))))
example : Prog (Compute.grade (.block (.world (.absolute (.static 0)) (.absolute (.static 64)) (.absolute (.static 0)))) Req.all) Int32 := do
  Compute.scaled (.block (.world (.absolute (.static 0)) (.absolute (.static 64)) (.absolute (.static 0))))
    (.named (.ofString "demo:provider")) 10

private def rendered {sig : Command.Signature}
    (request : Command.Call EncodedVal sig) : Except Diagnostic (String × Nat) := do
  let p ← Std.DP121.plan request
  p.withInvocation
    (fun i => pure ((Target.DP121.Command.invoke i).format.pretty 120, 0))
    (fun schema _ _ i _ => pure ((Target.DP121.Command.invoke i).format.pretty 120, schema.fields.length))

private def request := Std.Command.Declarations.dataModify.call <|
  .cons (Command.encode store) <| .cons (Command.encode path) <|
  .cons (Command.encode DataOp.set) <|
  .cons (Command.encode (DataSource.value (.nbtCompound [
    (⟨"n"⟩, .hole .i32 (1 : Val Int32)), (⟨"text"⟩, .nbt (.string "$(text)"))]))) .nil

#guard (rendered request).toOption =
  some ("data modify storage demo:data \"two words\"[-1] set value {\"n\":$(p0),\"text\":\"\\u0024(text)\"}", 1)
#guard (Command.Literal.decimal 0.5).format.pretty 120 = "0.5"
#guard (Command.Literal.path ((Nbt.Path.key "items").child .all)).format.pretty 120 = "\"items\"[]"
#guard (Command.Literal.path (.key "line\nbreak")).check matches .error _
#guard (Command.Literal.path (.key "$(path)")).check matches .error _
#guard (Command.Literal.path (.key "")).check matches .error _
#guard (Command.Literal.path ((Nbt.Path.key "items").child (.key ⟨""⟩))).check matches .error _
#guard (Command.Literal.path ((Nbt.Path.key "items").child (.index 2147483648))).check matches .error _
#guard (Command.Literal.path ((Nbt.Path.key "items").child (.index (-2147483649)))).check matches .error _
#guard (Command.Literal.path ((Nbt.Path.key "items").child (.index (-2147483648)))).check.isOk
#guard (Command.Literal.decimal (1 / 0)).check matches .error _

private def arithmetic := do
  let calculation ← Calculation.ofNumber ((2 + 3 : Oria.NumberProvider.Number .int) * 4)
  pure <| Std.Command.Declarations.compute.call <|
    .cons (Command.encode ComputeContext.default) <| .cons (Command.encode calculation) .nil

#guard (arithmetic.toOption.bind (fun request => (rendered request).toOption)) = some
  ("compute default integer {\"type\":\"minecraft:mul\",\"inputs\":[{\"type\":\"minecraft:add\",\"inputs\":[2,3]},4]}", 0)
#guard (Calculation.ofNumber (Oria.NumberProvider.Number.intConstant 2147483648)) matches
  .error (.invalidCommandNbt _)

private def constantRequest := Std.Command.Declarations.compute.call <|
  .cons (Command.encode ComputeContext.default) <|
  .cons (Command.encode (Calculation.integer (.ofNbt (12 : Int32)))) .nil

#guard (rendered constantRequest).toOption =
  some ("compute default integer {\"type\":\"minecraft:constant\",\"value\":12}", 0)

private def referenced := do
  let calculation ← Calculation.ofNumber (Oria.NumberProvider.Number.reference
    (Oria.NumberProvider.Ref.named (.ofString "demo:value") : Oria.NumberProvider.Ref .int))
  pure <| Std.Command.Declarations.compute.call <|
    .cons (Command.encode ComputeContext.default) <| .cons (Command.encode calculation) .nil

#guard (referenced.toOption.bind (fun request => (rendered request).toOption)) =
  some ("compute default integer demo:value", 0)

open Oria.NumberProvider

private def inputRequest (n : Val Int32) := Std.Command.Declarations.compute.call <|
  .cons (Command.encode ComputeContext.default) <|
  .cons (Command.encode (Calculation.inputs (Number.input n))) .nil

#guard (rendered (inputRequest 7)).toOption =
  some ("compute default integer {\"type\":\"minecraft:constant\",\"value\":$(p0)}", 1)

private def moduloRequest (n : Val Int32) := Std.Command.Declarations.compute.call <|
  .cons (Command.encode ComputeContext.default) <|
  .cons (Command.encode (Calculation.inputs (Number.floorMod (Number.input n) 16))) .nil

#guard (rendered (moduloRequest (-7))).toOption =
  some ("compute default integer {\"type\":\"minecraft:floor_mod\",\"left\":$(p0),\"right\":16}", 1)

example (n : Val Int32) :
    (Calculation.inputs (Number.floorMod (Number.input n) 16)).requirements = Req.none := by
  simp [OfNat.ofNat]

example (n : Val Int32) :
    ¬ Calculation.InputsEncodable (Number.input n + 2147483648) := by
  simp [OfNat.ofNat]

/-- Check imported provider proofs in an exported definition with an opaque object input. -/
@[mcfunction]
public def arithmeticInput (n : Val Int32) : Prog (Compute.grade .default) Int32 := by
  let expression := Number.input n / 2 + Number.floorMod (Number.input n) 2 * 8
  have h : expression.requirements = Req.none := by simp [expression, Req.none]
  exact h ▸ Compute.runInputs .default expression

/-- Floating-point provider evaluation can consume an explicitly converted object integer. -/
@[mcfunction]
public def squareRootInput (n : Val Int32) : Prog (Compute.grade .default) Int32 := by
  let expression := Number.sqrt (Number.fromInt (Number.input n))
  have h : expression.requirements = Req.none := by simp [expression]
  exact h ▸ Compute.runInputs .default expression

example : arithmeticInput.signature.grade = Compute.grade .default := rfl
example : squareRootInput.signature.grade = Compute.grade .default := rfl

private def floatInputRequest := do
  let calculation ← Calculation.ofInputs
    (Number.fromInt (Number.input (4 : Val Int32)) + 2.5)
  pure <| Std.Command.Declarations.compute.call <|
    .cons (Command.encode ComputeContext.default) <| .cons (Command.encode calculation) .nil

#guard (floatInputRequest.toOption.bind fun request => (rendered request).toOption) =
  some ("compute default float {\"type\":\"minecraft:add\",\"inputs\":[{\"type\":\"minecraft:from_int\",\"input\":$(p0)},2.5f]}", 1)

#guard Calculation.ofInputs (Number.input (1 : Val Int32) + 2147483648) matches
  .error (.invalidCommandNbt _)

#guard Calculation.ofInputs
    (Number.fromInt (Number.input (1 : Val Int32)) + Number.floatConstant (0 / 0)) matches
  .error (.invalidCommandNbt _)

private def namedInputRequest := do
  let calculation ← Calculation.ofInputs
    (Number.reference (Ref.named "demo:value") : Number .int (Val Int32))
  pure <| Std.Command.Declarations.compute.call <|
    .cons (Command.encode ComputeContext.default) <| .cons (Command.encode calculation) .nil

#guard (namedInputRequest.toOption.bind fun request => (rendered request).toOption) =
  some ("compute default integer demo:value", 0)

end Oria.Proofs.StdDataCompute
