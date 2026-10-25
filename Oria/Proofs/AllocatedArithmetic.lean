module

import Oria.Compiler.Lower.DP121.Arithmetic
import Lean.Elab.Command
meta import Lean.Elab.Command
import all Oria.Proofs.DP121Semantics
meta import Oria.Compiler.Lower.DP121.Arithmetic
meta import all Oria.Proofs.DP121Semantics

namespace Oria.Proofs.AllocatedArithmetic

open Oria Oria.IR Oria.Lower.DP121 Oria.Target.DP121 Oria.Target.DP121.Semantics
open Lean Lean.Elab.Command

run_cmd
  let .ok bank := Layout.allocate (.ofString "arithmetic.oria") 2
    | throwError "register layout failed"
  let left := bank.registers[0]
  let right := bank.registers[1]
  let leftCell := Stack.slot (.ofString "arithmetic:runtime") .current .locals 0
  let rightCell := Stack.slot (.ofString "arithmetic:runtime") .current .locals 1
  let model : Model := { DP121Semantics.countingModel with
    Scores := Score → Int32
    Storage := StoragePath → Int32
    Trace := Nat
    data := fun (command : DataCommand .plain) storage =>
      let write (path : StoragePath) (value : Int32) :=
        ⟨(fun p => if p = path then value else storage p), .succeeded value, #[0]⟩
      match command with
      | .get path => ⟨storage, .succeeded (storage (dataPath (mode := .plain) () path)), #[0]⟩
      | .setValue path (.int value) => write (dataPath (mode := .plain) () path) value
      | .setFrom target source => write (dataPath (mode := .plain) () target)
          (storage (dataPath (mode := .plain) () source))
      | _ => ⟨storage, .succeeded 0, #[0]⟩ }
  let code : Code := ⟨fun {kind} _ => match kind with
    | .plain => .plain #[] | .macro _ => .macro #[]⟩
  let operations : List (BinaryOp .i32 .i32 .i32 × (Int32 → Int32 → Int32)) :=
    [(.add, (· + ·)), (.sub, (· - ·)), (.mul, (· * ·))]
  for target in [Place.score left, .score right, .storage leftCell, .storage rightCell] do
    for (leftSource, rightSource) in [(Place.score left, Place.score right),
        (.storage leftCell, .storage rightCell), (.score left, .storage rightCell),
        (.storage leftCell, .score right)] do
      for (l, r) in [((-7 : Int32), (3 : Int32)), (7, -3), (-7, -3), (7, 0), (0, 1),
          (-2147483648, -1), (-2147483648, 3), (2147483647, -7),
          (-2147483648, -2147483648), (2147483647, 2147483647),
          (0, -2147483648), (0, 2147483647), (-2147483648, 2147483647), (2147483647, -2147483648)] do
        let initial : State model := ⟨fun s => if s = left then l else if s = right then r else 0,
          fun p => if p = leftCell then l else if p = rightCell then r else 0, #[]⟩
        let check (expected : Int32) (instructions : List (Command .plain)) : CommandElabM Unit := do
          let some result := evalPlainLines model code 200 instructions initial (.succeeded 0)
            | throwError "arithmetic evaluation exhausted fuel"
          let actual := match target with
            | .score score => result.state.scores score
            | .storage path => result.state.storage path
          unless actual == expected do
            throwError "aliased arithmetic returned {actual}, expected {expected}"
        for (op, expected) in operations do
          let instructions := Arithmetic.binary bank op target (.loc leftSource) (.loc rightSource)
          check (expected l r) instructions
        for flag in [Place.score left, .score right, .storage leftCell, .storage rightCell] do
          if flag != target then
            for demanded in [#v[some flag, some target], #v[some flag, none],
                #v[none, some target], #v[none, none]] do
              let instructions := Arithmetic.division bank demanded (.loc leftSource) (.loc rightSource)
              let some result := evalPlainLines model code 200 instructions initial (.succeeded 0)
                | throwError "division evaluation exhausted fuel"
              let read : Place → Int32
                | .score score => result.state.scores score
                | .storage path => result.state.storage path
              let expected := Oria.I32.divide l r
              if demanded[0].isSome then
                unless read flag == (if expected.isSome then 1 else 0) do
                  throwError "division success differs for {l} / {r}"
              if let some value := expected then
                if demanded[1].isSome then
                  unless read target == value do
                    throwError "aliased division returned {read target}, expected {value}"
        check (-l) (Arithmetic.unary bank .neg target (.loc leftSource))
        check (if l ≤ r then 1 else 0)
          (Arithmetic.binary bank .le target (.loc leftSource) (.loc rightSource))
        check (if l < r then 1 else 0)
          (Arithmetic.binary bank .lt target (.loc leftSource) (.loc rightSource))
        check (if l == r then 1 else 0)
          (Arithmetic.binary bank .eq target (.loc leftSource) (.loc rightSource))
        for op in ([.le, .lt, .eq] : List (BinaryOp .i32 .i32 .bool)) do
          for (a, b) in [(.loc leftSource, .loc rightSource), (.imm l, .loc rightSource),
              (.loc leftSource, .imm r), (.imm l, .imm r)] do
            let (before, test) := Arithmetic.condition bank (.compare op a b)
            let out := bank.scratch[2]
            check (if Machine.Condition.test op l r then 1 else 0)
              (before ++ [.scoreboard (.set out 0),
                .when .positive test (.scoreboard (.set out 1)),
                Stack.move ⟨target, .loc (.score out)⟩])

end Oria.Proofs.AllocatedArithmetic
